{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.U (
  check
, checkEnv
, module Cobalt.U.Attributes
, GatheringScheme(..)
, gDefns
, FinalSolution
, Solution(..)
, tcDefn
, tcDefns
) where

#if MIN_VERSION_base(4,8,0)
#else
import Control.Applicative ((<$>))
#endif
import Control.Lens.Extras
import Control.Monad.Except
import Data.List (nub)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Regex.MultiRules hiding (check)
import Unbound.LocallyNameless hiding (name, union)

import Cobalt.Core
import Cobalt.Language
import Cobalt.OutsideIn (entails)
import Cobalt.U.Gather
import Cobalt.U.Attributes
import Cobalt.U.Solver
import Cobalt.U.Rules.Translation
import Cobalt.U.Rules.Check

import Debug.Trace

type RawUnboundDefn = ( RawTermVar
                      , AnnUTerm TyVar
                      , Maybe PolyType
                      , Maybe ([Constraint],MonoType,[TyVar]))

doTyvaring :: Env -> RawDefn -> FreshM RawUnboundDefn
doTyvaring (Env fn dat _ _) (name,term,Nothing) = do
  unbound <- unbindTerm term fn dat
  tyv     <- tyvared unbound
  return (name, tyv, Nothing, Nothing)
doTyvaring (Env fn dat _ _) (name,term,Just p) = do
  unbound  <- unbindTerm term fn dat
  tyv      <- tyvared unbound
  unboundP <- split p
  return (name, tyv, Just p, Just unboundP)

type GDefnGathered = Either Errors ([Constraint], [AnnUTerm TyVar], GatherTermInfo)

gDefn_ :: GatheringScheme -> [Constraint] -> [TyVar] -> Env -> RawUnboundDefn -> FreshM (GDefnGathered, AnnUTerm TyVar, [TyVar])
gDefn_ gs sat tchs env@(Env _ _ ax rules) (_name,tyv,_,Nothing) =
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules gs) (IndexIndependent (env,sat,tchs)) tyv of
    Error err -> return (Left err, tyv, [])
    GatherTerm g [e] [i] -> do GatherTermInfo w c cv <- i
                               -- Chose whether to apply exists removal or not
                               let (p,v) = ann e
                                   simplifiedW = simplifyScript $ resolveCondScript sat tchs env p w
                               return (Right (g, [e], GatherTermInfo simplifiedW c cv), tyv, v : fvScript simplifiedW)
    _ -> error "This should never happen"
gDefn_ gs sat tchs (Env fn dat ax rules) (name,tyv,Just declaredType,Just (q1,t1,_)) = do
  let env' = Env ((name,declaredType) : fn) dat ax rules
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules gs) (IndexIndependent (env',sat,tchs)) tyv of
    Error err -> return (Left err, tyv, [])
    GatherTerm g [e] [i] -> do GatherTermInfo w c cv <- i
                               let (p,v) = ann e
                                   extra = Constraint_Unify (var v) t1
                                   simplifiedW = simplifyScript $ resolveCondScript sat tchs env' p w
                                   withExtra = simplifyScript $ case gs of
                                                 TreeScheme -> AsymJoin simplifiedW (Singleton extra p Nothing) p
                                                 FlatScheme -> Join [simplifiedW, Singleton extra p Nothing] p
                               -- Chose whether to apply exists removal or not -> look above
                               return (Right (g ++ q1, [e], GatherTermInfo withExtra c cv), tyv, v : fvScript simplifiedW)
    _ -> error "This should never happen"
gDefn_ _ _ _ _ _ = error "This should never happen"

gDefns :: GatheringScheme -> Env -> [(RawDefn,Bool)] -> [(GDefnGathered, AnnUTerm TyVar, [TyVar], [Constraint])]
gDefns gs env terms = runFreshM $
  forM terms $ \(term,_fail) -> do
    tyv <- doTyvaring env term
    ((Solution gg rs sb tchs,_,_),_,_) <- tcDefn_ gs (Just []) (Just []) env tyv
    let extra = nub $ gg ++ rs ++ map (\(x,y) -> Constraint_Unify (var x) y) sb
    (g,au,vrs) <- gDefn_ gs extra tchs env tyv
    return (g,au,vrs,extra)

tcDefn :: GatheringScheme -> Env -> RawUnboundDefn
       -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn gs = tcDefn_ gs Nothing Nothing

tcDefn_ :: GatheringScheme -> Maybe [Constraint] -> Maybe [TyVar] -> Env -> RawUnboundDefn
        -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn_ gs extra tchs env@(Env _ _ ax _) defn@(_,_,annotation,_) = do
  (gatherResult, term, tch) <- gDefn_ gs (fromMaybe [] extra) (fromMaybe [] tchs) env defn  -- pass extra information
  let (thePosition, _) = ann term
  case gatherResult of
    Left errs -> return ( (Solution [] [] [] [], map errorFromPreviousPhase errs, emptyGraph)
                         , atUAnn (\(pos, m) -> (pos, var m)) term
                         , Nothing )
    Right (g, [e], GatherTermInfo w _ _) -> do
      -- reuse implementation of obtaining substitution
      s@(inn@(Solution smallG rs subst' tch'),errs,graph) <- solve ax g tch w
      let newTerm = atUAnn (\(pos, m) -> (pos, getFromSubst m subst')) term
          tyvTerm = atUAnn (\(pos, m) -> (pos, var m)) term
      result@((Solution resultGiven resultResidual resultSubst resultTchs, resultErrs, _)
             ,_,_) <- case (annotation, rs) of
        (Just p, []) -> return (s, newTerm, Just p)
        (Nothing, _) -> do -- We need to close it
           let (almostFinalT, restC) = closeExn (smallG ++ rs) (getFromSubst (snd (ann e)) subst') (not . (`elem` tch'))
               finalT = nf almostFinalT
           finalCheck <- runExceptT $ tcCheckErrors restC finalT
           case finalCheck of
             Left missing@(SolverError_CouldNotDischarge missingRs) ->
                                return ( (inn, makeManyExplanation missing missingRs
                                                                   thePosition Nothing graph
                                               : errs
                                         , graph)
                                       , tyvTerm {- newTerm -}, Nothing )
             Left moreErrors -> return ((inn, emptyUnnamedSolverExplanation moreErrors : errs, graph), tyvTerm {- newTerm -}, Nothing)
             Right _ -> return (s, newTerm, Just finalT)
        _ -> -- Error, we could not discharge everything
             return ( ( inn
                      , makeManyExplanation (SolverError_CouldNotDischarge rs)
                                            rs thePosition Nothing graph
                        : errs
                      , graph )
                    , tyvTerm {- newTerm -}, Nothing )
      -- do a second pass if needed
      case (resultErrs, extra) of
        ([], _)      -> return result
        (_, Just _)  -> return result  -- already in second pass
        (_, Nothing) -> let resultExtra = nub $ resultGiven ++ resultResidual
                                                ++ map (\(x,y) -> Constraint_Unify (var x) y) resultSubst
                         in tcDefn_ gs (Just resultExtra) (Just resultTchs) env defn
    _ -> error "This should never happen"

getFromSubst :: TyVar -> [(TyVar, MonoType)] -> MonoType
getFromSubst v s = fromMaybe (var v) (lookup v s)

tcDefns :: GatheringScheme -> Env -> [(RawDefn,Bool)] -> [(FinalSolution, AnnUTerm MonoType, Maybe PolyType)]
tcDefns gs env terms = runFreshM $ tcDefns_ env terms
  where tcDefns_ _env [] = return []
        tcDefns_ env_@(Env fn da ax ru) ((d@(name,_,_),_):ds) = do
          tyv <- doTyvaring env_ d
          result@(_,_,typ) <- tcDefn gs env_ tyv
          case typ of
            Nothing -> (result :) <$> tcDefns_ env_ ds
            Just p  -> (result :) <$> tcDefns_ (Env ((translate name, p):fn) da ax ru) ds

resolveCondScript :: [Constraint] -> [TyVar] -> Env -> (SourcePos,SourcePos) -> TyScript -> TyScript
resolveCondScript sat tch env p = mapConstraintScript $ \c cp i ->
  let thePos = case cp of { Just cp' -> cp'; Nothing -> p }
   in Join (map (\x -> Singleton x thePos i) $ resolveCond sat tch env c) thePos

resolveCond :: [Constraint] -> [TyVar] -> Env -> Constraint -> [Constraint]
resolveCond sat tch env@(Env _ _ ax _) (Constraint_Cond c t e)
  | null c || trace (show sat ++ "\nentails?\n" ++ show c ++ "\n") (entails ax sat c tch) = concatMap (resolveCond sat tch env) t
--  | null c || entails ax sat c tch = concatMap (resolveCond sat tch env) t
  | otherwise                      = concatMap (resolveCond sat tch env) e
resolveCond sat tch env (Constraint_Later s cs)
  = [Constraint_Later s $ concatMap (resolveCond sat tch env) cs]
resolveCond sat tch env (Constraint_Exists b) = (:[]) . Constraint_Exists $ runFreshM $ do
  (v, (c1,c2)) <- unbind b
  return $ bind v (concatMap (resolveCond sat tch env) c1, concatMap (resolveCond sat tch env) c2)
resolveCond sat tch env (Constraint_Inst m p) = (:[]) . Constraint_Inst m $ runFreshM $
  resolveCondPolyType True m sat tch env p
resolveCond sat tch env (Constraint_Equal m p) = (:[]) . Constraint_Equal m $ runFreshM $
  resolveCondPolyType False m sat tch env p
resolveCond _ _ _ c = [c]  -- Do nothing on the rest

resolveCondPolyType :: Bool -> MonoType -> [Constraint] -> [TyVar] -> Env -> PolyType -> FreshM PolyType
resolveCondPolyType addToTch mt sat tch env (PolyType_Bind b) =
  do (v, rest) <- unbind b
     let newTch = if addToTch then v:tch else tch
     rest' <- resolveCondPolyType addToTch mt sat newTch env rest
     return $ PolyType_Bind (bind v rest')
resolveCondPolyType _ mt sat tch env (PolyType_Mono c m) =
  return $ PolyType_Mono (concatMap (resolveCond (Constraint_Unify m mt : sat) tch env) c) m
resolveCondPolyType _ _ _ _ _ PolyType_Bottom = return PolyType_Bottom

-- COPIED FROM Cobalt.OutsideIn.Top
-- ================================

tcCheckErrors :: [Constraint] -> PolyType -> ExceptT SolverError FreshM ()
tcCheckErrors rs t = do checkRigidity t
                        checkAmbiguity rs
                        checkLeftUnclosed rs

checkRigidity :: PolyType -> ExceptT SolverError FreshM ()
checkRigidity t = do let fvT :: [TyVar] = fv t
                     unless (null fvT) $ throwError (SolverError_NonTouchable fvT)

checkAmbiguity :: [Constraint] -> ExceptT SolverError FreshM ()
checkAmbiguity cs = do let vars = mapMaybe getVar cs
                           dup  = findDuplicate vars
                       case dup of
                         Nothing -> return ()
                         Just v  -> let cs' = filter (\c -> getVar c == Just v) cs
                                     in throwError (SolverError_Ambiguous v cs')

getVar :: Constraint -> Maybe TyVar
getVar (Constraint_Inst  (MonoType_Var v) _) = Just v
getVar (Constraint_Equal (MonoType_Var v) _) = Just v
getVar _ = Nothing

findDuplicate :: Eq a => [a] -> Maybe a
findDuplicate []     = Nothing
findDuplicate (x:xs) = if x `elem` xs then Just x else findDuplicate xs

checkLeftUnclosed :: [Constraint] -> ExceptT SolverError FreshM ()
checkLeftUnclosed cs = let cs' = filter (\x -> not (is _Constraint_Inst x) && not (is _Constraint_Equal x)) cs
                        in case cs' of
                             [] -> return ()
                             _  -> throwError (SolverError_CouldNotDischarge cs')
