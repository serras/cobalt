{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.U (
  check
, checkEnv
, module Cobalt.U.Attributes
, gDefns
, FinalSolution
, Solution(..)
, tcDefn
, tcDefns
) where

import Control.Applicative ((<$>))
import Control.Lens.Extras
import Control.Monad.Except
import Data.List (nub)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Regex.MultiRules hiding (check)
import Unbound.LocallyNameless hiding (name, union)

import Cobalt.Core
import Cobalt.Language
import Cobalt.U.Gather
import Cobalt.U.Attributes
import Cobalt.U.Solver
import Cobalt.U.Rules.Translation
import Cobalt.U.Rules.Check

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

type GDefnGathered = Either Errors ([Constraint], [TyVar], GatherTermInfo)

gDefn_ :: [Constraint] -> [TyVar] -> Env -> RawUnboundDefn -> FreshM (GDefnGathered, AnnUTerm TyVar, [TyVar])
gDefn_ sat tchs env@(Env _ _ ax rules) (_name,tyv,_,Nothing) =
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules) (IndexIndependent (env,sat,tchs)) tyv of
    Error err -> return (Left err, tyv, [])
    GatherTerm g v i -> do GatherTermInfo [w] c cv <- i
                           -- Chose whether to apply exists removal or not
                           let simplifiedW = simplifyScript w
                           return (Right (g, v, GatherTermInfo [simplifiedW] c cv), tyv, v ++ fvScript simplifiedW)
gDefn_ sat tchs (Env fn dat ax rules) (name,tyv,Just declaredType,Just (q1,t1,_)) = do
  let env' = Env ((name,declaredType) : fn) dat ax rules
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules) (IndexIndependent (env',sat,tchs)) tyv of
    Error err -> return (Left err, tyv, [])
    GatherTerm g [v] i -> do GatherTermInfo [w] c cv <- i
                             let extra = Constraint_Unify (var v) t1
                                 simplifiedW = simplifyScript w
                                 withExtra = Asym (Singleton extra (Nothing,Nothing)) simplifiedW (Nothing,Nothing)
                             -- Chose whether to apply exists removal or not -> look above
                             return (Right (g ++ q1, [v], GatherTermInfo [withExtra] c cv), tyv, v : fvScript simplifiedW)
    _ -> error "This should never happen"
gDefn_ _ _ _ _ = error "This should never happen"

gDefns :: Env -> [(RawDefn,Bool)] -> [(GDefnGathered, AnnUTerm TyVar, [TyVar], [Constraint])]
gDefns env terms = runFreshM $
  forM terms $ \(term,_fail) -> do
    tyv <- doTyvaring env term
    ((Solution gg rs sb tchs,_,_),_,_) <- tcDefn_ (Just []) (Just []) env tyv
    let extra = nub $ gg ++ rs ++ map (\(x,y) -> Constraint_Unify (var x) y) sb
    (g,au,vrs) <- gDefn_ extra tchs env tyv
    return (g,au,vrs,extra)

tcDefn :: Env -> RawUnboundDefn
       -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn = tcDefn_ Nothing Nothing

tcDefn_ :: Maybe [Constraint] -> Maybe [TyVar] -> Env -> RawUnboundDefn
        -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn_ extra tchs env@(Env _ _ ax _) defn@(_,_,annotation,_) = do
  (gatherResult, term, tch) <- gDefn_ (fromMaybe [] extra) (fromMaybe [] tchs) env defn  -- pass extra information
  case gatherResult of
    Left errs -> return ( (Solution [] [] [] [], map errorFromPreviousPhase errs, emptyGraph)
                         , atUAnn (\(pos, m) -> (pos, var m)) term
                         , Nothing )
    Right (g, [v], GatherTermInfo [w] _ _) -> do
      -- reuse implementation of obtaining substitution
      s@(inn@(Solution smallG rs subst' tch'),errs,graph) <- solve ax g tch w
      let newTerm = atUAnn (\(pos, m) -> (pos, getFromSubst m subst')) term
          tyvTerm = atUAnn (\(pos, m) -> (pos, var m)) term
      result@((Solution resultGiven resultResidual resultSubst resultTchs, resultErrs, _)
             ,_,_) <- case (annotation, rs) of
        (Just p, []) -> return (s, newTerm, Just p)
        (Nothing, _) -> do -- We need to close it
           let (almostFinalT, restC) = closeExn (smallG ++ rs) (getFromSubst v subst') (not . (`elem` tch'))
               finalT = nf almostFinalT
           finalCheck <- runExceptT $ tcCheckErrors restC finalT
           case finalCheck of
             Left missing@(SolverError_CouldNotDischarge missingRs) ->
                                return ( (inn, makeManyExplanation missing missingRs Nothing Nothing graph : errs, graph)
                                       , tyvTerm {- newTerm -}, Nothing )
             Left moreErrors -> return ((inn, emptySolverExplanation moreErrors : errs, graph), tyvTerm {- newTerm -}, Nothing)
             Right _ -> return (s, newTerm, Just finalT)
        _ -> -- Error, we could not discharge everything
             return ( ( inn
                      , makeManyExplanation (SolverError_CouldNotDischarge rs) rs Nothing Nothing graph : errs
                      , graph )
                    , tyvTerm {- newTerm -}, Nothing )
      -- do a second pass if needed
      case (resultErrs, extra) of
        ([], _)      -> return result
        (_, Just _)  -> return result  -- already in second pass
        (_, Nothing) -> let resultExtra = nub $ resultGiven ++ resultResidual
                                                ++ map (\(x,y) -> Constraint_Unify (var x) y) resultSubst
                         in tcDefn_ (Just resultExtra) (Just resultTchs) env defn
    _ -> error "This should never happen"

getFromSubst :: TyVar -> [(TyVar, MonoType)] -> MonoType
getFromSubst v s = fromMaybe (var v) (lookup v s)

tcDefns :: Env -> [(RawDefn,Bool)] -> [(FinalSolution, AnnUTerm MonoType, Maybe PolyType)]
tcDefns env terms = runFreshM $ tcDefns_ env terms
  where tcDefns_ _env [] = return []
        tcDefns_ env_@(Env fn da ax ru) ((d@(name,_,_),_):ds) = do
          tyv <- doTyvaring env_ d
          result@(_,_,typ) <- tcDefn env_ tyv
          case typ of
            Nothing -> (result :) <$> tcDefns_ env_ ds
            Just p  -> (result :) <$> tcDefns_ (Env ((translate name, p):fn) da ax ru) ds


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
