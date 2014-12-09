{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.Script.Top where

import Control.Applicative ((<$>))
import Control.Lens.Extras
import Control.Monad.Except
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Regex.MultiRules
import Unbound.LocallyNameless hiding (name, union)

import Cobalt.Graph as G
import Cobalt.Language.Syntax (Env(..), RawDefn)
import Cobalt.OutsideIn.Solver (Solution(..))
import Cobalt.Script.Gather
import Cobalt.Script.Rules
import Cobalt.Script.Script
import Cobalt.Script.Solver
import Cobalt.Script.Syntax
import Cobalt.Types

doTyvaring :: Env -> RawDefn -> FreshM (AnnUTerm TyVar)
doTyvaring (Env fn dat _ _) (_,term,_) = do
  unbound <- unbindTerm term fn dat
  tyvared unbound

gDefn_ :: [Constraint] -> Env -> RawDefn -> AnnUTerm TyVar -> FreshM (Gathered, AnnUTerm TyVar, [TyVar])
gDefn_ sat env@(Env _ _ ax rules) (_name,_term,Nothing) tyv = do
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules) (IndexIndependent (env,sat)) tyv of
    err@(Error _) -> return $ (err, tyv, [])
    GatherTerm g [w] v ->
      -- Chose whether to apply exists removal or not
      let simplifiedW = simplifyScript w in
      return (GatherTerm g [simplifiedW] v, tyv, v ++ fvScript simplifiedW)
      -- case removeExistsScript w of
      --  (w2, newG, _) -> return (GatherTerm (union g newG) [simplifyScript w2] v, tyv)
    _ -> error "This should never happen"
gDefn_ sat (Env fn dat ax rules) (name,_term,Just declaredType) tyv = do
  let env' = Env ((name,declaredType) : fn) dat ax rules
  case eval (map (syntaxRuleToScriptRule ax) rules ++ mainTypeRules) (IndexIndependent (env',sat)) tyv of
    err@(Error _) -> return $ (err, tyv, [])
    GatherTerm g [w] [v] -> do
      (q1,t1,_) <- split declaredType
      let extra = Constraint_Unify (var v) t1
          simplifiedW = simplifyScript w
          withExtra = Asym (Singleton extra (Nothing,Nothing)) simplifiedW (Nothing,Nothing)
      -- Chose whether to apply exists removal or not -> look above
      return (GatherTerm (g ++ q1) [withExtra] [v], tyv, v : fvScript simplifiedW)
    _ -> error "This should never happen"

gDefns :: Env -> [(RawDefn,Bool)] -> [(Gathered, AnnUTerm TyVar, [TyVar], [Constraint])]
gDefns env terms = runFreshM $
  forM terms $ \(term,_fail) -> do
    tyv <- doTyvaring env term
    ((Solution gg rs sb _,_,_),_,_) <- tcDefn_ (Just []) env term tyv
    let extra = nub $ gg ++ rs ++ map (\(x,y) -> Constraint_Unify (var x) y) sb
    (g,au,vrs) <- gDefn_ extra env term tyv
    return (g,au,vrs,extra)

tcDefn :: Env -> RawDefn -> AnnUTerm TyVar
       -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn = tcDefn_ Nothing

tcDefn_ :: Maybe [Constraint] -> Env -> RawDefn -> AnnUTerm TyVar
        -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn_ extra env@(Env _ _ ax _) defn@(_,_,annotation) tyv = do
  (gatherResult, term, tch) <- gDefn_ (maybe [] id extra) env defn tyv  -- pass extra information
  case gatherResult of
    Error errs -> return ((Solution [] [] [] [], errs, G.empty), atUAnn (\(pos, m) -> (pos, var m)) term, Nothing)
    GatherTerm g [w] [v] -> do
      -- reuse implementation of obtaining substitution
      s@(inn@(Solution smallG rs subst' tch'),errs,graph) <- solve ax g tch w
      let newTerm = atUAnn (\(pos, m) -> (pos, getFromSubst m subst')) term
      result@((Solution resultGiven resultResidual resultSubst _, resultErrs, _),_,_) <- case (annotation, rs) of
        (Just p, []) -> return (s, newTerm, Just p)
        (Nothing, _) -> do -- We need to close it
           let (almostFinalT, restC) = closeExn (smallG ++ rs) (getFromSubst v subst') (not . (`elem` tch'))
               finalT = nf $ almostFinalT
           finalCheck <- runExceptT $ tcCheckErrors restC finalT
           case finalCheck of
             Left moreErrors -> return ((inn, moreErrors : errs, graph), newTerm, Nothing)
             Right _ -> return (s, newTerm, Just finalT)
        _ -> -- Error, we could not discharge everything
             return ((inn, ("Could not deduce " ++ show rs) : errs, graph), newTerm, Nothing)
      -- do a second pass if needed
      case (resultErrs, extra) of
        ([], _)      -> return result
        (_, Just _)  -> return result  -- already in second pass
        (_, Nothing) -> let resultExtra = nub $ resultGiven ++ resultResidual
                                                ++ map (\(x,y) -> Constraint_Unify (var x) y) resultSubst
                         in tcDefn_ (Just resultExtra) env defn tyv
    _ -> error "This should never happen"

getFromSubst :: TyVar -> [(TyVar, MonoType)] -> MonoType
getFromSubst v s = case lookup v s of
                    Just m  -> m
                    Nothing -> var v

tcDefns :: Env -> [(RawDefn,Bool)] -> [(FinalSolution, AnnUTerm MonoType, Maybe PolyType)]
tcDefns env terms = runFreshM $ tcDefns_ env terms
  where tcDefns_ _env [] = return []
        tcDefns_ env_@(Env fn da ax ru) ((d@(name,_,_),_):ds) = do
          tyv <- doTyvaring env_ d 
          result@(_,_,typ) <- tcDefn env_ d tyv
          case typ of
            Nothing -> (result :) <$> tcDefns_ env_ ds
            Just p  -> (result :) <$> tcDefns_ (Env ((translate name, p):fn) da ax ru) ds


-- COPIED FROM Cobalt.OutsideIn.Top
-- ================================

tcCheckErrors :: [Constraint] -> PolyType -> ExceptT String FreshM ()
tcCheckErrors rs t = do checkRigidity t
                        checkAmbiguity rs
                        checkLeftUnclosed rs

checkRigidity :: PolyType -> ExceptT String FreshM ()
checkRigidity t = do let fvT :: [TyVar] = fv t
                     when (not (null fvT)) $ throwError $ case fvT of
                       [x] -> show x ++ " is a rigid type variable in: " ++ show t
                       _   -> show fvT ++ " are rigid type variables in: " ++ show t

checkAmbiguity :: [Constraint] -> ExceptT String FreshM ()
checkAmbiguity cs = do let vars = catMaybes $ map getVar cs
                           dup  = findDuplicate vars
                       case dup of
                         Nothing -> return ()
                         Just v  -> let cs' = filter (\c -> getVar c == Just v) cs
                                     in throwError $ "Ambiguous variable " ++ show v ++ ": " ++ show cs'

getVar :: Constraint -> Maybe TyVar
getVar (Constraint_Inst  (MonoType_Var v) _) = Just v
getVar (Constraint_Equal (MonoType_Var v) _) = Just v
getVar _ = Nothing

findDuplicate :: Eq a => [a] -> Maybe a
findDuplicate []     = Nothing
findDuplicate (x:xs) = if x `elem` xs then Just x else findDuplicate xs

checkLeftUnclosed :: [Constraint] -> ExceptT String FreshM ()
checkLeftUnclosed cs = let cs' = filter (\x -> not (is _Constraint_Inst x) && not (is _Constraint_Equal x)) cs
                        in case cs' of
                             [] -> return ()
                             _  -> throwError $ "Could not deduce: " ++ show cs'
