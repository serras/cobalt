{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.Script.Top where

import Control.Applicative ((<$>))
import Control.Lens.Extras
import Control.Monad.Except
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

gDefn :: Env -> RawDefn -> FreshM (Gathered, AnnUTerm TyVar, [TyVar])
gDefn env@(Env fn dat _ rules) (_name,term,Nothing) = do
  unbound <- unbindTerm term fn dat
  tyv     <- tyvared unbound
  case eval (map syntaxRuleToScriptRule rules ++ mainTypeRules) (IndexIndependent env) tyv of
    err@(Error _) -> return $ (err, tyv, [])
    GatherTerm g [w] v ->
      -- Chose whether to apply exists removal or not
      let simplifiedW = simplifyScript w in
      return (GatherTerm g [simplifiedW] v, tyv, v ++ fvScript simplifiedW)
      -- case removeExistsScript w of
      --  (w2, newG, _) -> return (GatherTerm (union g newG) [simplifyScript w2] v, tyv)
    _ -> error "This should never happen"
gDefn (Env fn dat ax rules) (name,term,Just declaredType) = do
  unbound <- unbindTerm term fn dat
  tyv     <- tyvared unbound
  let env' = Env ((name,declaredType) : fn) dat ax rules
  case eval (map syntaxRuleToScriptRule rules ++ mainTypeRules) (IndexIndependent env') tyv of
    err@(Error _) -> return $ (err, tyv, [])
    GatherTerm g [w] [v] -> do
      (q1,t1,_) <- split declaredType
      let extra = Constraint_Unify (var v) t1
          simplifiedW = simplifyScript w
          withExtra = Asym (Singleton extra (Nothing,Nothing)) simplifiedW (Nothing,Nothing)
      -- Chose whether to apply exists removal or not -> look above
      return (GatherTerm (g ++ q1) [withExtra] [v], tyv, v : fvScript simplifiedW)
    _ -> error "This should never happen"

gDefns :: Env -> [(RawDefn,Bool)] -> [(Gathered, AnnUTerm TyVar, [TyVar])]
gDefns env terms = runFreshM $ mapM (\(term,_fail) -> gDefn env term) terms

tcDefn :: Env -> RawDefn -> FreshM (FinalSolution, AnnUTerm MonoType, Maybe PolyType)
tcDefn env@(Env _ _ ax _) defn@(_,_,annotation) = do
  (gatherResult, term, tch) <- gDefn env defn
  case gatherResult of
    Error errs -> return ((Solution [] [] [] [], errs, G.empty), atUAnn (\(pos, m) -> (pos, var m)) term, Nothing)
    GatherTerm g [w] [v] -> do
      -- reuse implementation of obtaining substitution
      s@(inn@(Solution smallG rs subst' tch'),errs,graph) <- solve ax g tch w
      let newTerm = atUAnn (\(pos, m) -> (pos, getFromSubst m subst')) term
      case (annotation, rs) of
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
    _ -> error "This should never happen"

getFromSubst :: TyVar -> [(TyVar, MonoType)] -> MonoType
getFromSubst v s = case lookup v s of
                    Just m  -> m
                    Nothing -> var v

tcDefns :: Env -> [(RawDefn,Bool)] -> [(FinalSolution, AnnUTerm MonoType, Maybe PolyType)]
tcDefns env terms = runFreshM $ tcDefns_ env terms
  where tcDefns_ _env [] = return []
        tcDefns_ env_@(Env fn da ax ru) ((d@(name,_,_),_):ds) = do
          result@(_,_,typ) <- tcDefn env_ d
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
