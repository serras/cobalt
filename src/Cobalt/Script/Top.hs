{-# LANGUAGE GADTs #-}
module Cobalt.Script.Top where

import Data.Regex.MultiRules
import Unbound.LocallyNameless hiding (name)

import Cobalt.Graph as G
import Cobalt.Language.Syntax (Env(..), RawDefn)
import Cobalt.OutsideIn.Solver (Solution(..), toSolution)
import Cobalt.Script.Gather
import Cobalt.Script.Rules
import Cobalt.Script.Script
import Cobalt.Script.Solver
import Cobalt.Script.Syntax
import Cobalt.Types

gDefn :: Env -> RawDefn -> FreshM (Gathered, AnnUTerm TyVar)
gDefn env@(Env _ _ _ rules) (_name,term,_declaredType) = do
  unbound <- unbindTerm term
  tyv     <- tyvared unbound
  case eval (map syntaxRuleToScriptRule rules ++ mainTypeRules) (IndexIndependent env) tyv of
    err@(Error _) -> return $ (err, tyv)
    GatherTerm g w v -> return (GatherTerm g (map simplifyScript w) v, tyv)

gDefns :: Env -> [(RawDefn,Bool)] -> [(Gathered, AnnUTerm TyVar)]
gDefns env terms = runFreshM $ mapM (\(term,_fail) -> gDefn env term) terms

tcDefn :: Env -> RawDefn -> FreshM (ScriptSolution, [(TyVar, MonoType)], AnnUTerm MonoType)
tcDefn env@(Env _ _ ax _) defn = do
  (gatherResult, term) <- gDefn env defn
  case gatherResult of
    Error errs -> return ((emptySolution [] [], errs, G.empty), [], atUAnn (\(pos, m) -> (pos, var m)) term)
    GatherTerm g [w] [v] -> do
      let tch = v : fvScript w  -- touchable variables
      ((sg,rs,vars),err,gr) <- simpl ax g tch w
      -- reuse implementation of obtaining substitution
      let Solution sg' rs' subst' vars' = toSolution sg rs vars
      return (((sg',rs',vars'),err,gr), subst', atUAnn (\(pos, m) -> (pos, getFromSubst m subst')) term)
    _ -> error "This should never happen"

getFromSubst :: TyVar -> [(TyVar, MonoType)] -> MonoType
getFromSubst v s = case lookup v s of
                    Just m  -> m
                    Nothing -> var v

tcDefns :: Env -> [(RawDefn,Bool)] -> [(ScriptSolution, [(TyVar, MonoType)], AnnUTerm MonoType)]
tcDefns env terms = runFreshM $ mapM (\(term,_fail) -> tcDefn env term) terms
