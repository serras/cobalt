module Cobalt.Script.Top where

import Data.Regex.Rules
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

gDefn :: Env -> RawDefn -> FreshM (Either [String] Gathered)
gDefn env@(Env _ _ _ rules) (_name,term,_declaredType) = do
  unbound <- unbindTerm term
  tyv     <- tyvared unbound
  case eval (map syntaxRuleToScriptRule rules ++ mainTypeRules) env tyv of
    Left err -> return $ Left err
    Right (Gathered g w v) -> return $ Right (Gathered g (map simplifyScript w) v)

gDefns :: Env -> [(RawDefn,Bool)] -> [Either [String] Gathered]
gDefns env terms = runFreshM $ mapM (\(term,_fail) -> gDefn env term) terms

tcDefn :: Env -> RawDefn -> FreshM (ScriptSolution, [(TyVar, MonoType)])
tcDefn env@(Env _ _ ax _) defn = do
  gatherResult <- gDefn env defn
  case gatherResult of
    Left errs -> return ((emptySolution [] [], errs, G.empty),[])
    Right (Gathered g [w] [v]) -> do
      let tch = v : fvScript w  -- touchable variables
      ((sg,rs,vars),err,gr) <- simpl ax g tch w
      -- reuse implementation of obtaining substitution
      let s@(Solution sg' rs' subst' vars') = toSolution sg rs vars
      return (((sg',rs',vars'),err,gr),subst')

tcDefns :: Env -> [(RawDefn,Bool)] -> [(ScriptSolution, [(TyVar, MonoType)])]
tcDefns env terms = runFreshM $ mapM (\(term,_fail) -> tcDefn env term) terms
