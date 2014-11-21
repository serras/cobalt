module Cobalt.Script.Top where

import Data.Regex.Rules
import Unbound.LocallyNameless hiding (name)

import Cobalt.Language.Syntax (Env, RawDefn)
import Cobalt.Script.Gather
import Cobalt.Script.Script
import Cobalt.Script.Syntax

gDefn :: Env -> RawDefn -> FreshM (Either [String] Gathered)
gDefn env (_name,term,_declaredType) = do
  unbound <- unbindTerm term
  tyv     <- tyvared unbound
  case eval mainTypeRules env tyv of
    Left err -> return $ Left err
    Right (Gathered g w v) -> return $ Right (Gathered g (map simplifyScript w) v)

gDefns :: Env -> [(RawDefn,Bool)] -> [Either [String] Gathered]
gDefns env terms = runFreshM $ mapM (\(term,_fail) -> gDefn env term) terms
