{-# LANGUAGE ViewPatterns #-}
module Language.HigherRank.Infer (
  infer
, testString
) where

import Control.Applicative
import Control.Monad.Reader
import Text.Parsec
import Unbound.LocallyNameless

import Language.HigherRank.Parser
import Language.HigherRank.Syntax

type Env = [(TermVar, PolyType)]
type Result = (MonoType, AnnTerm, [Constraint], [BasicConstraint])
type TcMonad = FreshMT (ReaderT Env (Either String))

lookupEnv :: TermVar -> TcMonad PolyType
lookupEnv v = do optT <- asks (lookup v)
                 case optT of
                   Nothing -> fail $ "Cannot find " ++ show v
                   Just t  -> return t

extendEnv :: TermVar -> PolyType -> TcMonad a -> TcMonad a
extendEnv v s = local ((v,s) :)

infer :: Term -> TcMonad Result
infer (Term_IntLiteral n) =
  return (MonoType_Int, AnnTerm_IntLiteral n MonoType_Int,
          [], [])
infer (Term_Var x) =
  do sigma <- lookupEnv x
     tau <- mVar <$> fresh (string2Name "tau")
     return (tau, AnnTerm_Var (translate x) tau,
             [Constraint_Inst tau sigma], [])
infer (Term_Abs b) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     (tau,ann,c,ex) <- extendEnv x (pVar alpha) $ infer e
     let arrow = mVar alpha --> tau
     return (arrow, AnnTerm_Abs (bind (translate x) ann) arrow, c,ex)
infer (Term_App e1 e2) =
  do (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- infer e2
     alpha <- mVar <$> fresh (string2Name "alpha")
     return (alpha, AnnTerm_App ann1 ann2 alpha,
             c1 ++ c2 ++ [Constraint_Unify tau1 (tau2 --> alpha)],
             ex1 ++ ex2)
infer (Term_Let b) =
  do ((x, unembed -> e1),e2) <- unbind b
     (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- extendEnv x (PolyType_Mono tau1) $ infer e2
     return (tau2, AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2,
             c1 ++ c2, ex1 ++ ex2)

testString :: String -> Either String Result
testString s =
  case parse parseTerm "parse" s of
    Left  e -> Left (show e)
    Right t -> runReaderT (runFreshMT $ infer t) []
