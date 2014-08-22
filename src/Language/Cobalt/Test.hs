module Language.Cobalt.Test where

import Control.Monad.Reader
import Data.Either
import Text.Parsec
import Unbound.LocallyNameless

import Language.Cobalt.Infer
import Language.Cobalt.Parser
import Language.Cobalt.Syntax

import Debug.Trace

newtype TestResult = TestResult (AnnTerm, [BasicConstraint], [Constraint], Solution)
instance Show TestResult where
  show (TestResult (ann, given, wanted, soln)) =
    "Term: \n" ++ showAnnTerm (prettyType soln) ann ++ "\n" ++
    "Give: " ++ show given ++ "\n" ++
    "Want: " ++ show wanted ++ "\n" ++
    "Soln: " ++ show soln

testEnv :: Env
testEnv = rights . map (parse parseSig "parse") . map ("import " ++) $
            [ "nil :: {a} [a]"
            , "cons :: {a} a -> [a] -> [a]"
            , "tuple :: {a} {b} a -> b -> (a,b)"
            , "fst :: {a} {b} (a,b) -> a"
            , "snd :: {a} {b} (a,b) -> b"
            ]

testString :: String -> Either String TestResult
testString s =
  case parse parseDefn "parse" (s ++ ";;") of
    Left  e     -> Left (show e)
    Right (_,t) -> case runReaderT (runFreshMT $ infer t) testEnv of
      Left  e         -> Left e
      Right (_,a,c,q) -> case runFreshMT $ solve q c of
        Left  e  -> trace (show $ TestResult (a,q,c,[])) $ Left e
        Right sl -> Right $ TestResult (a,q,c,sl)
