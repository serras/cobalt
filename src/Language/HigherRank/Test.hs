module Language.HigherRank.Test where

import Control.Monad.Reader
import Text.Parsec
import Unbound.LocallyNameless

import Language.HigherRank.Infer
import Language.HigherRank.Parser
import Language.HigherRank.Syntax

import Debug.Trace

newtype TestResult = TestResult (AnnTerm, [BasicConstraint], [Constraint], Solution)
instance Show TestResult where
  show (TestResult (ann, given, wanted, soln)) =
    "Term: \n" ++ showAnnTerm (\x -> prettyType x soln) ann ++ "\n" ++
    "Give: " ++ show given ++ "\n" ++
    "Want: " ++ show wanted ++ "\n" ++
    "Soln: " ++ show soln

testNil :: (TermVar, PolyType)
testNil = (string2Name "nil",
           PolyType_Inst (bind (a, embed PolyType_Bottom)
             (PolyType_Mono (listTy (mVar a)))))
          where a = string2Name "a"

testCons :: (TermVar, PolyType)
testCons = (string2Name "cons",
            PolyType_Inst (bind (a, embed PolyType_Bottom)
              (PolyType_Mono
                 (MonoType_Arrow (mVar a)
                    (MonoType_Arrow
                       (listTy (mVar a))
                       (listTy (mVar a)))))))
           where a = string2Name "a"

testTuple :: (TermVar, PolyType)
testTuple = (string2Name "tuple",
             PolyType_Inst (bind (a, embed PolyType_Bottom)
               (PolyType_Inst (bind (b, embed PolyType_Bottom)
                  (PolyType_Mono
                     (MonoType_Arrow (mVar a)
                        (MonoType_Arrow (mVar b)
                           (tupleTy (mVar a) (mVar b)))))))))
            where a = string2Name "a"
                  b = string2Name "b"

testFst :: (TermVar, PolyType)
testFst = (string2Name "tuple",
             PolyType_Inst (bind (a, embed PolyType_Bottom)
               (PolyType_Inst (bind (b, embed PolyType_Bottom)
                  (PolyType_Mono
                     (MonoType_Arrow
                        (tupleTy (mVar a) (mVar b))
                        (mVar a)))))))
          where a = string2Name "a"
                b = string2Name "b"

testSnd :: (TermVar, PolyType)
testSnd = (string2Name "tuple",
             PolyType_Inst (bind (a, embed PolyType_Bottom)
               (PolyType_Inst (bind (b, embed PolyType_Bottom)
                  (PolyType_Mono
                     (MonoType_Arrow
                        (tupleTy (mVar a) (mVar b))
                        (mVar b)))))))
          where a = string2Name "a"
                b = string2Name "b"

testEnv :: Env
testEnv = [testNil, testCons, testTuple, testFst, testSnd]

testString :: String -> Either String TestResult
testString s =
  case parse parseTerm "parse" s of
    Left  e -> Left (show e)
    Right t -> case runReaderT (runFreshMT $ infer t) testEnv of
      Left  e         -> Left e
      Right (_,a,c,q) -> case runFreshMT $ solve q c of
        Left  e  -> trace (show $ TestResult (a,q,c,[])) $ Left e
        Right sl -> Right $ TestResult (a,q,c,sl)
