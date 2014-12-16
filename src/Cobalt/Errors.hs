{-# LANGUAGE RecordWildCards #-}
{-# ANN module ("HLint: ignore Use camelCase"::String) #-}
module Cobalt.Errors where

import Text.Parsec.Pos

import Cobalt.Types

data Comment = Comment_String String
             | Comment_Pos (SourcePos, SourcePos)
             deriving (Show, Eq)

data SolverError = SolverError_Unify UnifyErrorReason MonoType MonoType
                 | SolverError_Infinite TyVar MonoType
                 | SolverError_Equiv PolyType PolyType
                 | SolverError_CouldNotDischarge [Constraint]
                 | SolverError_NonTouchable [TyVar]
                 | SolverError_Inconsistency
                 | SolverError_Ambiguous TyVar [Constraint]

instance Show SolverError where
  show (SolverError_Unify r m1 m2) = "Could not unify " ++ show m1 ++ " ~ " ++ show m2 ++ " (" ++ show r ++ ")"
  show (SolverError_Infinite tv m) = "Could not construct infinite type " ++ show tv ++ " ~ " ++ show m
  show (SolverError_Equiv m1 m2) = "Could not prove equivalence between " ++ show m1 ++ " = " ++ show m2
  show (SolverError_CouldNotDischarge cs) = "Could not discharge " ++ show cs
  show (SolverError_NonTouchable vs) = "Unifying non-touchable variables " ++ show vs
  show SolverError_Inconsistency = "Inconsistent constraint found"
  show (SolverError_Ambiguous v c) = "Ambiguous type variable " ++ show v ++ " stemming from " ++ show c

data UnifyErrorReason = UnifyErrorReason_Head
                      | UnifyErrorReason_NumberOfArgs

instance Show UnifyErrorReason where
  show UnifyErrorReason_Head = "different head constructors"
  show UnifyErrorReason_NumberOfArgs = "different number of arguments"

data ErrorExplanation = SolverError { theError   :: SolverError
                                    , thePoint   :: Maybe (SourcePos, SourcePos)
                                    , theMessage :: Maybe String
                                    , theBlame   :: [(Constraint,[Comment])]
                                    }
                      | ErrorFromPreviousPhase { thePoint   :: Maybe (SourcePos, SourcePos)
                                               , theMessage :: Maybe String }

emptySolverExplanation :: SolverError -> ErrorExplanation
emptySolverExplanation err = SolverError err Nothing Nothing []

errorFromPreviousPhase :: String -> ErrorExplanation
errorFromPreviousPhase s = ErrorFromPreviousPhase Nothing (Just s)

instance Show ErrorExplanation where
  show SolverError { theBlame = [], .. } = "Found error at " ++ showPoint thePoint
                                           ++ ":\n  " ++ show theError
  show SolverError { theBlame = b, .. } = "Found error at " ++ showPoint thePoint
                                          ++ ":\n  " ++ show theError
                                          ++ "\nstemming from:" ++ concatMap (('\n' :) . showProblem) b
  show ErrorFromPreviousPhase { .. } = "Found error at point " ++ showPoint thePoint
                                       ++ ":\n" ++ show theMessage

showProblem :: (Constraint,[Comment]) -> String
showProblem (c,cms) = "* " ++ show c ++ concatMap (("\n  " ++) . showComment) cms

showComment :: Comment -> String
showComment (Comment_String s)  = "since " ++ s
showComment (Comment_Pos (i,e)) = "at " ++ show i ++ " -- " ++ show e

showPoint :: Maybe (SourcePos, SourcePos) -> String
showPoint Nothing      = "<unknown>"
showPoint (Just (i,e)) = show i ++ " -- " ++ show e