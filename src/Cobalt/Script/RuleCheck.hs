{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cobalt.Script.RuleCheck (
  check
, checkEnv
) where

import Control.Applicative
import Control.Monad (replicateM)
import Data.List (nub, (\\), intercalate)
import Data.MultiGenerics
import qualified Data.Regex.MultiGenerics as Rx
import qualified Data.Regex.MultiRules as Rx
import Test.QuickCheck
import Text.Parsec.Pos (newPos)
import Unbound.LocallyNameless hiding (from, union, generate)

import Cobalt.Language.Syntax as Sy
import qualified Cobalt.OutsideIn.Solver as OIn
import Cobalt.Script.Gather
import Cobalt.Script.Rules
import Cobalt.Script.Script
import Cobalt.Script.Solver
import Cobalt.Script.Syntax
import Cobalt.Types

import System.IO.Unsafe
import Unsafe.Coerce

check :: Sy.Env -> TypeRule -> Either String TypeRule
check env rule@(Rx.Rule rx _) =
  let samples = unsafePerformIO $ replicateM 100 $
                  generate (astGenerator (unsafeCoerce rx))
   in check_ samples
      where check_ [] = Right rule
            check_ (s : ss) = case okRule env rule s of
                                Left err -> Left err
                                Right _  -> check_ ss

checkEnv :: Sy.Env -> Either [String] Sy.Env
checkEnv env@(Sy.Env _ _ ax rules) = case checkEnv_ rules (1 :: Integer) of
  Just errs -> Left errs
  Nothing   -> Right env
  where checkEnv_ [] _ = Nothing
        checkEnv_ (r:rest) i = case (check env (syntaxRuleToScriptRule ax r), checkEnv_ rest (i+1)) of
                                 (Left a, Just b) -> Just (("RULE " ++ show i ++ ":\n" ++ a) : b)
                                 (Left a, _     ) -> Just ["RULE " ++ show i ++ ":\n" ++ a]
                                 (_,      Just b) -> Just b
                                 _                -> Nothing
        

astGenerator :: Rx.Regex (Rx.Wrap Integer) (UTerm_ ((SourcePos,SourcePos),TyVar)) IsATerm
             -> Gen (AnnUTerm TyVar)
astGenerator rx = Rx.arbitraryFromRegexAndGen generateVar rx

instance Arbitrary Constraint where
  arbitrary = error "Generation of constraints is not possible"
instance Arbitrary MonoType where
  arbitrary = error "Generation of monotypes is not possible"
instance Arbitrary PolyType where
  arbitrary = error "Generation of polytypes is not possible"

instance Arbitrary SourcePos where
  arbitrary = return (newPos "" 0 0)

instance Rep f => Arbitrary (Name f) where
  arbitrary = do Positive n <- resize 100000 arbitrary
                 return $ string2Name $ "x" ++ show (n :: Int)

generateVar :: forall (ix :: Ix). Sing ix -> Gen (Rx.Fix (UTerm_ ((SourcePos,SourcePos),TyVar)) ix)
generateVar SIsATerm = UTerm_Var <$> arbitrary <*> arbitrary
generateVar SIsACaseAlternative = error "Generation of case alternatives is not possible"

okRule :: Sy.Env -> TypeRule -> AnnUTerm TyVar -> Either String TypeRule
okRule (Env fn dat ax _) rule term =
  let -- 1. Add extra information for open variables
      (newVars :: [AnnUTermVar TyVar]) = nub (fv term) \\ map (translate . fst) fn
      extraFns      = [(translate newVar, var (translate newVar)) | newVar <- newVars]
      newEnv        = Env (extraFns ++ fn) dat ax []
      -- 2. Obtain the constraints
      evalWith      = Rx.eval (rule : mainTypeRules) (Rx.IndexIndependent (newEnv,[],[])) term
      evalWithout   = Rx.eval mainTypeRules (Rx.IndexIndependent (newEnv,[],[])) term
   in case (evalWith, evalWithout) of
        (GatherTerm gW [wW] _tW, GatherTerm gO [wO] _tO) -> 
           let from = gW ++ gO ++ toConstraintList' wW
               (OIn.Solution _ rs _ _, errs, _) = runFreshM $ solve ax from (fvScript wO) wO
            in if null rs && null errs
                  then Right rule
                  else Left $ intercalate "\n" ["term:",show (atUAnn (\(_,x) -> x) term)
                                               ,"given:",show from
                                               ,"wanted:",show wW
                                               ,"residual:",show rs
                                               ,"errors:",show errs]
        _ -> Left $ "error obtaining constraints"
