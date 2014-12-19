{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cobalt.U.Rules.Check (
  check
, checkEnv
) where

import Control.Applicative
import Control.Monad (replicateM)
import Data.List (nub, (\\), intercalate)
import Data.MultiGenerics
import qualified Data.Regex.MultiGenerics as Rx
import qualified Data.Regex.MultiRules as Rx
import Data.Traversable (sequenceA)
import Test.QuickCheck
import Unbound.LocallyNameless hiding (from, to, union, generate, name)

import Cobalt.Core
import Cobalt.Language as Sy
import qualified Cobalt.OutsideIn as OIn
import Cobalt.U.Attributes
import Cobalt.U.Gather
import Cobalt.U.Rules.Translation
import Cobalt.U.Solver

import System.IO.Unsafe
import Unsafe.Coerce

check :: String -> RuleStrictness -> Sy.Env -> TypeRule -> Either String TypeRule
check name strictness env rule@(Rx.Rule rx _) =
  let samples = unsafePerformIO $ replicateM 20 $
                  generate (astGenerator (unsafeCoerce rx))
   in check_ samples
      where check_ [] = Right rule
            check_ (s : ss) = case okRule name strictness env rule s of
                                Left err -> Left err
                                Right _  -> check_ ss

checkEnv :: Sy.Env -> Either [String] Sy.Env
checkEnv env@(Sy.Env _ _ ax rules) = case checkEnv_ rules (1 :: Integer) of
  Just errs -> Left errs
  Nothing   -> Right env
  where checkEnv_ [] _ = Nothing
        checkEnv_ (r@(Rule s n _ _ _) : rest) i =
          case (check n s env (syntaxRuleToScriptRule ax r), checkEnv_ rest (i+1)) of
            (Left a, Just b) -> Just (a : b)
            (Left a, _     ) -> Just [a]
            (_,      Just b) -> Just b
            _                -> Nothing
        

astGenerator :: Rx.Regex (Rx.Wrap Integer) (UTerm_ ((SourcePos,SourcePos),TyVar,[TyVar])) IsATerm
             -> Gen (AnnUTerm TyVar)
astGenerator = Rx.arbitraryFromRegexAndGen generateVar

instance Arbitrary ((SourcePos,SourcePos),TyVar,[TyVar]) where
  arbitrary = (,,) <$> arbitrary
                   <*> arbitrary
                   <*> sequenceA (replicate nUMBER_OF_SPEC_RULES_VARS arbitrary)

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

generateVar :: forall (ix :: Ix). Sing ix -> Gen (Rx.Fix (UTerm_ ((SourcePos,SourcePos),TyVar,[TyVar])) ix)
generateVar SIsATerm = UTerm_Var <$> arbitrary <*> arbitrary
generateVar SIsACaseAlternative = error "Generation of case alternatives is not possible"

nUMBER_OF_SPEC_RULES_VARS :: Int
nUMBER_OF_SPEC_RULES_VARS = 20

okRule :: String -> RuleStrictness -> Sy.Env -> TypeRule -> AnnUTerm TyVar -> Either String TypeRule
okRule name strictness (Env fn dat ax _) (Rx.Rule rx action) term =
  let -- 1. Add extra information for open variables
      (newVars :: [AnnUTermVar TyVar]) = nub (fv term) \\ map (translate . fst) fn
      extraFns      = [(translate newVar, var (translate newVar)) | newVar <- newVars]
      newEnv        = Env (extraFns ++ fn) dat ax []
      -- 2. Generate a new rule which is always applicable
      rule          = Rx.Rule rx (\x y z -> let (_,u,v) = action x y z in (True,u,v))
      -- 3. Obtain the constraints
      evalWith      = Rx.eval (rule : mainTypeRules) (Rx.IndexIndependent (newEnv,[],[])) term
      evalWithout   = Rx.eval mainTypeRules (Rx.IndexIndependent (newEnv,[],[])) term
      printError from to rss errs = intercalate "\n" [ "term:",         show (atUAnn (\(_,x,_) -> x) term)
                                                     , "given:",        show from
                                                     , "wanted:",       show to
                                                     , "residual:",     show rss
                                                     , "errors:",       show errs ]
   in case (evalWith, evalWithout) of
        (GatherTerm gW [wW] _tW customW customWVars, GatherTerm gO [wO] _tO _ _) ->
           let -- Check soundness
               fromSpec  = customW ++ gW ++ gO ++ toConstraintList' wW
               toNonSpec = wO
               tchVars   = customWVars ++ fvScript toNonSpec
               (OIn.Solution _ rs ss _, errs, _) = runFreshM $ solve ax fromSpec tchVars toNonSpec
               rss = rs ++ residualSubstitution (tchVars \\ map translate newVars) ss
            in if null rss && null errs
                  then case strictness of
                         RuleStrictness_NonStrict -> Right rule
                         RuleStrictness_Strict ->
                           let -- Check completeness
                               fromNonSpec = customW ++ gW ++ gO ++ toConstraintList' wO
                               toSpec      = wW
                               tchVars2    = fvScript toSpec
                               (OIn.Solution _ rs2 ss2 _, errs2, _) = runFreshM $ solve ax fromNonSpec tchVars2 toSpec
                               rss2 = rs2 ++ residualSubstitution (tchVars2 \\ map translate newVars) ss2
                            in if null rss2 && null errs2
                                  then Right rule
                                  else Left $ name ++ " is not complete:\n" ++ printError fromNonSpec toSpec rss2 errs2
                  else Left $ name ++ " is not sound:\n" ++ printError fromSpec toNonSpec rss errs
        _ -> Left "error obtaining constraints"

residualSubstitution :: [TyVar] -> [(TyVar,MonoType)] -> [Constraint]
residualSubstitution _ [] = []
residualSubstitution tch ((v1, MonoType_Var v2) : rest)
  | v1 == v2 = residualSubstitution tch rest
residualSubstitution tch ((v1, m2) : rest)
  | v1 `notElem` tch = residualSubstitution tch rest
  | otherwise        = Constraint_Unify (var v1) m2 : residualSubstitution tch rest