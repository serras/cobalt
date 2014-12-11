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
import Unbound.LocallyNameless hiding (from, to, union, generate, name)

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

check :: String -> RuleStrictness -> Sy.Env -> TypeRule -> Either String TypeRule
check name strictness env rule@(Rx.Rule rx _) =
  let samples = unsafePerformIO $ replicateM 100 $
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
        

astGenerator :: Rx.Regex (Rx.Wrap Integer) (UTerm_ ((SourcePos,SourcePos),TyVar)) IsATerm
             -> Gen (AnnUTerm TyVar)
astGenerator = Rx.arbitraryFromRegexAndGen generateVar

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
      printError from to rs ss errs = intercalate "\n" [ "term:",         show (atUAnn snd term)
                                                       , "given:",        show from
                                                       , "wanted:",       show to
                                                       , "residual:",     show rs
                                                       , "substitution:", show ss
                                                       , "errors:",       show errs ]
   in case (evalWith, evalWithout) of
        (GatherTerm gW [wW] _tW customW, GatherTerm gO [wO] _tO _) ->
           let -- Check soundness
               fromSpec  = customW ++ gW ++ gO ++ toConstraintList' wW
               toNonSpec = wO
               tchVars   = fvScript toNonSpec
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
                                  else Left $ name ++ " is not complete:\n" ++ printError fromNonSpec toSpec rs2 ss2 errs2
                  else Left $ name ++ " is not sound:\n" ++ printError fromSpec toNonSpec rs ss errs
        _ -> Left "error obtaining constraints"

residualSubstitution :: [TyVar] -> [(TyVar,MonoType)] -> [Constraint]
residualSubstitution _ [] = []
residualSubstitution tch ((v1, MonoType_Var v2) : rest)
  | v1 == v2 = residualSubstitution tch rest
residualSubstitution tch ((v1, m2) : rest)
  | v1 `notElem` tch = residualSubstitution tch rest
  | otherwise        = Constraint_Unify (var v1) m2 : residualSubstitution tch rest