{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.U.Rules.Translation (
  TypeRule
, syntaxRuleToScriptRule
) where

import Control.Applicative
import Control.Lens.Extras (is)
import Data.Foldable (fold)
import Data.List (elemIndex, union, insert)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx
import Unbound.LocallyNameless hiding (union)

import Cobalt.Core
import Cobalt.Language
import Cobalt.OutsideIn (entails)
import Cobalt.U.Attributes

import Unsafe.Coerce

type WI           = Wrap Integer
type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar)

type CaptureVarList = [TyVar]
type TranslationTypeEnv = [(TyVar, [MonoType])]
type TranslationExprEnv = [(TyVar, [UTerm ((SourcePos,SourcePos),TyVar)])]
type TranslationConsEnv = [(TyVar, [FreshM GatherTermInfo])]

(!!!) :: Eq a => [(a, b)] -> a -> b
(!!!) mp k = fromJust $ lookup k mp

-- Translation
syntaxRuleToScriptRule :: [Axiom] -> Rule -> TypeRule
syntaxRuleToScriptRule ax (Rule _ _ i) = runFreshM $ do
  (vars, (rx, check, script)) <- unbind i
  return $ Rx.Rule (Regex $ syntaxRegexToScriptRegex rx [] vars)
                   (\term envAndSat@(Rx.IndexIndependent (_,sat,tchs)) synChildren ->
                     let (p,thisTy)  = ann term
                         childrenMap = syntaxSynToMap synChildren
                         initialSyn  = foldr (mappend . snd) mempty childrenMap
                         rightSyns   = filter (is _Term . snd) childrenMap
                         (initialTy, exprs, constraints) = explodeMap vars rightSyns
                         checkW      = syntaxConstraintListToScript check thisTy initialTy
                         wanteds     = syntaxBindScriptToScript p thisTy initialTy exprs constraints script
                      in ( null check || entails ax sat checkW tchs
                         , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
                         , case initialSyn of
                             GatherTerm g _ _ -> GatherTerm g [term] [wanteds]
                             _ -> initialSyn  -- Float errors upwards
                         ) )

syntaxSynToMap :: Rx.Children WI Syn -> [(Integer, Gathered)]
syntaxSynToMap [] = []
syntaxSynToMap (Rx.Child (Wrap n) info : rest) =
  (n, fold (unsafeCoerce info :: [Gathered])) : syntaxSynToMap rest

explodeMap :: CaptureVarList -> [(Integer, Gathered)]
           -> (TranslationTypeEnv, TranslationExprEnv, TranslationConsEnv)
explodeMap _tyvars [] = ([], [], [])
explodeMap tyvars ((n, GatherTerm _ exprs i):rest) =
  let (t, e, c) = explodeMap tyvars rest
      v = tyvars !! fromEnum n
   in ( (v, map (var . snd . ann) exprs) : t, (v, exprs) : e, (v, i) : c)
explodeMap _ _ = error "This should never happen"

-- Translation of "match" block
syntaxRegexToScriptRegex :: RuleRegex -> [(RuleRegexVar, c IsATerm)]
                         -> CaptureVarList -> Regex' c WI UTermWithPos IsATerm
syntaxRegexToScriptRegex (RuleRegex_Square v) capturevars _tyvars =
  square $ fromJust $ lookup v capturevars
syntaxRegexToScriptRegex (RuleRegex_Iter   b) capturevars tyvars = runFreshM $ do
  (v, rx) <- unbind b
  return $ iter (\k -> syntaxRegexToScriptRegex rx ((v,k):capturevars) tyvars)
syntaxRegexToScriptRegex RuleRegex_Any _ _ = any_
syntaxRegexToScriptRegex (RuleRegex_Choice r1 r2) capturevars tyvars =
  syntaxRegexToScriptRegex r1 capturevars tyvars <||> syntaxRegexToScriptRegex r2 capturevars tyvars
syntaxRegexToScriptRegex (RuleRegex_App r1 r2) capturevars tyvars =
  inj $ UTerm_App_ (syntaxRegexToScriptRegex r1 capturevars tyvars)
                   (syntaxRegexToScriptRegex r2 capturevars tyvars)
                   __
syntaxRegexToScriptRegex (RuleRegex_Var s) _ _ = inj $ UTerm_Var_ (translate s) __
syntaxRegexToScriptRegex (RuleRegex_Int i) _ _ = inj $ UTerm_IntLiteral_ i __
syntaxRegexToScriptRegex (RuleRegex_Str s) _ _ = inj $ UTerm_StrLiteral_ s __
syntaxRegexToScriptRegex (RuleRegex_Capture n Nothing) _ tyvars =
  (Wrap $ toEnum $ fromJust $ elemIndex n tyvars) <<- any_
syntaxRegexToScriptRegex (RuleRegex_Capture n (Just r)) capturevars tyvars =
  (Wrap $ toEnum $ fromJust $ elemIndex n tyvars) <<- syntaxRegexToScriptRegex r capturevars tyvars

-- Translation of "script" block
syntaxBindScriptToScript :: (SourcePos, SourcePos)
                         -> TyVar -> TranslationTypeEnv -> TranslationExprEnv -> TranslationConsEnv
                         -> RuleScript -> FreshM GatherTermInfo
syntaxBindScriptToScript p this typeEnv exprEnv consEnv script = do
  (vars, statements) <- unbind script
  freshed <- mapM (fresh . s2n . tail . name2String) vars -- new var dropping '#'
  let varsFreshed = zipWith (\v f -> (v, [var f])) vars freshed
  GatherTermInfo sc c cv <- syntaxBindStatementsToScript p this (varsFreshed ++ typeEnv) exprEnv consEnv [] statements
  return $ GatherTermInfo sc c (freshed `union` cv)

syntaxBindStatementsToScript :: (SourcePos, SourcePos)
                             -> TyVar -> TranslationTypeEnv -> TranslationExprEnv -> TranslationConsEnv
                             -> [TyScript] -> [RuleScriptStatement] -> FreshM GatherTermInfo
syntaxBindStatementsToScript _ _ _ _ _ []  [] = fail "Empty stack at the end"
syntaxBindStatementsToScript _ _ _ _ _ [s] [] = return $ GatherTermInfo s [] []
syntaxBindStatementsToScript p _ _ _ _ xs  [] = return $ GatherTermInfo (Merge xs (Just p,Nothing)) [] []
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_Ref v : rest) =
  case lookup v consEnv of
    Just [i] -> do GatherTermInfo treeThis customThis customVarsThis <- i
                   GatherTermInfo r customR customVarsR <-
                     syntaxBindStatementsToScript p this typeEnv exprEnv consEnv
                                                  (treeThis : stack) rest
                   return $ GatherTermInfo r (customThis ++ customR) (customVarsThis `union` customVarsR)
    Just _   -> fail $ show v ++ " is not a single constraint"
    Nothing  -> fail $ "Cannot find " ++ show v
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_Constraint r msg : rest) =
  let newStackElt = Singleton (syntaxConstraintToScript r this typeEnv) (Just p, syntaxMessageToScript <$> msg)
   in syntaxBindStatementsToScript p this typeEnv exprEnv consEnv (newStackElt:stack) rest
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_Merge Nothing msg : rest) =
  let newStack = [Merge stack (Just p, syntaxMessageToScript <$> msg)]
   in syntaxBindStatementsToScript p this typeEnv exprEnv consEnv newStack rest
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_Merge (Just n) msg : rest) =
  let newStack = (Merge (take n stack) (Just p, syntaxMessageToScript <$> msg)) : drop n stack
   in syntaxBindStatementsToScript p this typeEnv exprEnv consEnv newStack rest
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_MergeBlameLast Nothing howMany msg : rest) =
  let upper = take howMany stack
      lower = drop howMany stack
      asym1 = case upper of { [x] -> x ; _ -> Merge upper (Just p, Nothing) }
      asym2 = case lower of { [x] -> x ; _ -> Merge lower (Just p, Nothing) }
      newStack = [Asym asym1 asym2 (Just p, syntaxMessageToScript <$> msg)]
   in syntaxBindStatementsToScript p this typeEnv exprEnv consEnv newStack rest
syntaxBindStatementsToScript p this typeEnv exprEnv consEnv stack (RuleScriptStatement_MergeBlameLast (Just n) howMany msg : rest) =
  let firstN = take n stack
      upper  = take howMany firstN
      lower  = drop howMany firstN
      asym1  = case upper of { [x] -> x ; _ -> Merge upper (Just p, Nothing) }
      asym2  = case lower of { [x] -> x ; _ -> Merge lower (Just p, Nothing) }
      newStack = Asym asym1 asym2 (Just p, syntaxMessageToScript <$> msg) : drop n stack
   in syntaxBindStatementsToScript p this typeEnv exprEnv consEnv newStack rest

-- Translation of types and constraints -- used in "check" block
syntaxConstraintListToScript :: [Constraint] -> TyVar -> TranslationTypeEnv -> [Constraint]
syntaxConstraintListToScript cs this captures =
  map (\c -> syntaxConstraintToScript c this captures) cs

syntaxConstraintToScript :: Constraint -> TyVar -> TranslationTypeEnv -> Constraint
syntaxConstraintToScript (Constraint_Unify m1 m2) this captures =
  Constraint_Unify (syntaxMonoTypeToScript m1 this captures)
                   (syntaxMonoTypeToScript m2 this captures)
syntaxConstraintToScript (Constraint_Inst m1 m2) this captures =
  Constraint_Inst  (syntaxMonoTypeToScript m1 this captures)
                   (runFreshM $ syntaxPolyTypeToScript m2 this captures)
syntaxConstraintToScript (Constraint_Equal m1 m2) this captures =
  Constraint_Equal (syntaxMonoTypeToScript m1 this captures)
                   (runFreshM $ syntaxPolyTypeToScript m2 this captures)
syntaxConstraintToScript (Constraint_Class c ms) this captures =
  Constraint_Class c (map (\m -> syntaxMonoTypeToScript m this captures) ms)
syntaxConstraintToScript (Constraint_Exists _) _ _ =
  error "Existential constraints not allowed"
syntaxConstraintToScript Constraint_Inconsistent _ _ =
  Constraint_Inconsistent

syntaxMonoTypeToScript :: MonoType -> TyVar -> TranslationTypeEnv -> MonoType
syntaxMonoTypeToScript f@(MonoType_Fam _ []) _ _ = f
syntaxMonoTypeToScript (MonoType_Fam f ms) this captures =
  MonoType_Fam f (map (\m -> syntaxMonoTypeToScript m this captures) ms)
syntaxMonoTypeToScript f@(MonoType_Con _ []) _ _ = f
syntaxMonoTypeToScript (MonoType_Con f ms) this captures =
  MonoType_Con f (map (\m -> syntaxMonoTypeToScript m this captures) ms)
syntaxMonoTypeToScript (MonoType_Var v) this captures =
  case name2String v of
    -- Variables starting with # refer to captured variables
    "#this" -> MonoType_Var this
    '#':_   -> case captures !!! v of
                 [m] -> m
                 _   -> error "Using multiple types where only one is expected"
    _       -> MonoType_Var v
syntaxMonoTypeToScript (MonoType_Arrow t1 t2) this captures = do
  MonoType_Arrow (syntaxMonoTypeToScript t1 this captures)
                 (syntaxMonoTypeToScript t2 this captures)

syntaxPolyTypeToScript :: PolyType -> TyVar -> TranslationTypeEnv -> FreshM PolyType
syntaxPolyTypeToScript (PolyType_Bind b) this captures = do
  (v,p) <- unbind b
  inn   <- syntaxPolyTypeToScript p this captures
  return $ PolyType_Bind (bind v inn)
syntaxPolyTypeToScript (PolyType_Mono [] m) this captures =
  return $ PolyType_Mono [] (syntaxMonoTypeToScript m this captures)
syntaxPolyTypeToScript (PolyType_Mono cs m) this captures =
  return $ PolyType_Mono (map (\c -> syntaxConstraintToScript c this captures) cs)
                         (syntaxMonoTypeToScript m this captures)
syntaxPolyTypeToScript PolyType_Bottom _ _ = return PolyType_Bottom

-- Translation of messages
syntaxMessageToScript :: RuleScriptMessage -> String
syntaxMessageToScript (RuleScriptMessage_Literal l) = l
syntaxMessageToScript _                             = error "Only literals are supported"
