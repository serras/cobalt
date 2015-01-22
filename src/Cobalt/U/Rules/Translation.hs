{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.U.Rules.Translation (
  TypeRule
, syntaxRuleToScriptRule
) where

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

-- Internal accessors
termWanted :: Gathered -> [TyScript]
termWanted (GatherTerm _ w _ _ _) = w
termWanted _                      = error "This is not a term synthesized attribute"

termTy :: Gathered -> [TyVar]
termTy (GatherTerm _ _ t _ _) = t
termTy _                      = error "This is not a term synthesized attribute"

type WI           = Wrap Integer
type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar,[TyVar])

syntaxRuleToScriptRule :: [Axiom] -> Rule -> TypeRule
syntaxRuleToScriptRule ax (Rule _ _ rx check script) =
  let vars = getCaptureVars rx
   in Rx.Rule
        (Regex $ syntaxRegexToScriptRegex rx [] vars)
        (\term envAndSat@(Rx.IndexIndependent (_,sat,tchs)) synChildren ->
          let (p,thisTy,specTys) = ann term
              childrenMap = syntaxSynToMap synChildren
              initialSyn  = foldr (mappend . snd) mempty childrenMap
              rightSyns   = filter (is _Term . snd) childrenMap
              checkW      = syntaxConstraintListToScript check thisTy vars rightSyns
              wanteds     = syntaxBindScriptToScript script p thisTy specTys vars rightSyns
           in ( null check || entails ax sat checkW tchs
              , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
              , case initialSyn of
                  GatherTerm g _ _ c cv -> GatherTerm g [wanteds] [thisTy] (checkW ++ c) (specTys ++ cv)
                  _ -> initialSyn  -- Float errors upwards
              ) )

type CaptureVarList = [String]

getCaptureVars :: RuleRegex -> CaptureVarList
getCaptureVars (RuleRegex_Capture s Nothing)  = [s]
getCaptureVars (RuleRegex_Capture s (Just r)) = insert s (getCaptureVars r)
getCaptureVars (RuleRegex_App     r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (RuleRegex_Choice  r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (RuleRegex_Iter        b) = runFreshM $ do (_,rx) <- unbind b
                                                          return $ getCaptureVars rx
getCaptureVars _                         = []

syntaxRegexToScriptRegex :: RuleRegex -> [(RuleRegexVar, c IsATerm)]
                         -> CaptureVarList -> Regex' c WI UTermWithPos IsATerm
syntaxRegexToScriptRegex (RuleRegex_Square v) varMap _ = square $ fromJust $ lookup v varMap
syntaxRegexToScriptRegex (RuleRegex_Iter   b) varMap captureMap = runFreshM $ do
  (v, rx) <- unbind b
  return $ iter (\k -> syntaxRegexToScriptRegex rx ((v,k):varMap) captureMap)
syntaxRegexToScriptRegex RuleRegex_Any _ _ = any_
syntaxRegexToScriptRegex (RuleRegex_Choice r1 r2) varMap captureMap =
  syntaxRegexToScriptRegex r1 varMap captureMap <||> syntaxRegexToScriptRegex r2 varMap captureMap
syntaxRegexToScriptRegex (RuleRegex_App r1 r2) varMap captureMap =
  inj $ UTerm_App_ (syntaxRegexToScriptRegex r1 varMap captureMap)
                   (syntaxRegexToScriptRegex r2 varMap captureMap)
                   __
syntaxRegexToScriptRegex (RuleRegex_Var s) _ _ = inj $ UTerm_Var_ (s2n s) __
syntaxRegexToScriptRegex (RuleRegex_Int i) _ _ = inj $ UTerm_IntLiteral_ i __
syntaxRegexToScriptRegex (RuleRegex_Capture n Nothing) _ captureMap =
  (Wrap $ toEnum $ fromJust $ elemIndex n captureMap) <<- any_
syntaxRegexToScriptRegex (RuleRegex_Capture n (Just r)) varMap captureMap =
  (Wrap $ toEnum $ fromJust $ elemIndex n captureMap) <<- syntaxRegexToScriptRegex r varMap captureMap

syntaxSynToMap :: Rx.Children WI Syn -> [(Integer, Gathered)]
syntaxSynToMap [] = []
syntaxSynToMap (Rx.Child (Wrap n) info : rest) = (n, fold (unsafeCoerce info :: [Gathered])) : syntaxSynToMap rest

(!!!) :: [(Integer, Gathered)] -> Int -> Gathered
(!!!) mp k = fromJust $ lookup (toEnum k) mp

syntaxBindScriptToScript :: Bind [TyVar] RuleScript -> (SourcePos,SourcePos) -> TyVar -> [TyVar]
                         -> CaptureVarList -> [(Integer, Gathered)] -> TyScript
syntaxBindScriptToScript b p this specTys capVars captures =
  let unboundScript = runFreshM $ do (bVars, s) <- unbind b
                                     return $ substs (zip bVars (map var specTys)) s
   in syntaxScriptToScript unboundScript p this capVars captures

syntaxScriptToScript :: RuleScript -> (SourcePos,SourcePos) -> TyVar
                     -> CaptureVarList -> [(Integer, Gathered)] -> TyScript
syntaxScriptToScript (RuleScript_Merge lst info) p this capVars captures =
  Merge (syntaxScriptListToScript lst p this capVars captures) (Just p, info)
syntaxScriptToScript (RuleScript_Asym r1 r2 info) p this capVars captures =
  Asym (syntaxScriptToScript r1 p this capVars captures)
       (syntaxScriptToScript r2 p this capVars captures)
       (Just p, info)
syntaxScriptToScript (RuleScript_Singleton c info) p this capVars captures =
  let [oneRule] = syntaxConstraintToScript c this capVars captures
   in Singleton oneRule (Just p, info)
syntaxScriptToScript (RuleScript_Ref s) _ _ capVars captures =
  c where [c] = termWanted (captures !!! fromJust (elemIndex s capVars))

syntaxScriptListToScript :: RuleScriptList -> (SourcePos,SourcePos) -> TyVar
                         -> CaptureVarList -> [(Integer, Gathered)] -> [TyScript]
syntaxScriptListToScript (RuleScriptList_Ref s) _ _ capVars captures =
  termWanted (captures !!! fromJust (elemIndex s capVars))
syntaxScriptListToScript (RuleScriptList_List items) p this capVars captures =
  map (\item -> syntaxScriptToScript item p this capVars captures) items
syntaxScriptListToScript (RuleScriptList_PerItem c info) p this capVars captures =
  map (\t -> Singleton t (Just p, info)) (syntaxConstraintToScript c this capVars captures)

syntaxConstraintListToScript :: [Constraint] -> TyVar -> CaptureVarList -> [(Integer, Gathered)] -> [Constraint]
syntaxConstraintListToScript cs this capVars captures =
  concatMap (\c -> syntaxConstraintToScript c this capVars captures) cs

syntaxConstraintToScript :: Constraint -> TyVar -> CaptureVarList -> [(Integer, Gathered)] -> [Constraint]
syntaxConstraintToScript (Constraint_Unify m1 m2) this capVars captures = do
  m1s <- syntaxMonoTypeToScript m1 this capVars captures
  m2s <- syntaxMonoTypeToScript m2 this capVars captures
  return $ Constraint_Unify m1s m2s
syntaxConstraintToScript (Constraint_Inst m1 m2) this capVars captures = do
  m1s <- syntaxMonoTypeToScript m1 this capVars captures
  m2s <- runFreshM $ syntaxPolyTypeToScript m2 this capVars captures
  return $ Constraint_Inst m1s m2s
syntaxConstraintToScript (Constraint_Equal m1 m2) this capVars captures = do
  m1s <- syntaxMonoTypeToScript m1 this capVars captures
  m2s <- runFreshM $ syntaxPolyTypeToScript m2 this capVars captures
  return $ Constraint_Equal m1s m2s
syntaxConstraintToScript (Constraint_Class c ms) this capVars captures = do
  mss <- map (\m -> syntaxMonoTypeToScript m this capVars captures) ms
  return $ Constraint_Class c mss
syntaxConstraintToScript (Constraint_Exists _) _ _ _ =
  error "Existential constraints not allowed"
syntaxConstraintToScript Constraint_Inconsistent _ _ _ =
  return Constraint_Inconsistent

syntaxMonoTypeToScript :: MonoType -> TyVar -> CaptureVarList -> [(Integer, Gathered)] -> [MonoType]
syntaxMonoTypeToScript f@(MonoType_Fam _ []) _ _ _ = return f
syntaxMonoTypeToScript (MonoType_Fam f ms) this capVars captures = do
  ss <- cartesianProduct (\m -> syntaxMonoTypeToScript m this capVars captures) ms
  return $ MonoType_Fam f ss
syntaxMonoTypeToScript f@(MonoType_Con _ []) _ _ _ = return f
syntaxMonoTypeToScript (MonoType_Con f ms) this capVars captures = do
  ss <- cartesianProduct (\m -> syntaxMonoTypeToScript m this capVars captures) ms
  return $ MonoType_Con f ss
syntaxMonoTypeToScript (MonoType_Var v) this capVars captures =
  case name2String v of
    -- Variables starting with # refer to captured variables
    "#this" -> return $ MonoType_Var this
    '#':s   -> do tyx <- termTy (captures !!! fromJust (elemIndex s capVars))
                  return $ MonoType_Var (translate tyx)
    _       -> return $ MonoType_Var v
syntaxMonoTypeToScript (MonoType_Arrow t1 t2) this capVars captures = do
  ty1 <- syntaxMonoTypeToScript t1 this capVars captures
  ty2 <- syntaxMonoTypeToScript t2 this capVars captures
  return $ MonoType_Arrow ty1 ty2

cartesianProduct :: (a -> [b]) -> [a] -> [[b]]
cartesianProduct _ [] = return []
cartesianProduct f (x:xs) = do
  y  <- f x
  ys <- cartesianProduct f xs
  return (y:ys)

syntaxPolyTypeToScript :: PolyType -> TyVar -> CaptureVarList -> [(Integer, Gathered)] -> FreshM [PolyType]
syntaxPolyTypeToScript (PolyType_Bind b) this capVars captures = do
  (v,p) <- unbind b
  inn   <- syntaxPolyTypeToScript p this capVars captures
  return $ map (PolyType_Bind . bind v) inn
syntaxPolyTypeToScript (PolyType_Mono [] m) this capVars captures =
  return $ do m2 <- syntaxMonoTypeToScript m this capVars captures
              return $ PolyType_Mono [] m2
syntaxPolyTypeToScript (PolyType_Mono cs m) this capVars captures =
  return $ do cs2 <- map (\c -> syntaxConstraintToScript c this capVars captures) cs
              m2  <- syntaxMonoTypeToScript m this capVars captures
              return $ PolyType_Mono cs2 m2
syntaxPolyTypeToScript PolyType_Bottom _ _ _ = return $ return PolyType_Bottom
