{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.Script.Rules (
  Errors
, Inh
, theEnv
, theSat
, theTouchables
, Syn(..)
, Gathered
, GatherCaseInfo(..)
, _Error
, _Term
, given
, wanted
, ty
, _Case
, TypeRule
, syntaxRuleToScriptRule
) where

import Control.Lens hiding (at)
import Control.Lens.Extras
import Data.Foldable (fold)
import Data.List (elemIndex, union, insert)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx
import Unbound.LocallyNameless hiding (union)

import Cobalt.Language.Syntax as Sy
import Cobalt.OutsideIn.Solver (entails)
import Cobalt.Script.Script
import Cobalt.Script.Syntax
import Cobalt.Types

import Unsafe.Coerce

type Errors = [String]
data Syn (ix :: Ix) where
  Error      :: Errors -> Syn ix
  GatherTerm :: [Constraint] -> [TyScript] -> [TyVar]  -> Syn IsATerm
  GatherCase :: [GatherCaseInfo] -> Syn IsACaseAlternative

data GatherCaseInfo = GatherCaseInfo { _extraConstraints :: [Constraint]
                                     , _hiddenVars :: [TyVar]
                                     , _konQ :: [Constraint]
                                     , _konT :: MonoType
                                     , _script :: TyScript
                                     , _thisVar :: TyVar
                                     }

type Gathered = Syn IsATerm

_Error :: Prism' (Syn ix) Errors
_Error = prism Error (\x -> case x of
                              Error e -> Right e
                              _       -> Left x)

_Term :: Prism' (Syn IsATerm) ([Constraint], [TyScript], [TyVar])
_Term = prism (\(g,w,t) -> GatherTerm g w t)
              (\x -> case x of
                       GatherTerm g w t -> Right (g,w,t)
                       _                -> Left x)

given :: Functor f => ([Constraint] -> f [Constraint])
      -> ([Constraint],[TyScript],[TyVar]) -> f ([Constraint],[TyScript],[TyVar])
given  = _1

wanted :: Functor f => ([TyScript] -> f [TyScript])
       -> ([Constraint],[TyScript],[TyVar]) -> f ([Constraint],[TyScript],[TyVar])
wanted = _2

ty :: Functor f => ([TyVar] -> f [TyVar])
   -> ([Constraint],[TyScript],[TyVar]) -> f ([Constraint],[TyScript],[TyVar])
ty     = _3

_Case :: Prism' (Syn IsACaseAlternative) [GatherCaseInfo]
_Case = prism (\g -> GatherCase g)
              (\x -> case x of
                       GatherCase g -> Right g
                       _            -> Left x)

-- Internal accessors
termWanted :: Gathered -> [TyScript]
termWanted (GatherTerm _ w _) = w
termWanted _                  = error "This is not a term synthesized attribute"

termTy :: Gathered -> [TyVar]
termTy (GatherTerm _ _ t) = t
termTy _                  = error "This is not a term synthesized attribute"

instance Monoid (Syn IsATerm) where
  mempty = GatherTerm [] [] []
  (Error e1) `mappend` (Error e2) = Error (union e1 e2)
  e@(Error _) `mappend` _ = e
  _ `mappend` e@(Error _) = e
  (GatherTerm g1 w1 v1) `mappend` (GatherTerm g2 w2 v2) = GatherTerm (g1 ++ g2) (w1 ++ w2) (v1 ++ v2)

instance Monoid (Syn IsACaseAlternative) where
  mempty = GatherCase []
  (Error e1) `mappend` (Error e2) = Error (union e1 e2)
  e@(Error _) `mappend` _ = e
  _ `mappend` e@(Error _) = e
  (GatherCase i1) `mappend` (GatherCase i2) = GatherCase (i1 ++ i2)

type Inh = Rx.IndexIndependent (Env, [Constraint], [TyVar])

theEnv :: Functor f => (Env -> f Env)
       -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theEnv = _1

theSat :: Functor f => ([Constraint] -> f [Constraint])
       -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theSat = _2

theTouchables :: Functor f => ([TyVar] -> f [TyVar])
              -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theTouchables = _3

type WI           = Wrap Integer
type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar)
type TypeRule     = Rx.Rule WI UTermWithPos Inh Syn

syntaxRuleToScriptRule :: [Axiom] -> Sy.Rule -> TypeRule
syntaxRuleToScriptRule ax (Rule rx check script) = 
  let vars = getCaptureVars rx
   in Rx.Rule
        (Regex $ syntaxRegexToScriptRegex rx [] vars)
        (\term envAndSat@(Rx.IndexIndependent (_,sat,tchs)) synChildren ->
          let (p,thisTy)  = ann term
              childrenMap = syntaxSynToMap synChildren
              initialSyn  = foldr mappend mempty $ map snd childrenMap
              rightSyns   = filter (is _Term . snd) childrenMap
              checkW      = syntaxConstraintListToScript check thisTy vars rightSyns
              wanteds     = syntaxScriptToScript script p thisTy vars rightSyns
           in ( null check || entails ax sat (checkW) tchs
              , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
              , case initialSyn of
                  GatherTerm g _ _ -> GatherTerm g [wanteds] [thisTy]
                  _ -> initialSyn  -- Float errors upwards
              ) )

type CaptureVarList = [String]

getCaptureVars :: Sy.RuleRegex -> CaptureVarList
getCaptureVars (Sy.RuleRegex_Capture s Nothing)  = [s]
getCaptureVars (Sy.RuleRegex_Capture s (Just r)) = insert s (getCaptureVars r)
getCaptureVars (Sy.RuleRegex_App     r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (Sy.RuleRegex_Choice  r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (Sy.RuleRegex_Iter        b) = runFreshM $ do (_,rx) <- unbind b
                                                             return $ getCaptureVars rx
getCaptureVars _                            = []

syntaxRegexToScriptRegex :: Sy.RuleRegex -> [(RuleRegexVar, c IsATerm)]
                         -> CaptureVarList -> Regex' c WI UTermWithPos IsATerm
syntaxRegexToScriptRegex (Sy.RuleRegex_Square v) varMap _ = square $ fromJust $ lookup v varMap
syntaxRegexToScriptRegex (Sy.RuleRegex_Iter   b) varMap captureMap = runFreshM $ do
  (v, rx) <- unbind b
  return $ iter (\k -> syntaxRegexToScriptRegex rx ((v,k):varMap) captureMap)
syntaxRegexToScriptRegex Sy.RuleRegex_Any _ _ = any_
syntaxRegexToScriptRegex (Sy.RuleRegex_Choice r1 r2) varMap captureMap =
  syntaxRegexToScriptRegex r1 varMap captureMap <||> syntaxRegexToScriptRegex r2 varMap captureMap
syntaxRegexToScriptRegex (Sy.RuleRegex_App r1 r2) varMap captureMap = 
  inj $ UTerm_App_ (syntaxRegexToScriptRegex r1 varMap captureMap)
                   (syntaxRegexToScriptRegex r2 varMap captureMap)
                   __
syntaxRegexToScriptRegex (Sy.RuleRegex_Var s) _ _ = inj $ UTerm_Var_ (s2n s) __
syntaxRegexToScriptRegex (Sy.RuleRegex_Int i) _ _ = inj $ UTerm_IntLiteral_ i __
syntaxRegexToScriptRegex (Sy.RuleRegex_Capture n Nothing) _ captureMap =
  (Wrap $ toEnum $ fromJust $ elemIndex n captureMap) <<- any_
syntaxRegexToScriptRegex (Sy.RuleRegex_Capture n (Just r)) varMap captureMap =
  (Wrap $ toEnum $ fromJust $ elemIndex n captureMap) <<- syntaxRegexToScriptRegex r varMap captureMap

syntaxSynToMap :: Rx.Children WI Syn -> [(Integer, Gathered)]
syntaxSynToMap [] = []
syntaxSynToMap (Rx.Child (Wrap n) info : rest) = (n, fold (unsafeCoerce info :: [Gathered])) : syntaxSynToMap rest

(!!!) :: [(Integer, Gathered)] -> Int -> Gathered
(!!!) mp k = fromJust $ lookup (toEnum k) mp

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
  c where [c] = termWanted (captures !!! (fromJust $ elemIndex s capVars))

syntaxScriptListToScript :: RuleScriptList -> (SourcePos,SourcePos) -> TyVar
                         -> CaptureVarList -> [(Integer, Gathered)] -> [TyScript]
syntaxScriptListToScript (RuleScriptList_Ref s) _ _ capVars captures =
  termWanted (captures !!! (fromJust $ elemIndex s capVars))
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
  ss <- map (\m -> syntaxMonoTypeToScript m this capVars captures) ms
  return $ MonoType_Fam f ss
syntaxMonoTypeToScript f@(MonoType_Con _ []) _ _ _ = return f
syntaxMonoTypeToScript (MonoType_Con f ms) this capVars captures = do
  ss <- map (\m -> syntaxMonoTypeToScript m this capVars captures) ms
  return $ MonoType_Con f ss
syntaxMonoTypeToScript (MonoType_Var v) this capVars captures =
  case name2String v of
    -- Variables starting with # refer to captured variables
    "#this" -> return $ MonoType_Var this
    '#':s   -> do tyx <- termTy (captures !!! (fromJust $ elemIndex s capVars))
                  return $ MonoType_Var (translate tyx)
    _       -> return $ MonoType_Var v
syntaxMonoTypeToScript (MonoType_Arrow t1 t2) this capVars captures = do
  ty1 <- syntaxMonoTypeToScript t1 this capVars captures
  ty2 <- syntaxMonoTypeToScript t2 this capVars captures
  return $ MonoType_Arrow ty1 ty2

syntaxPolyTypeToScript :: PolyType -> TyVar -> CaptureVarList -> [(Integer, Gathered)] -> FreshM [PolyType]
syntaxPolyTypeToScript (PolyType_Bind b) this capVars captures = do
  (v,p)  <- unbind b
  inn <- syntaxPolyTypeToScript p this capVars captures
  return $ map (\item -> PolyType_Bind $ bind v item) inn
syntaxPolyTypeToScript (PolyType_Mono cs m) this capVars captures =
  return $ do cs2 <- map (\c -> syntaxConstraintToScript c this capVars captures) cs
              m2  <- syntaxMonoTypeToScript m this capVars captures
              return $ PolyType_Mono cs2 m2
syntaxPolyTypeToScript PolyType_Bottom _ _ _ = return $ return PolyType_Bottom
