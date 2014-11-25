{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Cobalt.Script.Rules (
  Errors
, Gathered(Gathered)
, givenC
, wantedC
, ty
, Inh
, Syn
, TypeRule
, syntaxRuleToScriptRule
) where

import Control.Lens hiding (at)
import Data.List (elemIndex)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.Generics hiding (var)
import qualified Data.Regex.Rules as Rx
import Unbound.LocallyNameless

import Cobalt.Language.Syntax as Sy
import Cobalt.Script.Script
import Cobalt.Script.Syntax
import Cobalt.Types

type Errors = [String]
data Gathered = Gathered { _givenC  :: [Constraint]
                         , _wantedC :: [TyScript]
                         , _ty      :: [TyVar]
                         }
              deriving Show
makeLenses ''Gathered

instance Monoid Gathered where
  mempty = Gathered [] [] []
  (Gathered g1 w1 v1) `mappend` (Gathered g2 w2 v2)
    = Gathered (g1 ++ g2) (w1 ++ w2) (v1 ++ v2)

type Inh = Env
type Syn = Either Errors Gathered

instance Monoid Syn where
  mempty = Right mempty
  (Left s)  `mappend` (Left r)  = Left (s ++ r)
  (Left s)  `mappend` _         = Left s
  _         `mappend` (Left r)  = Left r
  (Right s) `mappend` (Right r) = Right (s `mappend` r)


type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar)
type TypeRule     = Rx.Rule Integer UTermWithPos Inh Syn

syntaxRuleToScriptRule :: Sy.Rule -> TypeRule
syntaxRuleToScriptRule (Rule rx script) = 
  let vars = getCaptureVars rx
   in ( Regex $ syntaxRegexToScriptRegex rx [] vars
      , \term env synChildren ->
          let (p,thisTy) = ann term
              initialSyn = M.foldr mappend mempty synChildren
              rightSyns  = M.map (\(Right x) -> x) synChildren
              wanted     = syntaxScriptToScript script p thisTy vars rightSyns
           in ( True
              , M.fromList [(n, env) | n <- [0 .. (toEnum $ length vars)]]
              , case initialSyn of
                  Right (Gathered g _ _) ->
                    Right $ Gathered g [wanted] [thisTy]
                  _ -> initialSyn
              ) )

type CaptureVarList = [String]

getCaptureVars :: Sy.RuleRegex -> CaptureVarList
getCaptureVars (Sy.RuleRegex_Capture     s) = [s]
getCaptureVars (Sy.RuleRegex_App     r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (Sy.RuleRegex_Choice  r1 r2) = getCaptureVars r1 `union` getCaptureVars r2
getCaptureVars (Sy.RuleRegex_Iter        b) = runFreshM $ do (_,rx) <- unbind b
                                                             return $ getCaptureVars rx
getCaptureVars _                            = []

syntaxRegexToScriptRegex :: Sy.RuleRegex -> [(RuleRegexVar, c)]
                         -> CaptureVarList -> Regex' c Integer UTermWithPos
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
syntaxRegexToScriptRegex (Sy.RuleRegex_Capture n) _ captureMap =
  (toEnum $ fromJust $ elemIndex n captureMap) <<- any_

syntaxScriptToScript :: RuleScript -> (SourcePos,SourcePos) -> TyVar
                     -> CaptureVarList -> Map Integer Gathered -> TyScript
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
  c where [c] = _wantedC (captures M.! (toEnum $ fromJust $ elemIndex s capVars))

syntaxScriptListToScript :: RuleScriptList -> (SourcePos,SourcePos) -> TyVar
                         -> CaptureVarList -> Map Integer Gathered -> [TyScript]
syntaxScriptListToScript (RuleScriptList_Ref s) _ _ capVars captures =
  _wantedC (captures M.! (toEnum $ fromJust $ elemIndex s capVars))
syntaxScriptListToScript (RuleScriptList_List items) p this capVars captures =
  map (\item -> syntaxScriptToScript item p this capVars captures) items
syntaxScriptListToScript (RuleScriptList_PerItem c info) p this capVars captures =
  map (\t -> Singleton t (Just p, info)) (syntaxConstraintToScript c this capVars captures)

syntaxConstraintToScript :: Constraint -> TyVar -> CaptureVarList -> Map Integer Gathered -> [Constraint]
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

syntaxMonoTypeToScript :: MonoType -> TyVar -> CaptureVarList -> Map Integer Gathered -> [MonoType]
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
    '#':s   -> do tyx <- _ty (captures M.! (toEnum $ fromJust $ elemIndex s capVars))
                  return $ MonoType_Var (translate tyx)
    _       -> return $ MonoType_Var v
syntaxMonoTypeToScript (MonoType_Arrow t1 t2) this capVars captures = do
  ty1 <- syntaxMonoTypeToScript t1 this capVars captures
  ty2 <- syntaxMonoTypeToScript t2 this capVars captures
  return $ MonoType_Arrow ty1 ty2

syntaxPolyTypeToScript :: PolyType -> TyVar -> CaptureVarList -> Map Integer Gathered -> FreshM [PolyType]
syntaxPolyTypeToScript (PolyType_Bind b) this capVars captures = do
  (v,p)  <- unbind b
  inn <- syntaxPolyTypeToScript p this capVars captures
  return $ map (\item -> PolyType_Bind $ bind v item) inn
syntaxPolyTypeToScript (PolyType_Mono cs m) this capVars captures =
  return $ do cs2 <- map (\c -> syntaxConstraintToScript c this capVars captures) cs
              m2  <- syntaxMonoTypeToScript m this capVars captures
              return $ PolyType_Mono cs2 m2
syntaxPolyTypeToScript PolyType_Bottom _ _ _ = return $ return PolyType_Bottom
