{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.U.Rules.Translation (
  TypeRule
, syntaxRuleToScriptRule
) where

import Control.Applicative
import Control.Lens.Extras (is)
import Control.Monad (foldM)
import Data.Foldable (fold)
import Data.Function (on)
import Data.List (elemIndex, transpose, union, sortBy)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx
import Unbound.LocallyNameless hiding (union, GT)

import Cobalt.Core
import Cobalt.Language
import Cobalt.OutsideIn (entails)
import Cobalt.U.Attributes

import Unsafe.Coerce
-- import Debug.Trace

type WI           = Wrap Integer
type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar)

type CaptureVarList = [TyVar]
type TranslationEnv = [(TyVar, Gathered)]
type TranslationTypeEnv = [(TyVar, [MonoType])]

-- Translation
syntaxRuleToScriptRule :: [Axiom] -> Rule -> TypeRule
syntaxRuleToScriptRule ax (Rule _ _ i) = runFreshM $ do
  (vars, (rx, check, script)) <- unbind i
  return $ Rx.Rule (Regex $ syntaxRegexToScriptRegex rx [] vars)
                   (\term envAndSat@(Rx.IndexIndependent (_,sat,tchs)) synChildren ->
                     let (p,thisTy)  = ann term
                         childrenMap = syntaxSynToMap vars synChildren
                         initialSyn  = foldr (mappend . snd) mempty childrenMap
                         rightSyns   = filter (is _Term . snd) childrenMap
                         initialTy   = map (\(v, GatherTerm _ exprs _) -> (v, map (var . snd . ann) exprs)) rightSyns
                         checkW      = syntaxConstraintListToScript check thisTy initialTy
                         wanteds     = (\(x,_,_) -> x) <$> syntaxBindScriptToScript p thisTy rightSyns initialTy (mergeFnAsym p) const script
                      in ( null check || entails ax sat checkW tchs
                         , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
                         , case initialSyn of
                             GatherTerm g _ _ -> GatherTerm g [term] [wanteds]
                             _ -> initialSyn  -- Float errors upwards
                         ) )

syntaxSynToMap :: CaptureVarList -> Rx.Children WI Syn -> TranslationEnv
syntaxSynToMap tyvars = map (\(Rx.Child (Wrap n) info) ->
  (tyvars !! fromEnum n, fold (unsafeCoerce info :: [Gathered])) )

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
syntaxBindScriptToScript :: (Rep a, Alpha a, Rep b, Alpha b)
                         => (SourcePos,SourcePos) -> TyVar -> TranslationEnv -> TranslationTypeEnv
                         -> ([(TyScript, a)] -> TyScript)     -- how to merge everything together
                         -> (b -> TranslationTypeEnv -> b)    -- how to change the next step
                         -> RuleScript a b -> FreshM (GatherTermInfo, b, TranslationTypeEnv)
syntaxBindScriptToScript p thisTy env tyEnv mergeFn nextFn script = do
  (vars, (instrs, next)) <- unbind script
  -- Add fresh variables
  freshedTyVars <- mapM (fresh . s2n . drop 1 . name2String) vars
  let startEnv = zipWith (\a b -> (a,[var b])) vars freshedTyVars ++ tyEnv
  -- Call over each instruction and merge
  (finalEnv, instrScripts) <-
    foldM (\(currentTyEnv, scriptList) (instr, msg) -> do
              (GatherTermInfo s c cv, newEnv) <- syntaxScriptTreeToScript p thisTy env currentTyEnv instr
              return (newEnv, scriptList ++ [((s,msg), c, cv)]))
          (startEnv, []) instrs
  let (allSMsg, allCustom, allCustomVars) = unzip3 instrScripts
  return ( GatherTermInfo (mergeFn allSMsg)
                          (concat allCustom)
                          (freshedTyVars `union` concat allCustomVars)
         , nextFn next finalEnv
         , finalEnv )

mergeFnMerge :: (SourcePos, SourcePos) -> [(TyScript, ())] -> TyScript
mergeFnMerge p = foldl (mergeScript p) Empty . map fst

mergeFnAsym :: (SourcePos, SourcePos) -> [(TyScript, Maybe RuleScriptMessage)] -> TyScript
mergeFnAsym _ [] = Empty
mergeFnAsym _ [(x,m)] = replaceMsg m x
mergeFnAsym p ((x,m):xs) = foldl (\prev (scr, msg) -> Asym scr prev (Just p, syntaxMessageToScript <$> msg))
                                 (replaceMsg m x) xs

mergeAllScripts :: (SourcePos,SourcePos) -> [GatherTermInfo] -> GatherTermInfo
mergeAllScripts p = foldl (\(GatherTermInfo ss cs cvs) (GatherTermInfo s c cv) ->
                              GatherTermInfo (mergeScript p s ss) (c ++ cs) (cv `union` cvs))
                          (GatherTermInfo Empty [] [])

mergeAllScriptsAsym :: (SourcePos,SourcePos) -> [(GatherTermInfo, Maybe RuleScriptMessage)] -> GatherTermInfo
mergeAllScriptsAsym p = foldl (\(GatherTermInfo ss cs cvs) (GatherTermInfo s c cv, msg) ->
                                  GatherTermInfo (Asym s ss (Just p, syntaxMessageToScript <$> msg)) (c ++ cs) (cv `union` cvs))
                              (GatherTermInfo Empty [] [])

replaceMsg :: Maybe RuleScriptMessage -> TyScript -> TyScript
replaceMsg msg (Singleton c (p, _)) = Singleton c (p, syntaxMessageToScript <$> msg)
replaceMsg msg (Merge ss (p, _))    = Merge ss (p, syntaxMessageToScript <$> msg)
replaceMsg msg (Asym s1 s2 (p, _))  = Asym s1 s2 (p, syntaxMessageToScript <$> msg)
replaceMsg _   s                    = s

syntaxScriptTreeToScript :: (SourcePos,SourcePos) -> TyVar -> TranslationEnv -> TranslationTypeEnv
                         -> RuleScriptTree -> FreshM (GatherTermInfo, TranslationTypeEnv)
syntaxScriptTreeToScript _ _ _ tys RuleScriptTree_Empty =
   return (GatherTermInfo Empty [] [], tys)
syntaxScriptTreeToScript _p _this env tys (RuleScriptTree_Ref v) =
  case lookup v env of
    Just (GatherTerm _ _ [g]) -> do { g' <- g; return (g',tys) }
    _  -> error "This should never happen, we reference a not existing variable"
syntaxScriptTreeToScript p this _env tys (RuleScriptTree_Constraint c) =
  return ( GatherTermInfo (Singleton (syntaxConstraintToScript c this tys)
                          (Just p, Nothing)) [] []
         , tys )
syntaxScriptTreeToScript p this env tys (RuleScriptTree_Merge vars loop) = do
  let iterOver = zipVarInformation vars env
  (newTyEnv,scripts) <- syntaxScriptTreeIter p this env tys (mergeFnMerge p) {- ! -} const const loop iterOver
  return (mergeAllScripts p (map fst scripts), newTyEnv)
syntaxScriptTreeToScript p this env tys (RuleScriptTree_Asym vars loop) = do
  let iterOver = zipVarInformation vars env
  (newTyEnv,scripts) <- syntaxScriptTreeIter p this env tys (mergeFnAsym p) {- ! -} const const loop iterOver
  return (mergeAllScripts p (map fst scripts), newTyEnv)
syntaxScriptTreeToScript p this env tys (RuleScriptTree_Fold vars accVar initial loop) = do
  let iterOver   = zipVarInformation vars env
      initTy     = syntaxMonoTypeToScript initial this tys
      nextTyFn   = \nextType currentTyEnv -> syntaxMonoTypeToScript nextType this currentTyEnv
      replaceVar = \currentTyEnv nextType -> (accVar,[nextType]) : filter (\(v,_) -> v /= accVar) currentTyEnv
  (finalEnv, scripts) <- syntaxScriptTreeIter p this env ((accVar,[initTy]):tys)
                                              (mergeFnMerge p) nextTyFn replaceVar loop iterOver
  return (mergeAllScripts p (map fst scripts), finalEnv)
syntaxScriptTreeToScript p this env tys (RuleScriptTree_AFold vars accVar initial loop) = do
  let iterOver   = zipVarInformation vars env
      initTy     = syntaxMonoTypeToScript initial this tys
      nextTyFn   = \(nextType, msg) currentTyEnv -> (syntaxMonoTypeToScript nextType this currentTyEnv, msg)
      replaceVar = \currentTyEnv (nextType,_) -> (accVar,[nextType]) : filter (\(v,_) -> v /= accVar) currentTyEnv
  (finalEnv, scripts) <- syntaxScriptTreeIter p this env ((accVar,[initTy]):tys)
                                              (mergeFnMerge p) nextTyFn replaceVar loop iterOver
  let finalScripts = map (\(s, (_, m)) -> (s, m)) scripts
  return (mergeAllScriptsAsym p finalScripts, finalEnv)

zipVarInformation :: [(TyVar,RuleScriptOrdering)] -> TranslationEnv
                  -> [[(UTerm ((SourcePos,SourcePos),TyVar), FreshM GatherTermInfo)]]
zipVarInformation [] _ = [[]] -- iterate once
zipVarInformation vars env =
  let varInfos = flip map vars $ \(v, order) ->
                   case lookup v env of
                     Just (GatherTerm _ terms gs) -> sortBy (orderSourcePos order `on` (fst . ann . fst) ) (zip terms gs)
                     Nothing -> []
                     _       -> error ("This should never happen, we are zipping " ++ show v ++ " incorrectly")
      minLength = minimum (map length varInfos)
   in transpose $ map (take minLength) varInfos

orderSourcePos :: RuleScriptOrdering -> (SourcePos,SourcePos) -> (SourcePos,SourcePos) -> Ordering
orderSourcePos _ (xi,xe) (yi,ye) | xi < yi, xe < ye = LT
                                 | yi < xi, ye < xe = GT
orderSourcePos RuleScriptOrdering_OutToIn (xi,xe) (yi,ye) | xi < yi || ye < xe = LT
                                                          | yi < xi || xe < ye = GT
orderSourcePos RuleScriptOrdering_InToOut (xi,xe) (yi,ye) | xi < yi || ye < xe = GT
                                                          | yi < xi || xe < ye = LT
orderSourcePos _ _ _ = EQ

syntaxScriptTreeIter :: (Rep a, Alpha a, Rep b, Alpha b)
                     => (SourcePos,SourcePos) -> TyVar -> TranslationEnv -> TranslationTypeEnv
                     -> ([(TyScript, a)] -> TyScript)
                     -> (b -> TranslationTypeEnv -> b)
                     -> (TranslationTypeEnv -> b -> TranslationTypeEnv)
                     -> (Bind [TyVar] (RuleScript a b))
                     -> [[(UTerm ((SourcePos,SourcePos),TyVar), FreshM GatherTermInfo)]]
                     -> FreshM (TranslationTypeEnv, [(GatherTermInfo, b)])
syntaxScriptTreeIter p this env tys mergeFn nextFn stepFn loop vars =
  (\(finalTy, finalLst) -> (finalTy, reverse finalLst)) <$>
  foldM (\(thisTyEnv, looplst) loopitem -> do
    (loopvars, loopbody) <- unbind loop
    let extraEnv = zipWith (\loopvar (term, ginfo) -> (loopvar, GatherTerm [] [term] [ginfo])) loopvars loopitem
        extraTy  = map (\(v, GatherTerm _ exprs _) -> (v, map (var . snd . ann) exprs)) extraEnv
    (loopelt, nextStep, nextTyEnv) <- syntaxBindScriptToScript p this (extraEnv ++ env) (extraTy ++ thisTyEnv)
                                                               mergeFn nextFn loopbody
    let newTys = stepFn (filter (\(v,_) -> v `notElem` loopvars) nextTyEnv) nextStep
    return (newTys, (loopelt, nextStep):looplst))
    (tys,[]) vars

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
    '#':_   -> case lookup v captures of
                 Nothing  -> error $ (show v) ++ " does not contain any type"
                 Just [m] -> m
                 Just _   -> error $ (show v) ++ " has multiple types, whereas only one is expected"
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
