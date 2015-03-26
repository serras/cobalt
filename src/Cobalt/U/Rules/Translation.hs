{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.U.Rules.Translation (
  TypeRule
, syntaxRuleToScriptRule
) where

import Control.Applicative
import Control.Lens
import Control.Lens.Extras (is)
import Control.Monad (foldM)
import Control.Monad.State
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
type TranslationInfoEnv = [(TyVar, Gathered)]
type TranslationTypeEnv = [(TyVar, [MonoType])]

type TranslationEnv = ( TranslationInfoEnv, TranslationTypeEnv
                      , (SourcePos,SourcePos), TyVar
                      , [(TyScript, Maybe String)], [Constraint], [TyVar])

_info    :: Lens' TranslationEnv TranslationInfoEnv
_info    = _1
_types   :: Lens' TranslationEnv TranslationTypeEnv
_types   = _2
_pos     :: Lens' TranslationEnv (SourcePos, SourcePos)
_pos     = _3
_this    :: Lens' TranslationEnv TyVar
_this    = _4
_scripts :: Lens' TranslationEnv [(TyScript, Maybe String)]
_scripts = _5
_custom  :: Lens' TranslationEnv [Constraint]
_custom  = _6
_customV :: Lens' TranslationEnv [TyVar]
_customV = _7

(%++) :: MonadState s m => Setting (->) s s [a] [a] -> a -> m ()
xs %++ x = xs %= (++ [x])

-- Translation
syntaxRuleToScriptRule :: [Axiom] -> Rule -> TypeRule
syntaxRuleToScriptRule ax (Rule _ _ i) = runFreshM $ do
  (vars, (rx, check, script)) <- unbind i
  return $ Rx.Rule (Regex $ syntaxRegexToScriptRegex rx [] vars)
                   (\term envAndSat@(Rx.IndexIndependent (_,sat,tchs)) synChildren ->
                     let (p,thisTy)  = ann term
                         childrenMap = syntaxSynToMap vars synChildren
                         rightSyns   = filter (is _Term . snd) childrenMap  -- non-Error info
                         checkW      = syntaxConstraintListToScript check thisTy (syntaxMapToTy rightSyns)
                         wanteds     = syntaxRuleScriptToScript_ rightSyns p thisTy script
                      in ( null check || entails ax sat checkW tchs
                         , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
                         , case foldr (mappend . snd) mempty childrenMap of  -- fold all children
                             GatherTerm g _ _ -> GatherTerm g [term] [wanteds]
                             anError -> anError  -- Float errors upwards
                         ) )

-- Preliminaries
syntaxSynToMap :: CaptureVarList -> Rx.Children WI Syn -> TranslationInfoEnv
syntaxSynToMap tyvars = map (\(Rx.Child (Wrap n) info) ->
  (tyvars !! fromEnum n, fold (unsafeCoerce info :: [Gathered])) )

syntaxMapToTy :: TranslationInfoEnv -> TranslationTypeEnv
syntaxMapToTy = map (\(v, GatherTerm _ exprs _) -> (v, map (var . snd . ann) exprs))

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
syntaxRuleScriptToScript_ :: TranslationInfoEnv -> (SourcePos,SourcePos) -> TyVar
                          -> RuleScript -> FreshM GatherTermInfo
syntaxRuleScriptToScript_ env p this s = do
  -- Execute like an "ordered" element
  finalInfo <- execStateT (syntaxMergerInstrToScript s Nothing (asymMerger p))
                          (env, syntaxMapToTy env, p, this, [], [], [])
  let [(finalScript,_)] = finalInfo ^. _scripts
  return $ GatherTermInfo finalScript
                          (finalInfo ^. _custom)
                          (finalInfo ^. _customV)

syntaxRuleScriptToScript :: RuleScript -> StateT TranslationEnv FreshM ()
syntaxRuleScriptToScript script = do
  (vars, instrs) <- unbind script
  -- Freshen new variables
  freshed <- mapM (fresh . s2n . tail . name2String) vars
  let varsFreshed = zipWith (\v f -> (v, [var f])) vars freshed
  -- Add the new variables to typing environment
  _types   %= (varsFreshed ++)
  _customV %= (union freshed)
  -- Execute script
  mapM_ syntaxInstrToScript instrs
  -- Delete variables which go out of bounds
  _types %= (filter (\(v,_) -> v `notElem` vars))

syntaxInstrToScript :: (RuleScriptInstr, Maybe RuleScriptMessage)
                    -> StateT TranslationEnv FreshM ()
syntaxInstrToScript (RuleScriptInstr_Empty, _) = return ()
syntaxInstrToScript (RuleScriptInstr_Ref v, msg) = do
  constr <- uses _info (lookup v)
  case constr of
    Just (GatherTerm _ _ [i]) -> do
      GatherTermInfo treeThis customThis customVarsThis <- lift i
      _scripts %++ (treeThis, syntaxMessageToScript <$> msg)
      _custom  %=  (union customThis)
      _customV %=  (union customVarsThis)
    Just _   -> fail $ show v ++ " is not a single constraint"
    Nothing  -> fail $ "Cannot find " ++ show v
syntaxInstrToScript (RuleScriptInstr_Constraint r, msg) = do
  c <- syntaxConstraintToScript r <$> use _this <*> use _types
  p <- use _pos
  _scripts %++ (Singleton c (Just p, Nothing), syntaxMessageToScript <$> msg)
syntaxInstrToScript (RuleScriptInstr_Ordered s, msg) = do
  p <- use _pos
  syntaxMergerInstrToScript s msg (asymMerger p)
syntaxInstrToScript (RuleScriptInstr_Merge s, msg) = do
  p <- use _pos
  syntaxMergerInstrToScript s msg $
    \lst -> foldl (mergeScript p) Empty (map fst lst)

syntaxMergerInstrToScript :: RuleScript -> Maybe RuleScriptMessage
                          -> ([(TyScript, Maybe String)] -> TyScript)
                          -> StateT TranslationEnv FreshM ()
syntaxMergerInstrToScript s msg merger = do
  prevScripts <- use _scripts  -- Save old script list
  _scripts .= []               -- Init new script list
  syntaxRuleScriptToScript s   -- Run inner computation
  newScripts <- use _scripts   -- Get inner scripts
  _scripts .= prevScripts ++ [(merger newScripts, syntaxMessageToScript <$> msg)]
                               -- Put back updated old script list

asymMerger :: (SourcePos,SourcePos) -> [(TyScript, Maybe String)] -> TyScript
asymMerger p = foldl (\prev (new,msg) -> Asym new prev (Just p, msg)) Empty

getVarIterator :: [(TyVar,RuleScriptOrdering)] -> TranslationInfoEnv
               -> [[(UTerm ((SourcePos,SourcePos),TyVar), FreshM GatherTermInfo)]]
getVarIterator vars env =
  let varInfos = flip map vars $ \(v, order) -> case lookup v env of
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
