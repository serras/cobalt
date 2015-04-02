{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.U.Rules.Translation (
  TypeRule
, syntaxRuleToScriptRule
) where

import Control.Applicative
import Control.Lens
import Control.Lens.Extras (is)
import Control.Monad.State
import Data.Foldable (fold, foldMap)
import Data.Function (on)
import Data.List (elemIndex, union, sortBy)
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

newtype TranslationEnv = TranslationEnv
                           ( TranslationInfoEnv, TranslationTypeEnv
                           , (SourcePos,SourcePos), TyVar
                           , [(TyScript, Maybe String)], [Constraint], [TyVar]
                           , Maybe (Gathered -> StateT TranslationEnv FreshM ()) )

_tenv    :: Iso' TranslationEnv
                  ( TranslationInfoEnv, TranslationTypeEnv
                  , (SourcePos,SourcePos), TyVar
                  , [(TyScript, Maybe String)], [Constraint], [TyVar]
                  , Maybe (Gathered -> StateT TranslationEnv FreshM ()) )
_tenv    = iso (\(TranslationEnv v) -> v) TranslationEnv
_info    :: Lens' TranslationEnv TranslationInfoEnv
_info    = _tenv . _1
_types   :: Lens' TranslationEnv TranslationTypeEnv
_types   = _tenv . _2
_pos     :: Lens' TranslationEnv (SourcePos, SourcePos)
_pos     = _tenv . _3
_this    :: Lens' TranslationEnv TyVar
_this    = _tenv . _4
_scripts :: Lens' TranslationEnv [(TyScript, Maybe String)]
_scripts = _tenv . _5
_custom  :: Lens' TranslationEnv [Constraint]
_custom  = _tenv . _6
_customV :: Lens' TranslationEnv [TyVar]
_customV = _tenv . _7
_cont    :: Lens' TranslationEnv (Maybe (Gathered -> StateT TranslationEnv FreshM ()))
_cont    = _tenv . _8

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
                         , [ Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
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
  finalInfo <- execStateT (syntaxMergerInstrToScript s Nothing (asymMerger AsymJoin p))
                          (TranslationEnv (env, syntaxMapToTy env, p, this, [], [], [], Nothing))
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
  oldTypes <- use _types
  _types   %= (varsFreshed ++)
  _customV %= (union freshed)
  -- Execute script
  mapM_ syntaxInstrToScript instrs
  -- Revert to previous state
  _types .= oldTypes

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
syntaxInstrToScript (RuleScriptInstr_Constraint r expl, msg) = do
  c <- syntaxConstraintToScript r <$> use _this <*> use _types
  p <- use _pos
  _scripts %++ ( Singleton c p (syntaxMessageToScript <$> expl)
               , syntaxMessageToScript <$> msg )
syntaxInstrToScript (RuleScriptInstr_Ordered s, msg) = do
  p <- use _pos
  syntaxMergerInstrToScript s msg (asymMerger AsymJoin p)
syntaxInstrToScript (RuleScriptInstr_Sequence s, msg) = do
  p <- use _pos
  syntaxMergerInstrToScript s msg (asymMerger Sequence p)
syntaxInstrToScript (RuleScriptInstr_Join s, msg) = do
  p <- use _pos
  syntaxMergerInstrToScript s msg (\xs -> Join (map fst xs) p)
syntaxInstrToScript (RuleScriptInstr_Match v cases, _) = do
  constr <- uses _info (lookup v)
  case constr of
    Just (GatherTerm _ [expr] _) -> syntaxInstrToScriptMatch expr cases
    Just _   -> fail $ show v ++ " is not a single constraint"
    Nothing  -> fail $ "Cannot find " ++ show v
{-
syntaxInstrToScript (RuleScriptInstr_Update v m, _msg) = do
  newMono <- syntaxMonoTypeToScript m <$> use _this <*> use _types
  -- Remove previous incarnations
  _info  %= (filter (\(k,_) -> v /= k))
  _types %= (filter (\(k,_) -> v /= k))
  -- Add new type
  _types %= ((v, [newMono]) :)
-}
syntaxInstrToScript (RuleScriptInstr_ForEach oneVar loop, _msg) = do
  oChildren <- orderedChildren oneVar <$> use _info
  syntaxInstrToScriptIter loop oChildren
syntaxInstrToScript (RuleScriptInstr_Iter v s, _msg) = do
  oldCont <- use _cont
  _cont .= Just (\g -> do -- Compute new variables
                          oldInfo <- use _info
                          oldTys  <- use _types
                          let newInfo = (v,g) : filter (\(w,_) -> w /= v) oldInfo
                              newTys  = syntaxMapToTy [(v,g)] ++ filter (\(w,_) -> w /= v) oldTys
                          _info  .= newInfo
                          _types .= newTys
                          -- Call the continuation
                          syntaxRuleScriptToScript s
                          -- Put everything back in place
                          _info  .= oldInfo
                          _types .= oldTys)
  syntaxRuleScriptToScript s  -- Run with continuation
  _cont .= oldCont
syntaxInstrToScript (RuleScriptInstr_Continue v, _msg) = do
  cont <- use _cont
  case cont of
    Nothing -> fail "continue without iter"
    Just c  -> do info <- uses _info (lookup v)
                  case info of
                    Nothing -> fail $ "Cannot find " ++ show v
                    Just g  -> c g

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

syntaxInstrToScriptIter :: Bind TyVar RuleScript -> [Gathered]
                        -> StateT TranslationEnv FreshM ()
syntaxInstrToScriptIter _ [] = return ()
syntaxInstrToScriptIter loopbody (itervar:rest) = do
  (loopvar, body) <- unbind loopbody
  let newInfo = [(loopvar, itervar)]
      newTys  = syntaxMapToTy newInfo
  _customV %= (union [loopvar])
  -- Add new variables
  oldInfo  <- use _info
  oldTypes <- use _types
  _info  %= (newInfo ++)
  _types %= (newTys ++)
  -- Run the inner loop
  syntaxRuleScriptToScript body
  -- Revert to previous state
  _info  .= oldInfo
  _types .= oldTypes
  -- And do the rest
  syntaxInstrToScriptIter loopbody rest

syntaxInstrToScriptMatch :: UTerm ((SourcePos,SourcePos),TyVar) -> [RuleBody]
                         -> StateT TranslationEnv FreshM ()
syntaxInstrToScriptMatch _ [] = return ()
syntaxInstrToScriptMatch expr (c:rest) = do
  (vars, (rx, _, script)) <- unbind c
  oldInfo <- use _info
  oldTys  <- use _types
  case match (Regex $ syntaxRegexToScriptRegex rx [] vars) expr of
    Nothing -> syntaxInstrToScriptMatch expr rest
    Just cg -> do let newInfos = zipWith (\n v -> case lookupGroup (Wrap n) cg of
                                                    Nothing -> (v, mempty)
                                                    Just (elts :: [UTerm ((SourcePos,SourcePos),TyVar)])
                                                      -> (v, foldMap (getInfo oldInfo . snd . ann) elts))
                                         [0 ..] vars
                      newTys   = syntaxMapToTy newInfos
                  -- Add new information
                  _info  %= (newInfos ++)
                  _types %= (newTys ++)
                  syntaxRuleScriptToScript script
                  -- Get back to old
                  _info  .= oldInfo
                  _types .= oldTys

getInfo :: TranslationInfoEnv -> TyVar -> Gathered
getInfo [] _ = error "Variable not found"
getInfo ((_, GatherTerm _ terms infos) : rst) vr =
  case searchInfo terms infos of
    Nothing -> getInfo rst vr
    Just (term,info) -> GatherTerm [] [term] [info]
  where searchInfo []     _      = Nothing
        searchInfo _      []     = Nothing
        searchInfo (t:ts) (i:rs) = if vr == snd (ann t)
                                   then Just (t, i)
                                   else searchInfo ts rs
getInfo (_ : _) _ = error "This should never happen, a non-GatherTerm variable"


-- For ASYMJOIN and SEQUENCE
asymMerger :: (TyScript -> TyScript -> (SourcePos,SourcePos) -> TyScript)
           -> (SourcePos,SourcePos) -> [(TyScript, Maybe String)] -> TyScript
asymMerger asym p =
  foldl (\prev (new,msg) ->
            let scr = asym prev new p in case msg of
              Nothing   -> scr
              Just msg' -> Label msg' scr)
        Empty

-- For FOREACH
-- Get children ordered by its position -- ugly code, don't look much at it
orderedChildren :: (TyVar,RuleScriptOrdering) -> TranslationInfoEnv -> [Gathered]
orderedChildren (v, order) env = case lookup v env of
  Just (GatherTerm _ terms gs) -> let search = sortBy (orderSourcePos order `on` (fst . ann . fst) ) (zip terms gs)
                                   in map (\(x,y) -> GatherTerm [] [x] [y]) search
  Nothing -> []
  _       -> error ("This should never happen, we are zipping " ++ show v ++ " incorrectly")

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
-- syntaxMessageToScript _                             = error "Only literals are supported"
