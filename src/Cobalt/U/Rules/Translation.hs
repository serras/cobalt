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
import Control.Monad.State
import Data.Foldable (fold)
import Data.Function
import Data.List (elemIndex, union, transpose, sortBy)
import Data.Maybe (fromJust, fromMaybe, catMaybes)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx
import Unbound.LocallyNameless hiding (union, GT)

import Cobalt.Core
import Cobalt.Language
import Cobalt.OutsideIn (entails)
import Cobalt.U.Attributes

import Unsafe.Coerce

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
                         wanteds     = undefined
                      in ( null check || entails ax sat checkW tchs
                         , [Rx.Child (Wrap n) [envAndSat] | n <- [0 .. (toEnum $ length vars)]]
                         , case initialSyn of
                             GatherTerm g _ _ -> GatherTerm g [term] [wanteds]
                             _ -> initialSyn  -- Float errors upwards
                         ) )

syntaxSynToMap :: CaptureVarList -> Rx.Children WI Syn -> [(TyVar, Gathered)]
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
syntaxBindScriptToScript :: (Rep a, Alpha a)
                         => (SourcePos,SourcePos) -> TyVar -> TranslationEnv
                         -> (TyScript -> a -> TyScript)  -- what to do with msg
                         -> ([TyScript] -> TyScript)     -- how to merge everything together
                         -> RuleScript a -> FreshM GatherTermInfo
syntaxBindScriptToScript p thisTy env msgFn mergeFn script = do
  (vars, instrs) <- unbind script
  instrScripts <- mapM (\(instr, msg) -> do GatherTermInfo s custom customVars <- syntaxScriptTreeToScript p thisTy env instr
                                            return $ ((s, msg), custom, customVars)) instrs
  let (allSMsg, allCustom, allCustomVars) = unzip3 instrScripts
  return $ GatherTermInfo (mergeFn (map (uncurry msgFn) allSMsg)) (concat allCustom) (concat allCustomVars)


syntaxScriptTreeToScript :: (SourcePos,SourcePos) -> TyVar -> TranslationEnv
                         -> RuleScriptTree -> FreshM GatherTermInfo
syntaxScriptTreeToScript = undefined

{-
-- Translation of "script" block
type TranslationEnv = ( (SourcePos, SourcePos)
                      , TyVar         -- #this
                      , TranslationTypeEnv
                      , TranslationExprEnv
                      , TranslationConsEnv
                      , [TyScript]     -- the stack
                      , [Constraint]   -- extra custom
                      , [TyVar] )      -- customVars

syntaxBindScriptToScript :: RuleScript -> StateT TranslationEnv FreshM GatherTermInfo
syntaxBindScriptToScript script = do
  syntaxBindScriptToScript' script
  p <- use _1
  tree_ <- use _6
  custom_ <- use _7
  customVars_ <- use _8
  case tree_ of
    []  -> fail "Empty stack at the end"
    [s] -> return $ GatherTermInfo s custom_ customVars_
    _   -> return $ GatherTermInfo (Merge tree_ (Just p, Nothing)) custom_ customVars_

-- After this is executed, local variables are deleted
syntaxBindScriptToScript' :: RuleScript -> StateT TranslationEnv FreshM ()
syntaxBindScriptToScript' script = do
  (vars, statements) <- unbind script
  freshed <- mapM (fresh . s2n . tail . name2String) vars
  let varsFreshed = zipWith (\v f -> (v, [var f])) vars freshed
  _3 %= (varsFreshed ++)
  _8 %= (union freshed)
  syntaxBindStatementsToScript statements
  _3 %= (filter (\(v,_) -> v `notElem` vars))

syntaxBindStatementsToScript :: [RuleScriptStatement] -> StateT TranslationEnv FreshM ()
syntaxBindStatementsToScript [] = return ()
syntaxBindStatementsToScript (RuleScriptStatement_Empty : rest) = do
  _6 %= (Empty :)
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_Ref v : rest) = do
  constr <- uses _5 (lookup v)
  case constr of
    Just [i] -> do GatherTermInfo treeThis customThis customVarsThis <- lift i
                   _6 %= (treeThis :)
                   _7 %= (union customThis)
                   _8 %= (union customVarsThis)
                   syntaxBindStatementsToScript rest
    Just _   -> fail $ show v ++ " is not a single constraint"
    Nothing  -> fail $ "Cannot find " ++ show v
syntaxBindStatementsToScript (RuleScriptStatement_Constraint r msg : rest) = do
  p     <- use _1
  this  <- use _2
  tyEnv <- use _3
  let c = syntaxConstraintToScript r this tyEnv
  _6 %= (Singleton c (Just p, syntaxMessageToScript <$> msg) :)
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_Merge howMany msg : rest) = do
  p     <- use _1
  stack <- use _6
  let toTake = fromMaybe (length stack) howMany
  _6 .= Merge (take toTake stack) (Just p, syntaxMessageToScript <$> msg) : drop toTake stack
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_MergeBlameLast howMany howManyToBlame msg : rest) = do
  p     <- use _1
  stack <- use _6
  let toTake = fromMaybe (length stack) howMany
      firstN = take toTake stack
      upper  = take howManyToBlame firstN
      lower  = drop howManyToBlame firstN
      asym1  = case upper of { [x] -> x ; _ -> Merge upper (Just p, Nothing) }
      asym2  = case lower of { [x] -> x ; _ -> Merge lower (Just p, Nothing) }
  _6 .= Asym asym1 asym2 (Just p, syntaxMessageToScript <$> msg) : drop toTake stack
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_Update v m : rest) = do
  this  <- use _2
  tyEnv <- use _3
  let m_ = syntaxMonoTypeToScript m this tyEnv
  _3 %= replaceElt v [m_]
  _4 %= filter (\(k,_) -> k /= v)
  _5 %= filter (\(k,_) -> k /= v)
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_LocalStack s : rest) = do
  p <- use _1
  previousStack <- use _6
  _6 .= []  -- new stack
  syntaxBindScriptToScript' s
  -- merge everything in the new stack
  left     <- use _6
  stackTop <- case left of
    []  -> fail "Empty stack at the end"
    [l] -> return l
    _   -> return (Merge left (Just p, Nothing))
  -- take the previous stack back
  _6 .= stackTop : previousStack
  syntaxBindStatementsToScript rest
syntaxBindStatementsToScript (RuleScriptStatement_ForEach vars loop : rest) = do
  -- Compute the lists to iterate over
  tyEnv <- use _3
  exEnv <- use _4
  coEnv <- use _5
  let typeThings = map (fromMaybe [] . flip lookup tyEnv) vars
      smallestLength = minimum (map length typeThings)
      exprThings = map (maybe (replicate smallestLength Nothing) (map Just) . flip lookup exEnv) vars
      consThings = map (maybe (replicate smallestLength Nothing) (map Just) . flip lookup coEnv) vars
      iterateOver = take smallestLength $ transpose typeThings
  -- Unbind inner loop
  (innervars, innerloop) <- lift $ unbind loop
  -- Run over each element
  syntaxBindStatementsToScriptForEach innervars innerloop iterateOver (transpose exprThings) (transpose consThings)
  syntaxBindStatementsToScript rest

syntaxBindStatementsToScriptForEach :: [TyVar] -> RuleScript
                                    -> [[MonoType]] -> [[Maybe (UTerm ((SourcePos,SourcePos),TyVar))]]
                                    -> [[Maybe (FreshM GatherTermInfo)]] -> StateT TranslationEnv FreshM ()
syntaxBindStatementsToScriptForEach _ _ [] _ _ = return ()
syntaxBindStatementsToScriptForEach vars loop (m : ms) (e : es) (c : cs) = do
  _3 %= (zipWith (\v m_ -> (v, [m_])) vars m ++)
  _4 %= (catMaybes (zipWith (\v e_ -> maybe Nothing (\e__ -> Just (v, [e__])) e_) vars e) ++)
  _5 %= (catMaybes (zipWith (\v c_ -> maybe Nothing (\c__ -> Just (v, [c__])) c_) vars c) ++)
  syntaxBindScriptToScript' loop
  _3 %= (filter (\(v,_) -> v `notElem` vars))
  _4 %= (filter (\(v,_) -> v `notElem` vars))
  _5 %= (filter (\(v,_) -> v `notElem` vars))
  syntaxBindStatementsToScriptForEach vars loop ms es cs
syntaxBindStatementsToScriptForEach _ _ (_:_) _ _ = error "This should never happen"

replaceElt :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
replaceElt _  _  [] = []
replaceElt x1 v1 ((x2, v2) : rs) | x1 == x2  = (x1, v1) : rs
                                 | otherwise = (x2, v2) : replaceElt x1 v1 rs
-}

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
