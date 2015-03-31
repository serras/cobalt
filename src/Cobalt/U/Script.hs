{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances #-}
module Cobalt.U.Script (
  Script(..)
, TyScript
, TyScriptInfo
, toConstraintList
, toConstraintList'
, fvScript
, substScript
, substsScript
, simplifyScript
, removeExistsScript
) where

import Data.List (intercalate, union, (\\))
import Data.Monoid
import Unbound.LocallyNameless (fv, subst, substs)

import Cobalt.Core
import Cobalt.Language (SourcePos)

data Script var constraint info
  = Empty
  | Label     info (Script var constraint info)
  | Singleton constraint
  | Join      [Script var constraint info]
  | AsymJoin  (Script var constraint info) (Script var constraint info)
  | Sequence  (Script var constraint info) (Script var constraint info)
  | Exists    [var] [constraint] (Script var constraint info)

type TyScriptInfo = (Maybe (SourcePos,SourcePos), Maybe String)
type TyScript = Script TyVar Constraint TyScriptInfo

toConstraintList :: ([var] -> [constraint] -> [constraint] -> constraint)  -- Exists
                 -> Script var constraint msg  -- Script
                 -> [constraint]
toConstraintList _ex Empty            = []
toConstraintList ex  (Label _ s)      = toConstraintList ex s
toConstraintList _ex (Singleton c)    = [c]
toConstraintList ex  (Join ss)        = concatMap (toConstraintList ex) ss
toConstraintList ex  (AsymJoin s1 s2) = toConstraintList ex s1 ++ toConstraintList ex s2
toConstraintList ex  (Sequence s1 s2) = toConstraintList ex s1 ++ toConstraintList ex s2
toConstraintList ex  (Exists v q s)   = [ex v q (toConstraintList ex s)]

toConstraintList' :: Script var constraint msg -> [constraint]
toConstraintList' Empty            = []
toConstraintList' (Label _ s)      = toConstraintList' s
toConstraintList' (Singleton c)    = [c]
toConstraintList' (Join ss)        = concatMap toConstraintList' ss
toConstraintList' (AsymJoin s1 s2) = toConstraintList' s1 ++ toConstraintList' s2
toConstraintList' (Sequence s1 s2) = toConstraintList' s1 ++ toConstraintList' s2
toConstraintList' (Exists _ _ _)   = []

fvScript :: TyScript -> [TyVar]
fvScript Empty            = []
fvScript (Label _ s)      = fvScript s
fvScript (Singleton c)    = fv c
fvScript (Join lst)       = foldr union [] (map fvScript lst)
fvScript (AsymJoin c1 c2) = fvScript c1 `union` fvScript c2
fvScript (Sequence c1 c2) = fvScript c1 `union` fvScript c2
fvScript (Exists v _ s)   = fvScript s \\ v

substScript :: TyVar -> MonoType -> TyScript -> TyScript
substScript _ _ Empty            = Empty
substScript v m (Label i s)      = Label i (substScript v m s)
substScript v m (Singleton c)    = Singleton (subst v m c)
substScript v m (Join ss)        = Join (map (substScript v m) ss)
substScript v m (AsymJoin c1 c2) = AsymJoin (substScript v m c1) (substScript v m c2)
substScript v m (Sequence c1 c2) = Sequence (substScript v m c1) (substScript v m c2)
substScript v m (Exists vs q w)  = Exists vs (map (subst v m) q) (substScript v m w)

substsScript :: [(TyVar, MonoType)] -> TyScript -> TyScript
substsScript _ Empty            = Empty
substsScript v (Label i s)      = Label i (substsScript v s)
substsScript v (Singleton c)    = Singleton (substs v c)
substsScript v (Join ss)        = Join (map (substsScript v) ss)
substsScript v (AsymJoin c1 c2) = AsymJoin (substsScript v c1) (substsScript v c2)
substsScript v (Sequence c1 c2) = Sequence (substsScript v c1) (substsScript v c2)
substsScript v (Exists vs q w)  = Exists vs (map (substs v) q) (substsScript v w)

instance Monoid TyScript where
  mempty = Empty
  mappend s Empty = s
  mappend Empty s = s
  mappend (Join ss) s@(Singleton _) = Join (s:ss)
  mappend s@(Singleton _) (Join ss) = Join (s:ss)
  mappend s1 s2 = Join [s1,s2]

instance Show TyScript where
  show Empty              = ""
  show (Label (_,msg) cs) = "label" ++ showMsg msg ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show cs)))
  show (Singleton c)      = show c
  show (Join cs)          = "join\n" ++ intercalate "\n" (map (\c -> intercalate "\n" (map ("  " ++) (lines (show c)))) cs)
  show (AsymJoin c1 c2)   = "asymjoin\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                                 ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Sequence c1 c2)   = "sequence\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                                 ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Exists _vs _cs _s)   = "exists"

showMsg :: Maybe String -> String
showMsg (Just m) = " => " ++ m
showMsg Nothing  = ""

simplifyScript :: Monoid info => Script var constraint info -> Script var constraint info
simplifyScript Empty            = Empty
simplifyScript s@(Singleton _)  = s
simplifyScript (Label i s)      = Label i (simplifyScript s)
simplifyScript (Join ss)        = case filter notEmpty $ map simplifyScript ss of
                                    []  -> Empty
                                    [m] -> m
                                    ms  -> Join ms
                                  where notEmpty Empty = False
                                        notEmpty _     = True
simplifyScript (AsymJoin c1 c2) = let s1 = simplifyScript c1
                                      s2 = simplifyScript c2
                                   in case (s1, s2) of
                                        (Empty, _) -> s2
                                        (_, Empty) -> s1
                                        _          -> AsymJoin s1 s2
simplifyScript (Sequence c1 c2) = let s1 = simplifyScript c1
                                      s2 = simplifyScript c2
                                   in case (s1, s2) of
                                        (Empty, _) -> s2
                                        (_, Empty) -> s1
                                        _          -> Sequence s1 s2
simplifyScript (Exists v q s)    = Exists v q (simplifyScript s)

removeExistsScript :: TyScript -> (TyScript, [Constraint], [TyVar])
removeExistsScript Empty = (Empty, [], [])
removeExistsScript (Label i s) =
  let (s', r, v) = removeExistsScript s
   in (Label i s', r, v)
removeExistsScript s@(Singleton _) = (s, [], [])
removeExistsScript (Join ss) =
  let (remSs, rest, vars) = unzip3 (map removeExistsScript ss)
   in (Join remSs, foldr union [] rest, foldr union [] vars)
removeExistsScript (AsymJoin c1 c2) =
  let (s1, r1, v1) = removeExistsScript c1
      (s2, r2, v2) = removeExistsScript c2
   in (AsymJoin s1 s2, r1 ++ r2, union v1 v2)
removeExistsScript (Sequence c1 c2) =
  let (s1, r1, v1) = removeExistsScript c1
      (s2, r2, v2) = removeExistsScript c2
   in (Sequence s1 s2, r1 ++ r2, union v1 v2)
removeExistsScript (Exists v q s) =
  let q1 = cleanTrivialConstraints q in
  case v \\ (fv q ++ fvScript s) of  -- Find not needed vars
    [] -> case applyPossibleSubsts v q1 s of
            Just (q2, s2) -> removeExistsScript (Exists v q2 s2)
            Nothing -> -- We have finished
              case removeExistsScript s of
                (sR, [], []) -> -- Check whether q1 can be flowed upwards
                  case (fv q1 `union` fvScript sR) \\ v of
                    [] -> -- They can, all variables are inside
                          (sR, q1, v)
                    _  -> (Exists v q1 sR, [], [])
                (sR, moreQ, moreV) -> removeExistsScript (Exists (union v moreV) (union q1 moreQ) sR)
    notNeededVars -> removeExistsScript (Exists (v \\ notNeededVars) q1 s)

applyPossibleSubsts :: [TyVar] -> [Constraint] -> TyScript -> Maybe ([Constraint], TyScript)
applyPossibleSubsts = applyPossibleSubsts_ []
  where applyPossibleSubsts_ _   _    []                       _  = Nothing
        applyPossibleSubsts_ acc vars (c@(Constraint_Unify m1 m2) : rest) ss
          | MonoType_Var v1 <- m1, v1 `elem` vars = Just (reverse acc ++ rest, substScript v1 m2 ss)
          | MonoType_Var v2 <- m2, v2 `elem` vars = Just (reverse acc ++ rest, substScript v2 m1 ss)
          | otherwise = applyPossibleSubsts_ (c : acc) vars rest ss
        applyPossibleSubsts_ acc vars (c : rest) ss = applyPossibleSubsts_ (c : acc) vars rest ss

cleanTrivialConstraints :: [Constraint] -> [Constraint]
cleanTrivialConstraints [] = []
cleanTrivialConstraints (Constraint_Unify t1 t2 : rest) | t1 == t2 = cleanTrivialConstraints rest
cleanTrivialConstraints (Constraint_Inst _ PolyType_Bottom : rest) = cleanTrivialConstraints rest
cleanTrivialConstraints (Constraint_Equal t1 (PolyType_Mono [] t2) : rest)
  | t1 == t2  = cleanTrivialConstraints rest
  | otherwise = Constraint_Unify t1 t2 : cleanTrivialConstraints rest
cleanTrivialConstraints (Constraint_Inst t1 (PolyType_Mono [] t2) : rest)
  | t1 == t2  = cleanTrivialConstraints rest
  | otherwise = Constraint_Unify t1 t2 : cleanTrivialConstraints rest
cleanTrivialConstraints (c : rest) = c : cleanTrivialConstraints rest
