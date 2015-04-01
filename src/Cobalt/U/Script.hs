{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE DeriveFunctor #-}
module Cobalt.U.Script (
  Script(..)
, TyScript
, TyScriptInfo
, toConstraintList
, toConstraintList'
, fvScript
, substScript
, substsScript
, joinScript
, simplifyScript
, removeExistsScript
) where

import Data.List (intercalate, union, (\\))
import Data.Monoid
import Unbound.LocallyNameless (fv, subst, substs)

import Cobalt.Core
import Cobalt.Language (SourcePos)

data Script var pos info constraint
  = Empty
  | Label     info (Script var pos info constraint)
  | Singleton constraint pos (Maybe info)
  | Join      [Script var pos info constraint] pos
  | AsymJoin  (Script var pos info constraint) (Script var pos info constraint) pos
  | Sequence  (Script var pos info constraint) (Script var pos info constraint) pos
  | Exists    [var] [constraint] (Script var pos info constraint) pos
  deriving Functor

type TyScriptPos  = (SourcePos,SourcePos)
type TyScriptInfo = String
type TyScript = Script TyVar TyScriptPos TyScriptInfo Constraint

foldConstraint :: Monoid b
               => (constraint -> b)
               -> ([var] -> [constraint] -> b -> b)
               -> Script var pos info constraint -> b
foldConstraint _ _  Empty              = mempty
foldConstraint c ex (Label _ s)        = foldConstraint c ex s
foldConstraint c _  (Singleton s _ _)  = c s
foldConstraint c ex (Join ss _)        = mconcat $ map (foldConstraint c ex) ss
foldConstraint c ex (AsymJoin s1 s2 _) = foldConstraint c ex s1 <> foldConstraint c ex s2
foldConstraint c ex (Sequence s1 s2 _) = foldConstraint c ex s1 <> foldConstraint c ex s2
foldConstraint c ex (Exists v q s _)   = ex v q (foldConstraint c ex s)

toConstraintList :: ([var] -> [constraint] -> [constraint] -> [constraint])  -- Exists
                 -> Script var pos info constraint  -- Script
                 -> [constraint]
toConstraintList ex = foldConstraint (\x -> [x]) ex

toConstraintList' :: Script var pos info constraint -> [constraint]
toConstraintList' = toConstraintList (\_ _ _ -> [])

fvScript :: Script TyVar pos info Constraint -> [TyVar]
fvScript = foldConstraint fv (\v _ vars -> vars \\ v)

substScript :: TyVar -> MonoType
            -> Script TyVar pos info Constraint
            -> Script TyVar pos info Constraint
substScript v m = fmap (subst v m)

substsScript :: [(TyVar, MonoType)]
             -> Script TyVar pos info Constraint
             -> Script TyVar pos info Constraint
substsScript v = fmap (substs v)

joinScript :: pos
           -> Script var pos info constraint
           -> Script var pos info constraint
           -> Script var pos info constraint
joinScript _ s Empty = s
joinScript _ Empty s = s
joinScript p (Join ss _) s@(Singleton _ _ _) = Join (s:ss) p
joinScript p s@(Singleton _ _ _) (Join ss _) = Join (s:ss) p
joinScript p s1 s2 = Join [s1,s2] p

instance (Show constraint, Show pos, Show info)
  => Show (Script var pos info constraint) where
  show Empty               = ""
  show (Label msg cs)      = "label { " ++ show msg ++ "}\n" ++ intercalate "\n" (map ("  " ++) (lines (show cs)))
  show (Singleton c p i)   = show c ++ " @ " ++ show p
                             ++ case i of { Just msg -> " {" ++ show msg ++ "}"; _ -> ""}
  show (Join cs p)         = "join @ "  ++ show p
                             ++ "\n" ++ intercalate "\n" (map (\c -> intercalate "\n" (map ("  " ++) (lines (show c)))) cs)
  show (AsymJoin c1 c2 p)  = "asymjoin @ " ++ show p
                             ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                             ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Sequence c1 c2 p)  = "sequence @ " ++ show p
                             ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                             ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Exists _ _ _ _)    = "exists"

simplifyScript :: Script var pos info constraint -> Script var pos info constraint
simplifyScript Empty               = Empty
simplifyScript s@(Singleton _ _ _) = s
simplifyScript (Label i s)         = Label i (simplifyScript s)
simplifyScript (Join ss p)         = case filter notEmpty $ map simplifyScript ss of
                                       []  -> Empty
                                       [m] -> m
                                       ms  -> Join ms p
                                     where notEmpty Empty = False
                                           notEmpty _     = True
simplifyScript (AsymJoin c1 c2 p)  = let s1 = simplifyScript c1
                                         s2 = simplifyScript c2
                                      in case (s1, s2) of
                                           (Empty, _) -> s2
                                           (_, Empty) -> s1
                                           _          -> AsymJoin s1 s2 p
simplifyScript (Sequence c1 c2 p)  = let s1 = simplifyScript c1
                                         s2 = simplifyScript c2
                                      in case (s1, s2) of
                                           (Empty, _) -> s2
                                           (_, Empty) -> s1
                                           _          -> Sequence s1 s2 p
simplifyScript (Exists v q s p)    = Exists v q (simplifyScript s) p

removeExistsScript :: TyScript -> (TyScript, [Constraint], [TyVar])
removeExistsScript Empty = (Empty, [], [])
removeExistsScript (Label i s) =
  let (s', r, v) = removeExistsScript s
   in (Label i s', r, v)
removeExistsScript s@(Singleton _ _ _) = (s, [], [])
removeExistsScript (Join ss p) =
  let (remSs, rest, vars) = unzip3 (map removeExistsScript ss)
   in (simplifyScript (Join remSs p), foldr union [] rest, foldr union [] vars)
removeExistsScript (AsymJoin c1 c2 p) =
  let (s1, r1, v1) = removeExistsScript c1
      (s2, r2, v2) = removeExistsScript c2
   in (simplifyScript (AsymJoin s1 s2 p), r1 ++ r2, union v1 v2)
removeExistsScript (Sequence c1 c2 p) =
  let (s1, r1, v1) = removeExistsScript c1
      (s2, r2, v2) = removeExistsScript c2
   in (simplifyScript (Sequence s1 s2 p), r1 ++ r2, union v1 v2)
removeExistsScript (Exists v q s p) =
  let q1 = cleanTrivialConstraints q in
  case v \\ (fv q ++ fvScript s) of  -- Find not needed vars
    [] -> case applyPossibleSubsts v q1 s of
            Just (q2, s2) -> removeExistsScript (Exists v q2 s2 p)
            Nothing -> -- We have finished
              case removeExistsScript s of
                (sR, [], []) -> -- Check whether q1 can be flowed upwards
                  case (fv q1 `union` fvScript sR) \\ v of
                    [] -> -- They can, all variables are inside
                          (sR, q1, v)
                    _  -> (Exists v q1 sR p, [], [])
                (sR, moreQ, moreV) -> removeExistsScript (Exists (union v moreV) (union q1 moreQ) sR p)
    notNeededVars -> removeExistsScript (Exists (v \\ notNeededVars) q1 s p)

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
