{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
module Cobalt.Script.Script (
  Script(..), TyScript
, toConstraintList
, fvScript
, substScript
, substsScript
, simplifyScript
, removeExistsScript
) where

import Data.List (intercalate, union, (\\))
import Unbound.LocallyNameless (fv, subst, substs)

import Cobalt.Language.Syntax (SourcePos)
import Cobalt.Types

data Script var constraint info
  = Empty
  | Singleton constraint info
  | Merge  [Script var constraint info] info
  | Asym   (Script var constraint info) (Script var constraint info) info
  | Exists [var] [constraint] (Script var constraint info)

type TyScript = Script TyVar Constraint (Maybe (SourcePos,SourcePos), Maybe String)

toConstraintList :: ([var] -> [constraint] -> [constraint] -> constraint)  -- Exists
                 -> Script var constraint msg  -- Script
                 -> [constraint]
toConstraintList _ex Empty           = []
toConstraintList _ex (Singleton c _) = [c]
toConstraintList ex  (Merge ss _)    = concatMap (toConstraintList ex) ss
toConstraintList ex  (Asym s1 s2 _)  = toConstraintList ex s1 ++ toConstraintList ex s2
toConstraintList ex  (Exists v q s)  = [ex v q (toConstraintList ex s)]

fvScript :: TyScript -> [TyVar]
fvScript Empty = []
fvScript (Singleton c _) = fv c
fvScript (Merge lst _)   = foldr union [] (map fvScript lst)
fvScript (Asym c1 c2 _)  = fvScript c1 `union` fvScript c2
fvScript (Exists v _ s)  = fvScript s \\ v

substScript :: TyVar -> MonoType -> TyScript -> TyScript
substScript _ _ Empty = Empty
substScript v m (Singleton c i) = Singleton (subst v m c) i
substScript v m (Merge ss i)    = Merge (map (substScript v m) ss) i
substScript v m (Asym c1 c2 i)  = Asym (substScript v m c1) (substScript v m c2) i
substScript v m (Exists vs q w) = Exists vs (map (subst v m) q) (substScript v m w)

substsScript :: [(TyVar, MonoType)] -> TyScript -> TyScript
substsScript _ Empty = Empty
substsScript v (Singleton c i) = Singleton (substs v c) i
substsScript v (Merge ss i)    = Merge (map (substsScript v) ss) i
substsScript v (Asym c1 c2 i)  = Asym (substsScript v c1) (substsScript v c2) i
substsScript v (Exists vs q w) = Exists vs (map (substs v) q) (substsScript v w)


instance Show TyScript where
  show Empty = ""
  show (Singleton c (_,msg)) = show c ++ showMsg msg
  show (Merge cs (_,msg))    = "merge" ++ showMsg msg ++ "\n" ++ intercalate "\n"
                                 (map (\c -> intercalate "\n" (map ("  " ++) (lines (show c)))) cs)
  show (Asym c1 c2 (_,msg))  = "asym" ++ showMsg msg ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                                                     ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Exists _vs _cs _s)   = "exists"

showMsg :: Maybe String -> String
showMsg (Just m) = " => " ++ m
showMsg Nothing  = "" 

simplifyScript :: Script var constraint info -> Script var constraint info
simplifyScript Empty = Empty
simplifyScript s@(Singleton _ _) = s
simplifyScript (Merge ss info)   = case filter notEmpty $ map simplifyScript ss of
                                     []  -> Empty
                                     [m] -> m
                                     ms  -> Merge ms info
                                   where notEmpty Empty = False
                                         notEmpty _     = True
simplifyScript (Asym c1 c2 info) = let s1 = simplifyScript c1
                                       s2 = simplifyScript c2
                                    in case (s1, s2) of
                                         (Empty, _) -> s2
                                         (_, Empty) -> s1
                                         _          -> Asym s1 s2 info
simplifyScript (Exists v q s)    = Exists v q (simplifyScript s)

removeExistsScript :: TyScript -> (TyScript, [Constraint], [TyVar])
removeExistsScript Empty = (Empty, [], [])
removeExistsScript s@(Singleton _ _) = (s, [], [])
removeExistsScript (Merge ss info) =
  let (remSs, rest, vars) = unzip3 (map removeExistsScript ss)
   in (Merge remSs info, foldr union [] rest, foldr union [] vars)
removeExistsScript (Asym c1 c2 info) =
  let (s1, r1, v1) = removeExistsScript c1
      (s2, r2, v2) = removeExistsScript c2
   in (Asym s1 s2 info, r1 ++ r2, union v1 v2)
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
