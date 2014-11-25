{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Cobalt.Script.Script (
  Script(..), TyScript,
  toConstraintList,
  fvScript,
  simplifyScript
) where

import Data.List (intercalate, union, (\\))
import Unbound.LocallyNameless (fv)

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
