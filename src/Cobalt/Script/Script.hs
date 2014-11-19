{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Cobalt.Script.Script where

import Data.List (intercalate)

import Cobalt.Language.Syntax (SourcePos)
import Cobalt.Types

data Script var constraint info
  = Empty
  | Singleton constraint info
  | Merge  [Script var constraint info] info
  | Asym   (Script var constraint info) (Script var constraint info) info
  | Exists [var] [constraint] (Script var constraint info)

type TyScript = Script TyVar Constraint (Maybe (SourcePos,SourcePos),String)

gather :: ([var] -> [constraint] -> [constraint] -> constraint)  -- Exists
       -> Script var constraint msg  -- Script
       -> [constraint]
gather _ex Empty           = []
gather _ex (Singleton c _) = [c]
gather ex  (Merge ss _)    = concatMap (gather ex) ss
gather ex  (Asym s1 s2 _)  = gather ex s1 ++ gather ex s2
gather ex  (Exists v q s)  = [ex v q (gather ex s)]

instance Show TyScript where
  show Empty = ""
  show (Singleton c (_,msg)) = show c ++ " => " ++ msg
  show (Merge cs (_,msg))    = "merge  => " ++ msg ++ "\n" ++ intercalate "\n"
                                 (map (\c -> intercalate "\n" (map ("  " ++) (lines (show c)))) cs)
  show (Asym c1 c2 (_,msg))  = "asym  => " ++ msg ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c1)))
                                                  ++ "\n" ++ intercalate "\n" (map ("  " ++) (lines (show c2)))
  show (Exists _vs _cs _s)   = "exists"

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
