{-# LANGUAGE GADTs #-}
module Cobalt.Script.Script where

import Cobalt.Types

data Script var constraint msg
  = Empty
  | Singleton constraint msg
  | Merge  [Script var constraint msg] msg
  | Asym   (Script var constraint msg) (Script var constraint msg) msg
  | Exists [var] [constraint] (Script var constraint msg)

type TyScript = Script TyVar Constraint String

gather :: ([var] -> [constraint] -> [constraint] -> constraint)  -- Exists
       -> Script var constraint msg  -- Script
       -> [constraint]
gather _ex Empty           = []
gather _ex (Singleton c _) = [c]
gather ex  (Merge ss _)    = concatMap (gather ex) ss
gather ex  (Asym s1 s2 _)  = gather ex s1 ++ gather ex s2
gather ex  (Exists v q s)  = [ex v q (gather ex s)]

