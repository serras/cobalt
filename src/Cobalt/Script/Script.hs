{-# LANGUAGE GADTs #-}
module Cobalt.Script.Script where

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

