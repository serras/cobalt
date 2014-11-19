{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Cobalt.Script.Rules where

import Control.Lens hiding (at)
import Data.Monoid
import Data.Regex.Generics hiding (var)
import Data.Regex.Rules as Rx
import Unbound.LocallyNameless

import Cobalt.Language.Syntax
import Cobalt.Script.Script
import Cobalt.Script.Syntax
import Cobalt.Types

type Errors = [String]
data Gathered = Gathered { _givenC  :: [Constraint]
                         , _wantedC :: TyScript
                         , _ty      :: [TyVar]
                         }
              deriving Show
makeLenses ''Gathered

instance Monoid Gathered where
  mempty = Gathered [] Empty []
  (Gathered g1 w1 v1) `mappend` (Gathered g2 w2 v2)
    = Gathered (g1 ++ g2) (Merge [w1,w2] (Nothing,"")) (v1 ++ v2)

type Inh = Env
type Syn = Either Errors Gathered

instance Monoid Syn where
  mempty = Right mempty
  (Left s)  `mappend` (Left r)  = Left (s ++ r)
  (Left s)  `mappend` _         = Left s
  _         `mappend` (Left r)  = Left r
  (Right s) `mappend` (Right r) = Right (s `mappend` r)

type UTermWithPos = UTerm_ ((SourcePos,SourcePos),TyVar)
type TypeRule = Rx.Rule Integer UTermWithPos Inh Syn
