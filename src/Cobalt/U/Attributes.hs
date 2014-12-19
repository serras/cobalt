{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
module Cobalt.U.Attributes (
  module Cobalt.U.Script
, Errors
, Inh
, theEnv
, theSat
, theTouchables
, Syn(..)
, Gathered
, GatherCaseInfo(..)
, _Error
, _Term
, given
, wanted
, ty
, custom
, customVars
, _Case
, TypeRule
) where

import Control.Lens hiding (at)
import Data.List (union)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx

import Cobalt.Core
import Cobalt.Language
import Cobalt.U.Script

type Errors = [String]
data Syn (ix :: Ix) where
  Error      :: Errors -> Syn ix
  GatherTerm :: [Constraint] -> [TyScript] -> [TyVar] -> [Constraint] -> [TyVar] -> Syn IsATerm
  GatherCase :: [GatherCaseInfo] -> Syn IsACaseAlternative

data GatherCaseInfo = GatherCaseInfo { _extraConstraints :: [Constraint]
                                     , _hiddenVars :: [TyVar]
                                     , _konQ :: [Constraint]
                                     , _konT :: MonoType
                                     , _script :: TyScript
                                     , _customChecks :: [Constraint]
                                     , _customVars :: [TyVar]
                                     , _thisVar :: TyVar
                                     }

type Gathered = Syn IsATerm

_Error :: Prism' (Syn ix) Errors
_Error = prism Error (\x -> case x of
                              Error e -> Right e
                              _       -> Left x)

_Term :: Prism' (Syn IsATerm) ([Constraint], [TyScript], [TyVar],[Constraint],[TyVar])
_Term = prism (\(g,w,t,c,cv) -> GatherTerm g w t c cv)
              (\x -> case x of
                       GatherTerm g w t c cv -> Right (g,w,t,c,cv)
                       _                     -> Left x)

given :: Functor f => ([Constraint] -> f [Constraint])
      -> ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar]) -> f ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar])
given = _1

wanted :: Functor f => ([TyScript] -> f [TyScript])
       -> ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar]) -> f ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar])
wanted = _2

ty :: Functor f => ([TyVar] -> f [TyVar])
   -> ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar]) -> f ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar])
ty = _3

custom :: Functor f => ([Constraint] -> f [Constraint])
       -> ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar]) -> f ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar])
custom = _4

customVars :: Functor f => ([TyVar] -> f [TyVar])
           -> ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar]) -> f ([Constraint],[TyScript],[TyVar],[Constraint],[TyVar])
customVars = _5

_Case :: Prism' (Syn IsACaseAlternative) [GatherCaseInfo]
_Case = prism GatherCase
              (\x -> case x of
                       GatherCase g -> Right g
                       _            -> Left x)

instance Monoid (Syn IsATerm) where
  mempty = GatherTerm [] [] [] [] []
  (Error e1) `mappend` (Error e2) = Error (e1 `union` e2)
  e@(Error _) `mappend` _ = e
  _ `mappend` e@(Error _) = e
  (GatherTerm g1 w1 v1 c1 cv1) `mappend` (GatherTerm g2 w2 v2 c2 cv2)
    = GatherTerm (g1 ++ g2) (w1 ++ w2) (v1 ++ v2) (c1 ++ c2) (cv1 `union` cv2)

instance Monoid (Syn IsACaseAlternative) where
  mempty = GatherCase []
  (Error e1) `mappend` (Error e2) = Error (e1 `union` e2)
  e@(Error _) `mappend` _ = e
  _ `mappend` e@(Error _) = e
  (GatherCase i1) `mappend` (GatherCase i2) = GatherCase (i1 ++ i2)

type Inh = Rx.IndexIndependent (Env, [Constraint], [TyVar])

theEnv :: Functor f => (Env -> f Env)
       -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theEnv = _1

theSat :: Functor f => ([Constraint] -> f [Constraint])
       -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theSat = _2

theTouchables :: Functor f => ([TyVar] -> f [TyVar])
              -> (Env, [Constraint], [TyVar]) -> f (Env, [Constraint], [TyVar])
theTouchables = _3

type TypeRule = Rx.Rule (Wrap Integer) (UTerm_ ((SourcePos,SourcePos),TyVar,[TyVar])) Inh Syn