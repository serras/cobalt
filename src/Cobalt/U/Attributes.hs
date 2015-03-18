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
, GatherTermInfo(..)
, GatherCaseInfo(..)
, _Error
, _Term
, given
, ty
, wanted
, _Case
, TypeRule
) where

import Control.Lens hiding (at)
import Data.List (union)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import qualified Data.Regex.MultiRules as Rx
import Unbound.LocallyNameless (FreshM)

import Cobalt.Core
import Cobalt.Language
import Cobalt.U.Script

type Errors = [String]
data Syn (ix :: Ix) where
  Error      :: Errors -> Syn ix
  GatherTerm :: [Constraint] -> [TyVar] -> FreshM GatherTermInfo -> Syn IsATerm
  GatherCase :: [GatherCaseInfo] -> Syn IsACaseAlternative

data GatherTermInfo = GatherTermInfo { tree :: [TyScript]
                                     , custom :: [Constraint]
                                     , customVars :: [TyVar]
                                     }

data GatherCaseInfo = GatherCaseInfo { _extraConstraints :: [Constraint]
                                     , _hiddenVars :: [TyVar]
                                     , _konQ :: [Constraint]
                                     , _konT :: MonoType
                                     , _script :: FreshM (TyScript, [Constraint], [TyVar])
                                     , _thisVar :: TyVar
                                     }

type Gathered = Syn IsATerm

_Error :: Prism' (Syn ix) Errors
_Error = prism Error (\x -> case x of
                              Error e -> Right e
                              _       -> Left x)

_Term :: Prism' (Syn IsATerm) ([Constraint], [TyVar], FreshM GatherTermInfo)
_Term = prism (\(g,v,i) -> GatherTerm g v i)
              (\x -> case x of
                       GatherTerm g v i -> Right (g,v,i)
                       _                -> Left x)

given :: Functor f => ([Constraint] -> f [Constraint])
      -> ([Constraint], [TyVar], FreshM GatherTermInfo) -> f ([Constraint], [TyVar], FreshM GatherTermInfo)
given = _1

ty :: Functor f => ([TyVar] -> f [TyVar])
   -> ([Constraint], [TyVar], FreshM GatherTermInfo) -> f ([Constraint], [TyVar], FreshM GatherTermInfo)
ty = _2

wanted :: Functor f => (FreshM GatherTermInfo -> f (FreshM GatherTermInfo))
       -> ([Constraint], [TyVar], FreshM GatherTermInfo) -> f ([Constraint], [TyVar], FreshM GatherTermInfo)
wanted = _3

_Case :: Prism' (Syn IsACaseAlternative) [GatherCaseInfo]
_Case = prism GatherCase
              (\x -> case x of
                       GatherCase g -> Right g
                       _            -> Left x)

instance Monoid (Syn IsATerm) where
  mempty = GatherTerm [] [] $ return (GatherTermInfo [] [] [])
  (Error e1) `mappend` (Error e2) = Error (e1 `union` e2)
  e@(Error _) `mappend` _ = e
  _ `mappend` e@(Error _) = e
  (GatherTerm g1 v1 i1) `mappend` (GatherTerm g2 v2 i2) = GatherTerm (g1 ++ g2) (v1 ++ v2) $ do
    GatherTermInfo w1 c1 cv1 <- i1
    GatherTermInfo w2 c2 cv2 <- i2
    return $ GatherTermInfo (w1 ++ w2) (c1 ++ c2) (cv1 `union` cv2)

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

type TypeRule = Rx.Rule (Wrap Integer) (UTerm_ ((SourcePos,SourcePos),TyVar)) Inh Syn
