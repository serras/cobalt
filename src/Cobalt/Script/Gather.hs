{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Cobalt.Script.Gather (
  Gathered
, givenC
, wantedC
, ty
, mainTypeRules
) where

import Control.Applicative
import Control.Lens hiding (at)
import Control.Monad.State (MonadState)
import Data.Monoid
import Data.Regex.Generics hiding (var)
import Data.Regex.Rules
import Unbound.LocallyNameless

import Cobalt.Language.Syntax (Env, fnE, SourcePos)
import Cobalt.Script.Syntax
import Cobalt.Script.Script
import Cobalt.Types
import Cobalt.Util ()

type Errors = [String]
data Gathered = Gathered { _givenC  :: [Constraint]
                         , _wantedC :: TyScript
                         , _ty      :: [TyVar]
                         }
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
type TypeRule = Rule Integer UTermWithPos Inh Syn

mainTypeRules :: [TypeRule]
mainTypeRules = [intLiteralRule, varRule, absRule, appRule]

intLiteralRule :: TypeRule
intLiteralRule = rule $
  shallow (UTerm_IntLiteral_ __ __) ->>> \(UTerm_IntLiteral _ (p,thisTy)) -> do
    this.syn._Right.givenC  .= []
    this.syn._Right.wantedC .= Singleton (Constraint_Unify (var thisTy) MonoType_Int)
                                 (Just p, "Numeric literal must be of type Int")
    this.syn._Right.ty      .= [thisTy]

varRule :: TypeRule
varRule = rule $
  shallow (UTerm_Var_ __ __) ->>> \(UTerm_Var v (p,thisTy)) -> do
    env <- use (this.inh.fnE)
    case lookup (translate v) env of
      Nothing    -> this.syn .= Left ["Cannot find " ++ show v]
      Just sigma -> do this.syn._Right.givenC  .= []
                       this.syn._Right.wantedC .= Singleton (Constraint_Inst (var thisTy) sigma)
                                                    (Just p, show v ++ " has type " ++ show sigma ++ " from the environment")
                       this.syn._Right.ty      .= [thisTy]

absRule :: TypeRule
absRule = rule $ \inner ->
  shallow (UTerm_Abs_ __ __ (inner <<- any_) __) ->>> \(UTerm_Abs v (_,vty) _ (p,thisTy)) -> do
    at inner . inh . fnE %= ((translate v, var vty) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    case innerSyn of
     Right (Gathered g w [ity]) -> do
       this.syn._Right.givenC  .= g
       let msg = "Function must have an arrow type"
       this.syn._Right.wantedC .= Asym (Singleton (Constraint_Unify (var thisTy) (var vty :-->: var ity))
                                                  (Just p, msg))
                                       w (Just p, msg)
       this.syn._Right.ty .= [thisTy]
     _ -> this.syn .= innerSyn

appRule :: TypeRule
appRule = rule $ \e1 e2 ->
  shallow (UTerm_App_ (e1 <<- any_) (e2 <<- any_) __) ->>> \(UTerm_App _ _ (p,thisTy)) -> do
    e1Syn <- use (at e1 . syn)
    e2Syn <- use (at e2 . syn)
    case (e1Syn, e2Syn) of
      (Right (Gathered g1 w1 [ity1]), Right (Gathered g2 w2 [ity2])) -> do
        this.syn._Right.givenC  .= g1 ++ g2
        let msg = "Application must have correct domain and codomain"
        this.syn._Right.wantedC .= Asym (Singleton (Constraint_Unify (var ity1) (var ity2 :-->: var thisTy))
                                                   (Just p, msg))
                                        (Merge [w1,w2] (Just p, "Expressions must be compatible"))
                                        (Just p, msg)
        this.syn._Right.ty .= [thisTy]
      _ -> this.syn .= mappend e1Syn e2Syn
