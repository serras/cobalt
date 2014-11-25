{-# LANGUAGE PatternSynonyms #-}
module Cobalt.Script.Gather (
  Gathered(..)
, givenC
, wantedC
, ty
, mainTypeRules
) where

import Control.Lens hiding (at)
import Data.Monoid
import Data.Regex.Generics hiding (var)
import Data.Regex.Rules
import Unbound.LocallyNameless

import Cobalt.Language.Syntax (fnE)
import Cobalt.Script.Rules
import Cobalt.Script.Script
import Cobalt.Script.Syntax
import Cobalt.Types
import Cobalt.Util ()

mainTypeRules :: [TypeRule]
mainTypeRules = [intLiteralRule, varRule, absRule, appRule]

intLiteralRule :: TypeRule
intLiteralRule = rule $
  inj (UTerm_IntLiteral_ __ __) ->>> \(UTerm_IntLiteral _ (p,thisTy)) -> do
    this.syn._Right.givenC  .= []
    this.syn._Right.wantedC .= [Singleton (Constraint_Unify (var thisTy) MonoType_Int)
                                  (Just p, Just "Numeric literal must be of type Int")]
    this.syn._Right.ty      .= [thisTy]

varRule :: TypeRule
varRule = rule $
  inj (UTerm_Var_ __ __) ->>> \(UTerm_Var v (p,thisTy)) -> do
    env <- use (this.inh.fnE)
    case lookup (translate v) env of
      Nothing    -> this.syn .= Left ["Cannot find " ++ show v]
      Just sigma -> do this.syn._Right.givenC  .= []
                       this.syn._Right.wantedC .= [Singleton (Constraint_Inst (var thisTy) sigma)
                                                     (Just p, Just $ show v ++ " has type " ++ show sigma ++ " from the environment")]
                       this.syn._Right.ty      .= [thisTy]

absRule :: TypeRule
absRule = rule $ \inner ->
  inj (UTerm_Abs_ __ __ (inner <<- any_) __) ->>> \(UTerm_Abs v (_,vty) _ (p,thisTy)) -> do
    at inner . inh . fnE %= ((translate v, var vty) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    this.syn .= innerSyn
    this.syn._Right.givenC  .= case innerSyn of
      Right (Gathered g _ _) -> g
      _                      -> thisIsNotOk
    let msg = Just "Function must have an arrow type"
    this.syn._Right.wantedC .= case innerSyn of
      Right (Gathered _ [w] [ity]) -> [Asym (Singleton (Constraint_Unify (var thisTy) (var vty :-->: var ity))
                                                       (Just p, msg))
                                            w (Just p, msg)]
      _                          -> thisIsNotOk
    this.syn._Right.ty .= [thisTy]

appRule :: TypeRule
appRule = rule $ \e1 e2 ->
  inj (UTerm_App_ (e1 <<- any_) (e2 <<- any_) __) ->>> \(UTerm_App _ _ (p,thisTy)) -> do
    e1Syn <- use (at e1 . syn)
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Right.givenC  .= case (e1Syn, e2Syn) of
      (Right (Gathered g1 _ _), Right (Gathered g2 _ _)) -> g1 ++ g2
      _ -> thisIsNotOk
    let msg = Just "Application must have correct domain and codomain"
    this.syn._Right.wantedC .= case (e1Syn, e2Syn) of
      (Right (Gathered _ [w1] [ity1]), Right (Gathered _ [w2] [ity2])) ->
        [Asym (Singleton (Constraint_Unify (var ity1) (var ity2 :-->: var thisTy))
                         (Just p, msg))
              (Merge [w1,w2] (Just p, Just "Expressions must be compatible"))
              (Just p, msg)]
      _ -> thisIsNotOk
    this.syn._Right.ty .= [thisTy]

thisIsNotOk :: a
thisIsNotOk = error "This should never happen"
