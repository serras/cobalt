{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
module Cobalt.Script.Gather (
  Syn(..)
, Gathered
, mainTypeRules
) where

import Control.Lens hiding (at)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import Data.Regex.MultiRules
import Unbound.LocallyNameless

import Cobalt.Language.Syntax (fnE)
import Cobalt.Script.Rules
import Cobalt.Script.Script
import Cobalt.Script.Syntax
import Cobalt.Types
import Cobalt.Util ()

mainTypeRules :: [TypeRule]
mainTypeRules = [ intLiteralRule
                , varRule
                , absRule
                , absAnnRule
                , appRule
                , letRule
                , letAnnRule
                ]

given  = _1
wanted = _2
ty     = _3

intLiteralRule :: TypeRule
intLiteralRule = rule0 $
  inj (UTerm_IntLiteral_ __ __) ->>> \(UTerm_IntLiteral _ (p,thisTy)) -> do
    this.syn._Term.given  .= []
    this.syn._Term.wanted .= [Singleton (Constraint_Unify (var thisTy) MonoType_Int)
                                        (Just p, Just "Numeric literal must be of type Int")]
    this.syn._Term.ty     .= [thisTy]

varRule :: TypeRule
varRule = rule0 $
  inj (UTerm_Var_ __ __) ->>> \(UTerm_Var v (p,thisTy)) -> do
    env <- use (this.inh_.fnE)
    case lookup (translate v) env of
      Nothing    -> this.syn .= Error ["Cannot find " ++ show v]
      Just sigma -> do this.syn._Term.given  .= []
                       this.syn._Term.wanted .= [Singleton (Constraint_Inst (var thisTy) sigma)
                                                           (Just p, Just $ show v ++ " is typed from the environment")]
                       this.syn._Term.ty     .= [thisTy]

absRule :: TypeRule
absRule = rule $ \inner ->
  inj (UTerm_Abs_ __ __ (inner <<- any_) __) ->>> \(UTerm_Abs v (_,vty) _ (p,thisTy)) -> do
    copy [inner]
    at inner . inh_ . fnE %= ((translate v, var vty) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    this.syn .= innerSyn
    this.syn._Term.given .= case innerSyn of
      GatherTerm g _ _ -> g
      _                -> thisIsNotOk
    let msg = Just "Function must have an arrow type"
    this.syn._Term.wanted .= case innerSyn of
      GatherTerm _ [w] [ity] -> [Asym (Singleton (Constraint_Unify (var thisTy) (var vty :-->: var ity))
                                                 (Just p, msg))
                                      w (Just p, msg)]
      _                      -> thisIsNotOk
    this.syn._Term.ty .= [thisTy]

absAnnRule :: TypeRule
absAnnRule = rule $ \inner ->
  inj (UTerm_AbsAnn_ __ __ (inner <<- any_) __ __) ->>> \(UTerm_AbsAnn v (vpos,vty) _ tyAnn (p,thisTy)) -> do
    copy [inner]
    at inner . inh_ . fnE %= ((translate v, tyAnn) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    this.syn .= innerSyn
    this.syn._Term.given .= case innerSyn of
      GatherTerm g _ _ -> g
      _                -> thisIsNotOk
    let msg = Just "Function must have an arrow type"
    this.syn._Term.wanted .= case innerSyn of
      GatherTerm _ [w] [ity] -> case tyAnn of
        PolyType_Mono [] m -> [Asym (Singleton (Constraint_Unify (var thisTy) (m :-->: var ity)) (Just p, msg))
                                    w (Just p, msg)]
        _ -> [Asym (Merge [ Singleton (Constraint_Unify (var thisTy) (var vty :-->: var ity)) (Just p, msg)
                          , Singleton (Constraint_Equal (var vty) tyAnn) (Just vpos, msg) ] (Just p, msg))
                   w (Just p, msg)]
      _ -> thisIsNotOk
    this.syn._Term.ty .= [thisTy]

appRule :: TypeRule
appRule = rule $ \(e1, e2) ->
  inj (UTerm_App_ (e1 <<- any_) (e2 <<- any_) __) ->>> \(UTerm_App _ _ (p,thisTy)) -> do
    copy [e1, e2]
    e1Syn <- use (at e1 . syn)
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Term.given  .= case (e1Syn, e2Syn) of
      (GatherTerm g1 _ _, GatherTerm g2 _ _) -> g1 ++ g2
      _ -> thisIsNotOk
    let msg = Just "Application must have correct domain and codomain"
    this.syn._Term.wanted .= case (e1Syn, e2Syn) of
      (GatherTerm _ [w1] [ity1], GatherTerm _ [w2] [ity2]) ->
        [Asym (Singleton (Constraint_Unify (var ity1) (var ity2 :-->: var thisTy))
                         (Just p, msg))
              (Merge [w1,w2] (Just p, Just "Expressions must be compatible"))
              (Just p, msg)]
      _ -> thisIsNotOk
    this.syn._Term.ty .= [thisTy]

letRule :: TypeRule
letRule = rule $ \(e1, e2) ->
  inj (UTerm_Let_ __ (e1 <<- any_) (e2 <<- any_) __) ->>> \(UTerm_Let x _ _ (p,thisTy)) -> do
    copy [e1, e2]
    e1Syn <- use (at e1 . syn)
    -- Change second part environment
    at e2 . inh_ . fnE %= case e1Syn of
      GatherTerm _ _ [ity1] -> ((translate x, var ity1) : )
      _                     -> id
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Term.given .= case (e1Syn, e2Syn) of
      (GatherTerm g1 _ _, GatherTerm g2 _ _) -> g1 ++ g2
      _ -> thisIsNotOk
    this.syn._Term.wanted .= case (e1Syn, e2Syn) of
      (GatherTerm _ [w1] _, GatherTerm _ [w2] [ity2]) ->
        [ Merge [w1, w2, Singleton (Constraint_Unify (var thisTy) (var ity2)) (Just p, Nothing)]
                (Just p, Nothing) ]
      _ -> thisIsNotOk
    this.syn._Term.ty .= [thisTy]

letAnnRule :: TypeRule
letAnnRule = rule $ \(e1, e2) ->
  inj (UTerm_LetAnn_ __ (e1 <<- any_) (e2 <<- any_) __ __) ->>> \(UTerm_LetAnn x _ _ tyAnn (p,thisTy)) -> do
    copy [e1, e2]
    e1Syn <- use (at e1 . syn)
    -- Change second part environment, now we have the type!
    at e2 . inh_ . fnE %= ((translate x, tyAnn) : )
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Term.given .= case (e1Syn, e2Syn) of
      (GatherTerm g1 _ _, GatherTerm g2 _ _) -> g1 ++ g2
      _ -> thisIsNotOk
    this.syn._Term.wanted .= case (e1Syn, e2Syn) of
      (GatherTerm _ [w1] [ity1], GatherTerm _ [w2] [ity2]) -> case tyAnn of
        PolyType_Mono [] m ->
          [ Merge [ w1, w2
                  , Singleton (Constraint_Unify (var thisTy) (var ity2)) (Just p, Nothing)
                  , Singleton (Constraint_Unify (var ity1) m) (Just p, Nothing) ]
                  (Just p, Nothing) ]
        _ -> error "Not yet implemented for polytypes"
      _ -> thisIsNotOk
    this.syn._Term.ty .= [thisTy]

{-
matchRule :: TypeRule
matchRule = rule $ \e branches ->
  inj (UTerm_Match_ (e <<- any_) __ [UCaseAlternative __ __ (branches <<- any_)] __) ->>
     \(UTerm_Match _ k alternatives (p,ty)) -> do
-}

thisIsNotOk :: a
thisIsNotOk = error "This should never happen"
