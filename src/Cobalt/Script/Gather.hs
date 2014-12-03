{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module Cobalt.Script.Gather (
  Syn(..)
, Gathered
, mainTypeRules
) where

import Control.Lens hiding (at)
import Control.Lens.Extras
import Data.List (insert, (\\), nub)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import Data.Regex.MultiRules
import Unbound.LocallyNameless

import Cobalt.Language.Syntax (SourcePos, fnE)
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
                , matchRule
                , caseRule
                ]

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
  inj (UTerm_AbsAnn_ __ __ (inner <<- any_) __ __) ->>> \(UTerm_AbsAnn v (vpos,vty) _ (tyAnn,_) (p,thisTy)) -> do
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
  inj (UTerm_LetAnn_ __ (e1 <<- any_) (e2 <<- any_) __ __) ->>>
    \(UTerm_LetAnn x _ _ (tyAnn,(q1,t1,_)) (p,thisTy)) -> do
      let isMono = case tyAnn of
                     PolyType_Mono [] m -> Just m
                     _                  -> Nothing
      -- Work on environment
      copy [e1, e2]
      env <- use (this.inh_.fnE)
      -- Change second part environment, now we have the type!
      at e2 . inh_ . fnE %= ((translate x, tyAnn) : )
      -- Create the output script
      e1Syn <- use (at e1 . syn)
      e2Syn <- use (at e2 . syn)
      this.syn .= mappend e1Syn e2Syn
      this.syn._Term.given .= case (isMono, e1Syn, e2Syn) of
        (Just _,  GatherTerm g1 _ _, GatherTerm g2 _ _) -> g1 ++ g2
        (Nothing, _                , GatherTerm g2 _ _) -> g2
        _ -> thisIsNotOk
      this.syn._Term.wanted .= case (isMono, e1Syn, e2Syn) of
        (Just m, GatherTerm _ [w1] [ity1], GatherTerm _ [w2] [ity2]) -> 
            [ Merge [ w1, Singleton (Constraint_Unify (var ity1) m) (Just p, Nothing)
                    , w2, Singleton (Constraint_Unify (var thisTy) (var ity2)) (Just p, Nothing)
                    ] (Just p, Nothing) ]
        (Nothing, GatherTerm g1 [w1] [ity1], GatherTerm _ [w2] [ity2]) -> 
            let vars = insert ity1 (fvScript w1) \\ nub (fv env)
             in [ Merge [ Exists vars (q1 ++ g1) (Merge [ Singleton (Constraint_Unify (var ity1) t1) (Just p, Nothing)
                                                        , w1 ] (Just p, Nothing))
                        , w2, Singleton (Constraint_Unify (var thisTy) (var ity2)) (Just p, Nothing)
                        ] (Just p, Nothing) ]
        _ -> thisIsNotOk
      this.syn._Term.ty .= [thisTy]

matchRule :: TypeRule
matchRule = rule $ \(e, branches) ->
  inj (UTerm_Match_ (e <<- any_) __ __ [branches <<- any_] __) ->>> \(UTerm_Match _ k mk _ (p,thisTy)) -> do
        copy [e]
        copy [branches]
        env <- use (this.inh_.fnE)
        einfo <- use (at e . syn)
        binfo <- use (at branches . syn)
        -- Handle errors
        this.syn .= case (einfo, binfo) of
          (Error eerr, Error berr) -> Error (eerr ++ berr)
          (Error eerr, _) -> Error eerr
          (_, Error berr) -> Error berr
          _ -> mempty
        -- Check if we found the data type in the declarations
        this.syn %= case mk of
          Just _  -> id
          Nothing -> \x -> mappend (Error ["Cannot find data type '" ++ k]) x
        -- Do the final thing
        this.syn._Term.given  .= case (einfo, binfo, mk) of
          (GatherTerm g _ _, GatherCase cases, Just mko) -> 
            let caseInfos = map (generateCase (nub (fv env)) thisTy p mko) cases in
            case filter (is _Nothing) caseInfos of
              [] -> g ++ concatMap (snd . fromJust) caseInfos
              _ -> thisIsNotOk
          _ -> thisIsNotOk
        this.syn._Term.wanted .= case (einfo, binfo, mk) of
          (GatherTerm _ [we] [te], GatherCase cases, Just mko) ->
             let caseInfos = map (generateCase (nub (fv env)) thisTy p mko) cases in
             case filter (is _Nothing) caseInfos of
               [] -> [ Asym (Singleton (Constraint_Unify (var te) mko) (Just p, Just "Expression in match must be of the specified type"))
                            (Merge (we : map (fst . fromJust) caseInfos) (Just p, Nothing))
                            (Just p, Nothing) ]
               _ -> thisIsNotOk
          _ -> thisIsNotOk
        this.syn._Term.ty .= [thisTy]

generateCase :: [TyVar] -> TyVar -> (SourcePos,SourcePos) -> MonoType -> GatherCaseInfo
             -> Maybe (TyScript, [Constraint])
generateCase envVars thisTy p (MonoType_Con k vars) (GatherCaseInfo g betaVars q (MonoType_Con kc varsc) s caseTy)
  | k == kc, [] <- betaVars, [] <- q =
     Just ( Asym (Singleton (Constraint_Unify (var thisTy) (var caseTy)) (Just p, Nothing))
                 (foldr (\(MonoType_Var v1, v2) curS -> substScript v1 v2 curS) s (zip varsc vars))
                 (Just p, Nothing)
          , g )
  | k == kc =  -- Existential case
     let evars = nub (union (fv varsc) (fvScript s)) \\ union envVars (fv vars)
      in Just ( Exists evars (g ++ q ++ zipWith Constraint_Unify vars varsc)
                       (Asym (Singleton (Constraint_Unify (var thisTy) (var caseTy)) (Just p, Nothing))
                             (foldr (\(MonoType_Var v1, v2) curS -> substScript v1 v2 curS) s (zip varsc vars))
                             (Just p, Nothing))
              , [] )
  | otherwise = Nothing
generateCase _ _ _ _ _ = thisIsNotOk

caseRule :: TypeRule
caseRule = rule $ \e ->
  inj (UCaseAlternative_ __ __ __ (e <<- any_) __) ->>> \(UCaseAlternative con vs caseTy _ _) -> do
    let caseTy' = case caseTy of
                    Just (_,(q, arr -> (argsT, MonoType_Con dname convars), boundvars)) -> Just (q, argsT, dname, convars, boundvars)
                    _ -> Nothing
    -- Work on new environment
    copy [e]
    at e . inh_ . fnE %= case caseTy' of
      Nothing -> id
      Just (_,argsT,_,_,_) -> ((zip (map translate vs) (map (PolyType_Mono []) argsT)) ++) -- Add to environment info from matching
    -- Work in case alternative
    eSyn <- use (at e . syn)
    this.syn .= case caseTy' of
      Nothing -> case eSyn of
        Error err -> Error $ ("Cannot find constructor " ++ show con) : err
        _ -> Error ["Cannot find constructor " ++ show con]
      Just (q,_,dname,convars,boundvars) -> case eSyn of
        Error err -> Error err
        GatherTerm g [w] [eTy] ->
          let -- resultC = Singleton (Constraint_Unify (var thisTy) (var eTy)) (Just p, Nothing)
              betaVars = boundvars \\ fv convars
           in GatherCase [GatherCaseInfo g betaVars q (MonoType_Con dname convars) w eTy]
        _ -> thisIsNotOk
    
thisIsNotOk :: a
thisIsNotOk = error "This should never happen"
