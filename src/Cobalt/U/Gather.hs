{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module Cobalt.U.Gather (
  Syn(..)
, Gathered
, mainTypeRules
) where

import Control.Lens hiding (at)
import Control.Lens.Extras
import Control.Monad.State (MonadState)
import Data.List (insert, (\\), nub)
import Data.Maybe (fromJust)
import Data.Monoid
import Data.Regex.MultiGenerics hiding (var)
import Data.Regex.MultiRules
import Unbound.LocallyNameless

import Cobalt.Core
import Cobalt.Language
import Cobalt.U.Attributes
import Util.ExceptTIsFresh ()

mainTypeRules :: [TypeRule]
mainTypeRules = [ intLiteralRule
                , strLiteralRule
                , varRule
                , absRule
                , absAnnRule
                , appRule
                , letRule
                , letAnnRule
                , matchRule
                , caseRule
                ]

pattern SingletonC c     p = Singleton c p Nothing
pattern SingUnifyC m1 m2 p = SingletonC (Constraint_Unify m1 m2) p
pattern SingInstC  m  s  p = SingletonC (Constraint_Inst  m  s ) p
pattern SingEqualC m  s  p = SingletonC (Constraint_Equal m  s ) p

infix 4 .=!
(.=!) :: (MonadState s m, Monad n) => ASetter s s a [n b] -> b -> m ()
l .=! r = l .= [return r]

infix 4 .=.
(.=.) :: MonadState s m => ASetter s s a [t] -> t -> m ()
l .=. r = l .= [r]

ty :: UTerm ((SourcePos,SourcePos),TyVar) -> TyVar
ty = snd . ann

intLiteralRule :: TypeRule
intLiteralRule = rule0 $
  inj (UTerm_IntLiteral_ __ __) ->>> \theThing@(UTerm_IntLiteral _ (p,thisTy)) -> do
    this.syn._Term.given  .= []
    this.syn._Term.me     .= [theThing]
    this.syn._Term.wanted .=! GatherTermInfo { tree = SingUnifyC (var thisTy) MonoType_Int p
                                             , custom = []
                                             , customVars = []
                                             }

strLiteralRule :: TypeRule
strLiteralRule = rule0 $
  inj (UTerm_StrLiteral_ __ __) ->>> \theThing@(UTerm_StrLiteral _ (p,thisTy)) -> do
    this.syn._Term.given  .= []
    this.syn._Term.me     .= [theThing]
    this.syn._Term.wanted .=! GatherTermInfo { tree = SingUnifyC (var thisTy) MonoType_String p
                                             , custom = []
                                             , customVars = []
                                             }

varRule :: TypeRule
varRule = rule0 $
  inj (UTerm_Var_ __ __) ->>> \theThing@(UTerm_Var v (p,thisTy)) -> do
    env <- use (this.inh_.theEnv.fnE)
    case lookup (translate v) env of
      Nothing    -> this.syn .= Error ["Cannot find " ++ show v]
      Just sigma -> do this.syn._Term.given  .= []
                       this.syn._Term.me     .= [theThing]
                       this.syn._Term.wanted .=! GatherTermInfo { tree = SingInstC (var thisTy) sigma p
                                                                , custom = []
                                                                , customVars = []
                                                                }

absRule :: TypeRule
absRule = rule $ \inner ->
  inj (UTerm_Abs_ __ __ (inner <<- any_) __) ->>> \theThing@(UTerm_Abs v (_,vty) _ (p,thisTy)) -> do
    copy [inner]
    at inner . inh_ . theEnv . fnE %= ((translate v, var vty) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    this.syn .= innerSyn
    this.syn._Term.me .= [theThing]
    this.syn._Term.wanted .=. case innerSyn of
      GatherTerm _g [ity] [i] -> do
        gg@(GatherTermInfo w _ _ ) <- i
        return $ gg { tree = AsymJoin w (SingUnifyC (var thisTy) (var vty :-->: var (ty ity)) p) p }
      _ -> thisIsNotOk

absAnnRule :: TypeRule
absAnnRule = rule $ \inner ->
  inj (UTerm_AbsAnn_ __ __ (inner <<- any_) __ __) ->>> \theThing@(UTerm_AbsAnn v (vpos,vty) _ (tyAnn,_) (p,thisTy)) -> do
    copy [inner]
    at inner . inh_ . theEnv . fnE %= ((translate v, tyAnn) : ) -- Add to environment
    innerSyn <- use (at inner . syn)
    this.syn .= innerSyn
    this.syn._Term.me .= [theThing]
    this.syn._Term.wanted .=. case innerSyn of
      GatherTerm _g [ity] [i] -> do
        gg@(GatherTermInfo w _ _ ) <- i
        return $ gg { tree = case tyAnn of
                        PolyType_Mono [] m -> AsymJoin w (SingUnifyC (var thisTy) (m :-->: var (ty ity)) p) p
                        _ -> AsymJoin w (Join [ SingUnifyC (var thisTy) (var vty :-->: var (ty ity)) p
                                              , SingEqualC (var vty) tyAnn vpos ] p) p }
      _ -> thisIsNotOk

appRule :: TypeRule
appRule = rule $ \(e1, e2) ->
  inj (UTerm_App_ (e1 <<- any_) (e2 <<- any_) __) ->>> \theThing@(UTerm_App _ _ (p,thisTy)) -> do
    copy [e1, e2]
    e1Syn <- use (at e1 . syn)
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Term.me .= [theThing]
    this.syn._Term.wanted .=. case (e1Syn, e2Syn) of
      (GatherTerm _g1 [ity1] [i1], GatherTerm _g2 [ity2] [i2]) -> do
         GatherTermInfo w1 c1 cv1 <- i1
         GatherTermInfo w2 c2 cv2 <- i2
         return $ GatherTermInfo { tree = AsymJoin (Join [w1,w2] p) (SingUnifyC (var (ty ity1)) (var (ty ity2) :-->: var thisTy) p) p
                                 , custom = c1 ++ c2
                                 , customVars = cv1 `union` cv2
                                 }
      _ -> thisIsNotOk

letRule :: TypeRule
letRule = rule $ \(e1, e2) ->
  inj (UTerm_Let_ __ (e1 <<- any_) (e2 <<- any_) __) ->>> \theThing@(UTerm_Let x _ _ (p,thisTy)) -> do
    copy [e1, e2]
    e1Syn <- use (at e1 . syn)
    -- Change second part environment
    at e2 . inh_ . theEnv . fnE %= case e1Syn of
      GatherTerm _ [ity1] _ -> ((translate x, var (ty ity1)) : )
      _                     -> id
    e2Syn <- use (at e2 . syn)
    this.syn .= mappend e1Syn e2Syn
    this.syn._Term.me .= [theThing]
    this.syn._Term.wanted .=. case (e1Syn, e2Syn) of
      (GatherTerm _g1 _ity1 [i1], GatherTerm _g2 [ity2] [i2]) -> do
        GatherTermInfo w1 c1 cv1 <- i1
        GatherTermInfo w2 c2 cv2 <- i2
        return $ GatherTermInfo { tree = Join [w1, w2, SingUnifyC (var thisTy) (var (ty ity2)) p] p
                                , custom = c1 ++ c2
                                , customVars = cv1 `union` cv2
                                }
      _ -> thisIsNotOk

letAnnRule :: TypeRule
letAnnRule = rule $ \(e1, e2) ->
  inj (UTerm_LetAnn_ __ (e1 <<- any_) (e2 <<- any_) __ __) ->>>
    \theThing@(UTerm_LetAnn x _ _ (tyAnn,(q1,t1,_)) (p,thisTy)) -> do
      let isMono = case tyAnn of
                     PolyType_Mono [] m -> Just m
                     _                  -> Nothing
      -- Work on environment
      copy [e1, e2]
      env <- use (this.inh_.theEnv.fnE)
      -- Change second part environment, now we have the type!
      at e2 . inh_ . theEnv . fnE %= ((translate x, tyAnn) : )
      -- Create the output script
      e1Syn <- use (at e1 . syn)
      e2Syn <- use (at e2 . syn)
      this.syn .= mappend e1Syn e2Syn
      this.syn._Term.given .= case (isMono, e1Syn, e2Syn) of
        (Just _,  GatherTerm g1 _ _, GatherTerm g2 _ _) -> g1 ++ g2
        (Nothing, _                , GatherTerm g2 _ _) -> g2
        _ -> thisIsNotOk
      this.syn._Term.me .= [theThing]
      this.syn._Term.wanted .=. case (e1Syn, e2Syn) of
        (GatherTerm g1 [ity1] [i1], GatherTerm _g2 [ity2] [i2]) -> do
          GatherTermInfo w1 c1 cv1 <- i1
          GatherTermInfo w2 c2 cv2 <- i2
          return $ GatherTermInfo { tree = case isMono of
                                      Just m  -> Join [ w1
                                                      , SingUnifyC (var (ty ity1)) m p, w2
                                                      , SingUnifyC (var thisTy) (var (ty ity2)) p ] p
                                      Nothing -> let vars = insert (ty ity1) (fvScript w1) \\ nub (fv env)
                                                  in Join [ Exists vars (q1 ++ g1)
                                                                   (Join [ w1, SingUnifyC (var (ty ity1)) t1 p ] p) p
                                                          , w2, SingUnifyC (var thisTy) (var (ty ity2)) p ] p
                                  , custom = c1 ++ c2
                                  , customVars = cv1 `union` cv2
                                  }
        _ -> thisIsNotOk

matchRule :: TypeRule
matchRule = rule $ \(e, branches) ->
  inj (UTerm_Match_ (e <<- any_) __ __ [branches <<- any_] __) ->>> \theThing@(UTerm_Match _ k mk _ (p,thisTy)) -> do
        copy [e]
        copy [branches]
        env <- use (this.inh_.theEnv.fnE)
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
              [] -> g ++ concatMap (fst . fromJust) caseInfos
              _ -> thisIsNotOk
          _ -> thisIsNotOk
        this.syn._Term.me .= [theThing]
        -- And now the wanted part
        this.syn._Term.wanted .=. case (einfo, binfo, mk) of
          (GatherTerm _ [te] [i], GatherCase cases, Just mko) ->
            let caseInfos = map (generateCase (nub (fv env)) thisTy p mko) cases in
            case filter (is _Nothing) caseInfos of
              [] -> do GatherTermInfo we c cv <- i
                       caseInfosJust <- sequence $ map (snd . fromJust) caseInfos
                       let (caseWs, caseCs, caseCVs) = unzip3 caseInfosJust
                       return $ GatherTermInfo { tree = AsymJoin (Join (we : caseWs) p)
                                                                 (SingUnifyC (var (ty te)) mko p) p
                                               , custom = c ++ concat caseCs
                                               , customVars = cv ++ concat caseCVs
                                               }
              _ -> thisIsNotOk
          _ -> thisIsNotOk

generateCase :: [TyVar] -> TyVar -> (SourcePos,SourcePos) -> MonoType -> GatherCaseInfo
             -> Maybe ([Constraint], FreshM (TyScript, [Constraint], [TyVar]))
-- generateCase envVars thisTy p (MonoType_Con k vars) (GatherCaseInfo g betaVars q (MonoType_Con kc varsc) s c cv caseTy)
generateCase envVars thisTy p (MonoType_Con k vars) (GatherCaseInfo g betaVars q (MonoType_Con kc varsc) sc caseTy)
  | k == kc, [] <- betaVars, [] <- q =
     Just (g, do GatherTermInfo s c cv <- sc
                 return ( AsymJoin (foldr (\(MonoType_Var v1, v2) curS -> substScript v1 v2 curS) s (zip varsc vars))
                                   (SingUnifyC (var thisTy) (var caseTy) p) p
                        , c, cv) )
  | k == kc =  -- Existential case
     Just ([], do GatherTermInfo s c _cv <- sc
                  let evars = nub (union (fv varsc) (fvScript s)) \\ union envVars (fv vars)
                  return ( Exists evars (g ++ q ++ zipWith Constraint_Unify vars varsc)
                                  (AsymJoin (foldr (\(MonoType_Var v1, v2) curS -> substScript v1 v2 curS) s (zip varsc vars))
                                            (SingUnifyC (var thisTy) (var caseTy) p) p) p
                         , c, [] ) )
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
    at e . inh_ . theEnv . fnE %= case caseTy' of
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
        GatherTerm g [eTy] [i] ->
          let -- resultC = Singleton (Constraint_Unify (var thisTy) (var eTy)) (Just p, Nothing)
              betaVars    = boundvars \\ fv convars
           in GatherCase [GatherCaseInfo g betaVars q (MonoType_Con dname convars) i (ty eTy)]
        _ -> thisIsNotOk

thisIsNotOk :: a
thisIsNotOk = error "This should never happen"
