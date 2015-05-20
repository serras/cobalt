{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TupleSections #-}
module Cobalt.Language.UnboundSyntax (
  Ix(..)
, Sing(..)
, UnboundPolyType
, UTerm_(..)
, UTerm
, UTermVar
, UCaseAlternative
, AnnUTerm
, AnnUTermVar
, pattern UTerm_IntLiteral
, pattern UTerm_StrLiteral
, pattern UTerm_Var
, pattern UTerm_Abs
, pattern UTerm_AbsAnn
, pattern UTerm_App
, pattern UTerm_Let
, pattern UTerm_LetAnn
, pattern UTerm_Match
, pattern UCaseAlternative
, unbindTerm
, tyvared
, ann
, atUAnn
) where

#if MIN_VERSION_base(4,8,0)
#else
import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Data.Traversable (traverse)
#endif
import Data.List (intercalate)
import Data.MultiGenerics
-- import Text.Parsec.Pos (SourcePos)
import Unbound.LocallyNameless hiding (close)

import Cobalt.Core
import Cobalt.Language.Syntax

data Ix = IsATerm | IsACaseAlternative
data instance Sing (a :: Ix) where
  SIsATerm            :: Sing 'IsATerm
  SIsACaseAlternative :: Sing 'IsACaseAlternative
deriving instance Eq (Sing (a :: Ix))

instance SingI 'IsATerm where
  sing = SIsATerm
instance SingI 'IsACaseAlternative where
  sing = SIsACaseAlternative

type UnboundPolyType = (PolyType, ([Constraint], MonoType, [TyVar]))

data UTerm_ t (f :: Ix -> *) (ix :: Ix) where
  UTerm_IntLiteral_ :: Integer -> t -> UTerm_ t f 'IsATerm
  UTerm_Var_        :: UTermVar t -> t -> UTerm_ t f 'IsATerm
  UTerm_Abs_        :: UTermVar t -> t -> f 'IsATerm -> t -> UTerm_ t f 'IsATerm
  UTerm_AbsAnn_     :: UTermVar t -> t -> f 'IsATerm -> UnboundPolyType -> t -> UTerm_ t f 'IsATerm
  UTerm_App_        :: f 'IsATerm -> f 'IsATerm -> t -> UTerm_ t f 'IsATerm
  UTerm_Let_        :: UTermVar t -> f 'IsATerm -> f 'IsATerm -> t -> UTerm_ t f 'IsATerm
  UTerm_LetAnn_     :: UTermVar t -> f 'IsATerm -> f 'IsATerm -> UnboundPolyType -> t -> UTerm_ t f 'IsATerm
  UTerm_Match_      :: f 'IsATerm -> String -> Maybe MonoType -> [f 'IsACaseAlternative] -> t -> UTerm_ t f 'IsATerm
  UTerm_StrLiteral_ :: String -> t -> UTerm_ t f 'IsATerm
  UCaseAlternative_ :: UTermVar t -> [UTermVar t] -> Maybe UnboundPolyType -> f 'IsATerm -> t -> UTerm_ t f 'IsACaseAlternative

type UTerm t = Fix (UTerm_ t) 'IsATerm
type UTermVar t = Name (UTerm t)
type UCaseAlternative t = Fix (UTerm_ t) 'IsACaseAlternative

instance Show t => Show (UTerm t) where
  show = intercalate "\n" . showL
instance Show t => Show (UCaseAlternative t) where
  show = intercalate "\n" . showU

showL :: Show t => UTerm t -> [String]
showL (UTerm_IntLiteral n a)   = [show n ++ " => " ++ show a]
showL (UTerm_Var v a)          = [show v ++ " => " ++ show a]
showL (UTerm_Abs v i e a)      =
  ("\\(" ++ show v ++ " => " ++ show i ++ ") => " ++ show a) : (map ("  " ++) (showL e))
showL (UTerm_AbsAnn v i e p a) =
  ("\\(" ++ show v ++ " :: " ++ show p ++ " => " ++ show i ++ ") => " ++ show a) : (map ("  " ++) (showL e))
showL (UTerm_App e1 e2 a) =
  ("@ => " ++ show a) : map ("  " ++) (showL e1 ++ showL e2)
showL (UTerm_Let v b e a) =
  ["let " ++ show v ++ " = "] ++ map ("  " ++) (showL b)
  ++ ["in => " ++ show a] ++ map ("  " ++) (showL e)
showL (UTerm_LetAnn v b e p a) =
  ["let " ++ show v ++ " :: " ++ show p ++ " = "] ++ map ("  " ++) (showL b)
  ++ ["in => " ++ show a] ++ map ("  " ++) (showL e)
showL (UTerm_Match e k _ cs a) =
  ["match "] ++ map ("  " ++) (showL e)
  ++ ["with " ++ k ++ " => " ++ show a] ++ concatMap showU cs
showL (UTerm_StrLiteral n a)   = ["\"" ++ show n ++ "\" => " ++ show a]
showL _ = error "You should never get here"

showU :: Show t => UCaseAlternative t -> [String]
showU (UCaseAlternative k vs _ e a) =
  ("| " ++ intercalate " " (map show (k:vs)) ++ " => " ++ show a) : map ("  " ++) (showL e)
showU _ = error "You should never get here"

type AnnUTerm t = Fix (UTerm_ ((SourcePos,SourcePos),t)) 'IsATerm
type AnnUTermVar t = Name (AnnUTerm t)

pattern UTerm_IntLiteral n        a = Fix (UTerm_IntLiteral_ n a)
pattern UTerm_Var v               a = Fix (UTerm_Var_ v a)
pattern UTerm_Abs v i e           a = Fix (UTerm_Abs_ v i e a)
pattern UTerm_AbsAnn v i p e      a = Fix (UTerm_AbsAnn_ v i p e a)
pattern UTerm_App e1 e2           a = Fix (UTerm_App_ e1 e2 a)
pattern UTerm_Let v b e           a = Fix (UTerm_Let_ v b e a)
pattern UTerm_LetAnn v b e p      a = Fix (UTerm_LetAnn_ v b e p a)
pattern UTerm_Match e k dt cs     a = Fix (UTerm_Match_ e k dt cs a)
pattern UTerm_StrLiteral n        a = Fix (UTerm_StrLiteral_ n a)
pattern UCaseAlternative k vs p e a = Fix (UCaseAlternative_ k vs p e a)

splitPlus :: PolyType -> FreshM UnboundPolyType
splitPlus p = (p,) <$> split p

splitNormaal :: PolyType -> FreshM UnboundPolyType
splitNormaal p = do
  (q,arr -> (args,result),v) <- split p
  (newResult, newQs, newVars) <- normaalResult result
  return (p, (q ++ newQs, unarr args newResult, v ++ newVars))

normaalResult :: MonoType -> FreshM (MonoType, [Constraint], [TyVar])
normaalResult (MonoType_Con k vs) = do (vs2, q, tyv) <- normaalResultVars vs
                                       return (MonoType_Con k vs2, q, tyv)
  where normaalResultVars [] = return ([], [], [])
        normaalResultVars (v@(MonoType_Var _) : r) = do (r2, q, tyv) <- normaalResultVars r
                                                        return (v : r2, q, tyv)
        normaalResultVars (m : r) = do (r2, q, tyv) <- normaalResultVars r
                                       x <- fresh (s2n "a")
                                       return (var x : r2, Constraint_Unify (var x) m : q, x : tyv)
normaalResult other = return (other, [], [])

-- Note: we need the FnEnv to be able to find the type in constructors.
unbindTerm :: Alpha t => Term t -> FnEnv -> DataEnv -> FreshM (UTerm t)
unbindTerm (Term_IntLiteral n a) _  _  = return $ UTerm_IntLiteral n a
unbindTerm (Term_Var v a)        _  _  = return $ UTerm_Var (translate v) a
unbindTerm (Term_Abs b i a)      nv dv = do (v,e) <- unbind b
                                            e_ <- unbindTerm e nv dv
                                            return $ UTerm_Abs (translate v) i e_ a
unbindTerm (Term_AbsAnn b i p a) nv dv = do (v,e) <- unbind b
                                            e_ <- unbindTerm e nv dv
                                            p_ <- splitPlus p
                                            return $ UTerm_AbsAnn (translate v) i e_ p_ a
unbindTerm (Term_App e1 e2 a)    nv dv = UTerm_App <$> unbindTerm e1 nv dv
                                                   <*> unbindTerm e2 nv dv
                                                   <*> pure a
unbindTerm (Term_Let b a)        nv dv = do ((v, unembed -> e1),e2) <- unbind b
                                            e1_ <- unbindTerm e1 nv dv
                                            e2_ <- unbindTerm e2 nv dv
                                            return $ UTerm_Let (translate v) e1_ e2_ a
unbindTerm (Term_LetAnn b p a)   nv dv = do ((v, unembed -> e1),e2) <- unbind b
                                            e1_ <- unbindTerm e1 nv dv
                                            e2_ <- unbindTerm e2 nv dv
                                            p_ <- splitPlus p
                                            return $ UTerm_LetAnn (translate v) e1_ e2_ p_ a
unbindTerm (Term_Match e k cs a) nv dv = do us <- mapM (\x -> unbindCase x nv dv) cs
                                            e_ <- unbindTerm e nv dv
                                            dt_ <- case lookup k dv of
                                              Just vars -> Just <$> (MonoType_Con k <$> (map var <$> mapM fresh vars))
                                              Nothing -> return Nothing
                                            return $ UTerm_Match e_ k dt_ us a
unbindTerm (Term_StrLiteral n a) _  _  = return $ UTerm_StrLiteral n a
-- unbindTerm _ = error "You should never get here"

unbindCase :: Alpha t => (TermVar t, Bind [TermVar t] (Term t), t) -> FnEnv -> DataEnv -> FreshM (UCaseAlternative t)
unbindCase (v,b,a) nv dv = do (vs, inner) <- unbind b
                              inner_ <- unbindTerm inner nv dv
                              p_ <- case lookup (translate v) nv of
                                      Nothing -> return Nothing
                                      Just p  -> Just <$> splitNormaal p
                              return $ UCaseAlternative (translate v) (map translate vs) p_ inner_ a

tyvared :: (Applicative m, Fresh m, Rep t) => UTerm t -> m (UTerm (t,TyVar))
tyvared (UTerm_IntLiteral n a)     = UTerm_IntLiteral <$> pure n <*> upgrade a
tyvared (UTerm_Var v a)            = UTerm_Var <$> pure (translate v) <*> upgrade a
tyvared (UTerm_Abs v i e a)        = UTerm_Abs <$> pure (translate v) <*> upgrade i
                                               <*> tyvared e <*> upgrade a
tyvared (UTerm_AbsAnn v i e p a)   = UTerm_AbsAnn <$> pure (translate v) <*> upgrade i <*> tyvared e
                                                  <*> pure p <*> upgrade a
tyvared (UTerm_App e1 e2 a)        = UTerm_App <$> tyvared e1 <*> tyvared e2 <*> upgrade a
tyvared (UTerm_Let v e1 e2 a)      = UTerm_Let <$> pure (translate v) <*> tyvared e1
                                               <*> tyvared e2 <*> upgrade a
tyvared (UTerm_LetAnn v e1 e2 p a) = UTerm_LetAnn <$> pure (translate v) <*> tyvared e1
                                                  <*> tyvared e2 <*> pure p <*> upgrade a
tyvared (UTerm_StrLiteral n a)     = UTerm_StrLiteral <$> pure n <*> upgrade a
tyvared (UTerm_Match e k dt us a)  = UTerm_Match <$> tyvared e <*> pure k <*> pure dt
                                                 <*> traverse caseTyvared us <*> upgrade a
  where caseTyvared (UCaseAlternative v vs p inner t) = UCaseAlternative <$> pure (translate v)
                                                                         <*> pure (map translate vs)
                                                                         <*> pure p
                                                                         <*> tyvared inner
                                                                         <*> upgrade t
        caseTyvared _ = error "You should never get here"
tyvared _ = error "You should never get here"

upgrade :: (Applicative m, Fresh m) => t -> m (t,TyVar)
upgrade t = (,) <$> pure t <*> fresh (s2n "t")

ann :: UTerm t -> t
ann (UTerm_IntLiteral _ a)   = a
ann (UTerm_Var _ a)          = a
ann (UTerm_Abs _ _ _ a)      = a
ann (UTerm_AbsAnn _ _ _ _ a) = a
ann (UTerm_App _ _ a)        = a
ann (UTerm_Let _ _ _ a)      = a
ann (UTerm_LetAnn _ _ _ _ a) = a
ann (UTerm_Match _ _ _ _ a)  = a
ann (UTerm_StrLiteral _ a)   = a
ann _ = error "You should never get here"

atUAnn :: Rep b => (a -> b) -> UTerm a -> UTerm b
atUAnn f (UTerm_IntLiteral n a)     = UTerm_IntLiteral n (f a)
atUAnn f (UTerm_Var v a)            = UTerm_Var (translate v) (f a)
atUAnn f (UTerm_Abs x xa e a)       = UTerm_Abs (translate x) (f xa) (atUAnn f e) (f a)
atUAnn f (UTerm_AbsAnn x xa e p a)  = UTerm_AbsAnn (translate x) (f xa) (atUAnn f e) p (f a)
atUAnn f (UTerm_App e1 e2 a)        = UTerm_App (atUAnn f e1) (atUAnn f e2) (f a)
atUAnn f (UTerm_Let x e1 e2 a)      = UTerm_Let (translate x) (atUAnn f e1) (atUAnn f e2) (f a)
atUAnn f (UTerm_LetAnn x e1 e2 p a) = UTerm_LetAnn (translate x) (atUAnn f e1) (atUAnn f e2) p (f a)
atUAnn f (UTerm_Match e k dt us a)  = UTerm_Match (atUAnn f e) k dt (map atAnnAlternative us) (f a)
  where atAnnAlternative (UCaseAlternative v vs p i b) =
          UCaseAlternative (translate v) (map translate vs) p (atUAnn f i) (f b)
        atAnnAlternative _ = error "You should never get here"
atUAnn f (UTerm_StrLiteral n a)     = UTerm_StrLiteral n (f a)
atUAnn _ _ = error "You should never get here"


-- INSTANCES FOR GENERICS LIBRARIES
-- ================================

-- | Implementation of 'Generic1m' for 'UTerm_'.
--   This is required to use tree regular expressions.
instance Generic1m (UTerm_ t) where
  type Rep1m (UTerm_ t) =
         Tag1m (K1m () Integer :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: K1m () t :**: Par1m 'IsATerm :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: K1m () t :**: Par1m 'IsATerm :**: K1m () UnboundPolyType :**: K1m () t) 'IsATerm
    :++: Tag1m (Par1m 'IsATerm :**: Par1m 'IsATerm :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: Par1m 'IsATerm :**: Par1m 'IsATerm :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: Par1m 'IsATerm :**: Par1m 'IsATerm :**: K1m () UnboundPolyType :**: K1m () t) 'IsATerm
    :++: Tag1m (Par1m 'IsATerm :**: K1m () String :**: K1m () (Maybe MonoType) :**: Rec1m [] 'IsACaseAlternative :**: K1m () t) 'IsATerm
    :++: Tag1m (K1m () (UTermVar t) :**: K1m () [UTermVar t] :**: K1m () (Maybe UnboundPolyType) :**: Par1m 'IsATerm :**: K1m () t) 'IsACaseAlternative
    :++: Tag1m (K1m () String :**: K1m () t) 'IsATerm

  from1k (UTerm_IntLiteral_ n        a) = L1m $ Tag1m (K1m n :**: K1m a)
  from1k (UTerm_Var_ v               a) = R1m $ L1m $ Tag1m (K1m v :**: K1m a)
  from1k (UTerm_Abs_ x va e          a) = R1m $ R1m $ L1m $ Tag1m (K1m x :**: K1m va :**: Par1m e :**: K1m a)
  from1k (UTerm_AbsAnn_ x va e p     a) = R1m $ R1m $ R1m $ L1m $ Tag1m (K1m x :**: K1m va :**: Par1m e :**: K1m p :**: K1m a)
  from1k (UTerm_App_ e1 e2           a) = R1m $ R1m $ R1m $ R1m $ L1m $ Tag1m (Par1m e1 :**: Par1m e2 :**: K1m a)
  from1k (UTerm_Let_ x e1 e2         a) = R1m $ R1m $ R1m $ R1m $ R1m $ L1m $ Tag1m (K1m x :**: Par1m e1 :**: Par1m e2 :**: K1m a)
  from1k (UTerm_LetAnn_ x e1 e2 p    a) = R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ L1m $ Tag1m (K1m x :**: Par1m e1 :**: Par1m e2 :**: K1m p :**: K1m a)
  from1k (UTerm_Match_ e k dt cs     a) = R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ L1m $ Tag1m (Par1m e :**: K1m k :**: K1m dt :**:  Rec1m cs :**: K1m a)
  from1k (UCaseAlternative_ v vs p e a) = R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ L1m $ Tag1m (K1m v :**: K1m vs :**: K1m p :**: Par1m e :**: K1m a)
  from1k (UTerm_StrLiteral_ n        a) = R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ R1m $ Tag1m (K1m n :**: K1m a)

  to1k (L1m (Tag1m (K1m n :**: K1m a))) = UTerm_IntLiteral_ n a
  to1k (R1m (L1m (Tag1m (K1m v :**: K1m a)))) = UTerm_Var_ v a
  to1k (R1m (R1m (L1m (Tag1m (K1m x :**: K1m va :**: Par1m e :**: K1m a))))) = UTerm_Abs_ x va e a
  to1k (R1m (R1m (R1m (L1m (Tag1m (K1m x :**: K1m va :**: Par1m e :**: K1m p :**: K1m a)))))) = UTerm_AbsAnn_ x va e p a
  to1k (R1m (R1m (R1m (R1m (L1m (Tag1m (Par1m e1 :**: Par1m e2 :**: K1m a))))))) = UTerm_App_ e1 e2 a
  to1k (R1m (R1m (R1m (R1m (R1m (L1m (Tag1m (K1m x :**: Par1m e1 :**: Par1m e2 :**: K1m a)))))))) = UTerm_Let_ x e1 e2 a
  to1k (R1m (R1m (R1m (R1m (R1m (R1m (L1m (Tag1m (K1m x :**: Par1m e1 :**: Par1m e2 :**: K1m p :**: K1m a))))))))) = UTerm_LetAnn_ x e1 e2 p a
  to1k (R1m (R1m (R1m (R1m (R1m (R1m (R1m (L1m (Tag1m (Par1m e :**: K1m k :**: K1m dt :**: Rec1m cs :**: K1m a)))))))))) = UTerm_Match_ e k dt cs a
  to1k (R1m (R1m (R1m (R1m (R1m (R1m (R1m (R1m (L1m (Tag1m (K1m v :**: K1m vs :**: K1m p :**: Par1m e :**: K1m a))))))))))) = UCaseAlternative_ v vs p e a
  to1k (R1m (R1m (R1m (R1m (R1m (R1m (R1m (R1m (R1m (Tag1m (K1m n :**: K1m a))))))))))) = UTerm_StrLiteral_ n a

-- Hand-written `RepLib` instance for `unbound`
instance Rep t => Rep (UTerm t) where
  rep = Data (DT "UTerm" ((rep :: R t) :+: MNil))
             [ Con rIntLiteral ((rep :: R Integer) :+: (rep :: R t) :+: MNil)
             , Con rTermVar    ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbs    ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbsAnn ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: (rep :: R (UTerm t))
                                :+: (rep :: R UnboundPolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermApp    ((rep :: R (UTerm t)) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLet    ((rep :: R (UTermVar t)) :+: (rep :: R (UTerm t)) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLetAnn ((rep :: R (UTermVar t)) :+: (rep :: R (UTerm t)) :+: (rep :: R (UTerm t))
                                :+: (rep :: R UnboundPolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermMatch  ((rep :: R (UTerm t)) :+: (rep :: R String) :+: (rep :: R (Maybe MonoType))
                                :+: (rep :: R [UCaseAlternative t]) :+: (rep :: R t) :+: MNil)
             , Con rStrLiteral ((rep :: R String) :+: (rep :: R t) :+: MNil)
             ]

instance (Rep t) => Rep (UCaseAlternative t) where
  rep = Data (DT "UCaseAlternative" ((rep :: R t) :+: MNil))
             [ Con rCaseAlternative ((rep :: R (UTermVar t)) :+: (rep :: R [UTermVar t])
                                     :+: (rep :: R (Maybe UnboundPolyType)) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil) ]

instance ( Rep t, Sat (ctx t), Sat (ctx (UTerm t)), Sat (ctx (UTermVar t))
         , Sat (ctx Integer), Sat (ctx String), Sat (ctx (Maybe MonoType)), Sat (ctx UnboundPolyType)
         , Sat (ctx [UCaseAlternative t]) ) => Rep1 ctx (UTerm t) where
  rep1 = rAnnTerm1 dict dict dict dict dict dict dict dict

rAnnTerm1 :: forall t ctx. Rep t
          => ctx t -> ctx (UTerm t) -> ctx (UTermVar t)
          -> ctx Integer -> ctx String -> ctx (Maybe MonoType) -> ctx UnboundPolyType
          -> ctx [UCaseAlternative t] -> R1 ctx (UTerm t)
rAnnTerm1 ct ctt ctv ci cs cm cp cbl =
  Data1 (DT "UTerm" ((rep :: R t) :+: MNil))
        [ Con rIntLiteral (ci  :+: ct :+: MNil)
        , Con rTermVar    (ctv :+: ct :+: MNil)
        , Con rTermAbs    (ctv :+: ct :+: ctt :+: ct :+: MNil)
        , Con rTermAbsAnn (ctv :+: ct :+: ctt :+: cp :+: ct :+: MNil)
        , Con rTermApp    (ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLet    (ctv :+: ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLetAnn (ctv :+: ctt :+: ctt :+: cp :+: ct :+: MNil)
        , Con rTermMatch  (ctt :+: cs :+: cm :+: cbl :+: ct :+: MNil)
        , Con rStrLiteral (cs  :+: ct :+: MNil)
        ]

instance ( Rep t, Sat (ctx t)
         , Sat (ctx (UTerm t)), Sat (ctx (UTermVar t)), Sat (ctx [UTermVar t])
         , Sat (ctx (Maybe UnboundPolyType)))
         => Rep1 ctx (UCaseAlternative t) where
  rep1 = rCaseAlt1 dict dict dict dict dict

rCaseAlt1 :: forall t ctx. Rep t
          => ctx t -> ctx (UTerm t) -> ctx (UTermVar t) -> ctx [UTermVar t]
          -> ctx (Maybe UnboundPolyType)
          -> R1 ctx (UCaseAlternative t)
rCaseAlt1 ct ctt cv cvv cup =
  Data1 (DT "UCaseAlternative" ((rep :: R t) :+: MNil))
        [ Con rCaseAlternative (cv :+: cvv :+: cup :+: ctt :+: ct :+: MNil) ]

rIntLiteral :: Emb (Integer :*: t :*: Nil) (UTerm t)
rIntLiteral = Emb { to = \(n :*: t :*: Nil) -> UTerm_IntLiteral n t
                  , from = \x -> case x of
                                   UTerm_IntLiteral n t -> Just (n :*: t :*: Nil)
                                   _                    -> Nothing
                  , labels = Nothing
                  , name = "UTerm_IntLiteral"
                  , fixity = Nonfix
                  }

rTermVar :: Emb ((UTermVar t) :*: t :*: Nil) (UTerm t)
rTermVar = Emb { to = \(v :*: t :*: Nil) -> UTerm_Var v t
               , from = \x -> case x of
                                UTerm_Var v t -> Just (v :*: t :*: Nil)
                                _             -> Nothing
               , labels = Nothing
               , name = "UTerm_Var"
               , fixity = Nonfix
               }

rTermAbs :: Emb (UTermVar t :*: t :*: UTerm t :*: t :*: Nil) (UTerm t)
rTermAbs = Emb { to = \(v :*: i :*: e :*: t :*: Nil) -> UTerm_Abs v i e t
               , from = \x -> case x of
                               UTerm_Abs v i e t -> Just (v :*: i :*: e :*: t :*: Nil)
                               _                 -> Nothing
               , labels = Nothing
               , name = "UTerm_Abs"
               , fixity = Nonfix
               }

rTermAbsAnn :: Emb (UTermVar t :*: t :*: UTerm t :*: UnboundPolyType :*: t :*: Nil) (UTerm t)
rTermAbsAnn = Emb { to = \(v :*: i :*: e :*: p :*: t :*: Nil) -> UTerm_AbsAnn v i e p t
                  , from = \x -> case x of
                                  UTerm_AbsAnn v i e p t -> Just (v :*: i :*: e :*: p :*: t :*: Nil)
                                  _                      -> Nothing
                  , labels = Nothing
                  , name = "UTerm_AbsAnn"
                  , fixity = Nonfix
                  }

rTermApp :: Emb (UTerm t :*: UTerm t :*: t :*: Nil) (UTerm t)
rTermApp = Emb { to = \(t1 :*: t2 :*: t :*: Nil) -> UTerm_App t1 t2 t
               , from = \x -> case x of
                               UTerm_App t1 t2 t -> Just (t1 :*: t2 :*: t :*: Nil)
                               _                 -> Nothing
               , labels = Nothing
               , name = "UTerm_App"
               , fixity = Nonfix
               }

rTermLet :: Emb (UTermVar t :*: UTerm t :*: UTerm t :*: t :*: Nil) (UTerm t)
rTermLet = Emb { to = \(v :*: e :*: b :*: t :*: Nil) -> UTerm_Let v e b t
               , from = \x -> case x of
                               UTerm_Let v e b t -> Just (v :*: e :*: b :*: t :*: Nil)
                               _                 -> Nothing
               , labels = Nothing
               , name = "UTerm_Let"
               , fixity = Nonfix
               }

rTermLetAnn :: Emb (UTermVar t :*: UTerm t :*: UTerm t :*: UnboundPolyType :*: t :*: Nil) (UTerm t)
rTermLetAnn = Emb { to = \(v :*: e :*: b :*: p :*: t :*: Nil) -> UTerm_LetAnn v e b p t
                  , from = \x -> case x of
                                  UTerm_LetAnn v e b p t -> Just (v :*: e :*: b :*: p :*: t :*: Nil)
                                  _                      -> Nothing
                  , labels = Nothing
                  , name = "UTerm_LetAnn"
                  , fixity = Nonfix
                  }

rTermMatch :: Emb (UTerm t :*: String :*: Maybe MonoType :*: [UCaseAlternative t] :*: t :*: Nil) (UTerm t)
rTermMatch = Emb { to = \(e :*: c :*: dt :*: alts :*: t :*: Nil) -> UTerm_Match e c dt alts t
                 , from = \x -> case x of
                                 UTerm_Match e c dt alts t -> Just (e :*: c :*: dt :*: alts :*: t :*: Nil)
                                 _                         -> Nothing
                 , labels = Nothing
                 , name = "UTerm_Match"
                 , fixity = Nonfix
                 }

rStrLiteral :: Emb (String :*: t :*: Nil) (UTerm t)
rStrLiteral = Emb { to = \(n :*: t :*: Nil) -> UTerm_StrLiteral n t
                  , from = \x -> case x of
                                   UTerm_StrLiteral n t -> Just (n :*: t :*: Nil)
                                   _                    -> Nothing
                  , labels = Nothing
                  , name = "UTerm_StrLiteral"
                  , fixity = Nonfix
                  }

rCaseAlternative :: Emb (UTermVar t :*: [UTermVar t] :*: Maybe UnboundPolyType :*: UTerm t :*: t :*: Nil) (UCaseAlternative t)
rCaseAlternative = Emb { to = \(v :*: vs :*: p :*: e :*: t :*: Nil) -> UCaseAlternative v vs p e t
                       , from = \(UCaseAlternative v vs p e t) -> Just (v :*: vs :*: p :*: e :*: t :*: Nil)
                       , labels = Nothing
                       , name = "UCaseAlternative"
                       , fixity = Nonfix
                       }

instance Alpha t => Alpha (UTerm t)
instance Alpha t => Alpha (UCaseAlternative t)
instance ( Alpha t, Subst (UTerm t) t, Subst (UTerm t) (UCaseAlternative t)
         , Subst t Constraint, Subst t MonoType, Subst t PolyType ) => Subst (UTerm t) (UTerm t) where
  isvar (UTerm_Var v _) = Just (SubstName v)
  isvar _               = Nothing
instance (Alpha t, Subst t t, Subst t Constraint, Subst t MonoType, Subst t PolyType) => Subst t (UTerm t)
instance (Alpha t, Subst t t, Subst t Constraint, Subst t MonoType, Subst t PolyType) => Subst t (UCaseAlternative t)

instance (Subst t PolyType, Subst t Constraint, Subst t MonoType) => Subst (UTerm t) PolyType
instance (Subst t MonoType) => Subst (UTerm t) MonoType
instance (Subst t Constraint, Subst t PolyType, Subst t MonoType) => Subst (UTerm t) Constraint
