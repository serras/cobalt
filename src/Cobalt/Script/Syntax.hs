{-# LANGUAGE DeriveGeneric #-}
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
module Cobalt.Script.Syntax (
  UCaseAlternative(..)
, UTerm_(..)
, UTerm
, UTermVar
, AnnUTerm
, pattern UTerm_IntLiteral
, pattern UTerm_Var
, pattern UTerm_Abs
, pattern UTerm_AbsAnn
, pattern UTerm_App
, pattern UTerm_Let
, pattern UTerm_LetAnn
, pattern UTerm_Match
, unbindTerm
, tyvared
, ann
, atUAnn
) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Data.Foldable
import Data.Traversable (traverse)
import Data.Regex.Generics hiding (var)
import qualified GHC.Generics as G
import Unbound.LocallyNameless hiding (close)

import Cobalt.Language.Syntax
import Cobalt.Types

data UTerm_ t (f :: *)
  = UTerm_IntLiteral_ Integer t
  | UTerm_Var_    (UTermVar t) t
  | UTerm_Abs_    (UTermVar t) t f t
  | UTerm_AbsAnn_ (UTermVar t) t f PolyType t
  | UTerm_App_    f f t
  | UTerm_Let_    (UTermVar t) f f t
  | UTerm_LetAnn_ (UTermVar t) f f PolyType t
  | UTerm_Match_  f String [UCaseAlternative t f] t
  deriving (Show, G.Generic1)

data UCaseAlternative t f = UCaseAlternative (UTermVar t) [UTermVar t] f t
  deriving (Show, Functor, Foldable)

type UTerm t    = Fix (UTerm_ t)
type UTermVar t = Name (UTerm t)

type AnnUTerm t = Fix (UTerm_ ((SourcePos,SourcePos),t))

pattern UTerm_IntLiteral n   a = Fix (UTerm_IntLiteral_ n a)
pattern UTerm_Var v          a = Fix (UTerm_Var_ v a)
pattern UTerm_Abs v i e      a = Fix (UTerm_Abs_ v i e a)
pattern UTerm_AbsAnn v i p e a = Fix (UTerm_AbsAnn_ v i p e a)
pattern UTerm_App e1 e2      a = Fix (UTerm_App_ e1 e2 a)
pattern UTerm_Let v b e      a = Fix (UTerm_Let_ v b e a)
pattern UTerm_LetAnn v b e p a = Fix (UTerm_LetAnn_ v b e p a)
pattern UTerm_Match e k cs   a = Fix (UTerm_Match_ e k cs a)

unbindTerm :: Alpha t => Term t -> FreshM (UTerm t)
unbindTerm (Term_IntLiteral n a) = return $ UTerm_IntLiteral n a
unbindTerm (Term_Var v a)        = return $ UTerm_Var (translate v) a
unbindTerm (Term_Abs b i a)      = do (v,e) <- unbind b
                                      e_ <- unbindTerm e
                                      return $ UTerm_Abs (translate v) i e_ a
unbindTerm (Term_AbsAnn b i p a) = do (v,e) <- unbind b
                                      e_ <- unbindTerm e
                                      return $ UTerm_AbsAnn (translate v) i e_ p a
unbindTerm (Term_App e1 e2 a)    = UTerm_App <$> unbindTerm e1
                                             <*> unbindTerm e2
                                             <*> pure a
unbindTerm (Term_Let b a)        = do ((v, unembed -> e1),e2) <- unbind b
                                      e1_ <- unbindTerm e1
                                      e2_ <- unbindTerm e2
                                      return $ UTerm_Let (translate v) e1_ e2_ a
unbindTerm (Term_LetAnn b p a)   = do ((v, unembed -> e1),e2) <- unbind b
                                      e1_ <- unbindTerm e1
                                      e2_ <- unbindTerm e2
                                      return $ UTerm_LetAnn (translate v) e1_ e2_ p a
unbindTerm (Term_Match e k cs a) = do us <- mapM (\(v,b,t) -> do
                                                    (vs,inner) <- unbind b
                                                    inner_ <- unbindTerm inner
                                                    return $ UCaseAlternative (translate v)
                                                                              (map translate vs)
                                                                              inner_ t) cs
                                      e_ <- unbindTerm e
                                      return $ UTerm_Match e_ k us a

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
tyvared (UTerm_Match e k us a)     = UTerm_Match <$> tyvared e <*> pure k
                                                 <*> traverse caseTyvared us <*> upgrade a
  where caseTyvared (UCaseAlternative v vs inner t) = UCaseAlternative <$> pure (translate v)
                                                                       <*> pure (map translate vs)
                                                                       <*> tyvared inner
                                                                       <*> upgrade t
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
ann (UTerm_Match _ _ _ a)    = a
ann _ = error "You should never get here"

atUAnn :: Rep b => (a -> b) -> UTerm a -> UTerm b
atUAnn f (UTerm_IntLiteral n a)     = UTerm_IntLiteral n (f a)
atUAnn f (UTerm_Var v a)            = UTerm_Var (translate v) (f a)
atUAnn f (UTerm_Abs x xa e a)       = UTerm_Abs (translate x) (f xa) (atUAnn f e) (f a)
atUAnn f (UTerm_AbsAnn x xa e p a)  = UTerm_AbsAnn (translate x) (f xa) (atUAnn f e) p (f a)
atUAnn f (UTerm_App e1 e2 a)        = UTerm_App (atUAnn f e1) (atUAnn f e2) (f a)
atUAnn f (UTerm_Let x e1 e2 a)      = UTerm_Let (translate x) (atUAnn f e1) (atUAnn f e2) (f a)
atUAnn f (UTerm_LetAnn x e1 e2 p a) = UTerm_LetAnn (translate x) (atUAnn f e1) (atUAnn f e2) p (f a)
atUAnn f (UTerm_Match e k us a)     = UTerm_Match (atUAnn f e) k (map atAnnAlternative us) (f a)
  where atAnnAlternative (UCaseAlternative v vs i b) =
          UCaseAlternative (translate v) (map translate vs) (atUAnn f i) (f b)
atUAnn _ _ = error "You should never get here"


-- INSTANCES FOR GENERICS LIBRARIES
-- ================================

-- Hand-written `RepLib` instance for `unbound`
instance Rep t => Rep (UTerm t) where
  rep = Data (DT "UTerm" ((rep :: R t) :+: MNil))
             [ Con rIntLiteral ((rep :: R Integer) :+: (rep :: R t) :+: MNil)
             , Con rTermVar    ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbs    ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbsAnn ((rep :: R (UTermVar t)) :+: (rep :: R t) :+: (rep :: R (UTerm t)) :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermApp    ((rep :: R (UTerm t)) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLet    ((rep :: R (UTermVar t)) :+: (rep :: R (UTerm t)) :+: (rep :: R (UTerm t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLetAnn ((rep :: R (UTermVar t)) :+: (rep :: R (UTerm t)) :+: (rep :: R (UTerm t))
                                :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermMatch  ((rep :: R (UTerm t)) :+: (rep :: R String)
                                :+: (rep :: R [UCaseAlternative t (UTerm t)]) :+: (rep :: R t) :+: MNil)
             ]

instance (Rep t, Rep f) => Rep (UCaseAlternative t f) where
  rep = Data (DT "UCaseAlternative" ((rep :: R t) :+: (rep :: R f) :+: MNil))
             [ Con rCaseAlternative ((rep :: R (UTermVar t)) :+: (rep :: R [UTermVar t]) :+: (rep :: R f) :+: (rep :: R t) :+: MNil) ]

instance ( Rep t, Sat (ctx t), Sat (ctx (UTerm t)), Sat (ctx (UTermVar t))
         , Sat (ctx Integer), Sat (ctx String), Sat (ctx PolyType)
         , Sat (ctx [UCaseAlternative t (UTerm t)]) ) => Rep1 ctx (UTerm t) where
  rep1 = rAnnTerm1 dict dict dict dict dict dict dict

rAnnTerm1 :: forall t ctx. Rep t
          => ctx t -> ctx (UTerm t) -> ctx (UTermVar t)
          -> ctx Integer -> ctx String -> ctx PolyType
          -> ctx [UCaseAlternative t (UTerm t)] -> R1 ctx (UTerm t)
rAnnTerm1 ct ctt ctv ci cs cp cbl =
  Data1 (DT "UTerm" ((rep :: R t) :+: MNil))
        [ Con rIntLiteral (ci  :+: ct :+: MNil)
        , Con rTermVar    (ctv :+: ct :+: MNil)
        , Con rTermAbs    (ctv :+: ct :+: ctt :+: ct :+: MNil)
        , Con rTermAbsAnn (ctv :+: ct :+: ctt :+: cp :+: ct :+: MNil)
        , Con rTermApp    (ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLet    (ctv :+: ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLetAnn (ctv :+: ctt :+: ctt :+: cp :+: ct :+: MNil)
        , Con rTermMatch  (ctt :+: cs :+: cbl :+: ct :+: MNil)
        ]

instance ( Rep t, Rep f, Sat (ctx t), Sat (ctx f)
         , Sat (ctx (UTermVar t)), Sat (ctx [UTermVar t]) )
         => Rep1 ctx (UCaseAlternative t f) where
  rep1 = rCaseAlt1 dict dict dict dict

rCaseAlt1 :: forall t f ctx. (Rep t, Rep f)
          => ctx t -> ctx f -> ctx (UTermVar t) -> ctx [UTermVar t]
          -> R1 ctx (UCaseAlternative t f)
rCaseAlt1 ct cf cv cvv =
  Data1 (DT "UCaseAlternative" ((rep :: R t) :+: (rep :: R f) :+: MNil))
        [ Con rCaseAlternative (cv :+: cvv :+: cf :+: ct :+: MNil) ]

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

rTermAbsAnn :: Emb (UTermVar t :*: t :*: UTerm t :*: PolyType :*: t :*: Nil) (UTerm t)
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

rTermLetAnn :: Emb (UTermVar t :*: UTerm t :*: UTerm t :*: PolyType :*: t :*: Nil) (UTerm t)
rTermLetAnn = Emb { to = \(v :*: e :*: b :*: p :*: t :*: Nil) -> UTerm_LetAnn v e b p t
                  , from = \x -> case x of
                                  UTerm_LetAnn v e b p t -> Just (v :*: e :*: b :*: p :*: t :*: Nil)
                                  _                       -> Nothing
                  , labels = Nothing
                  , name = "UTerm_LetAnn"
                  , fixity = Nonfix
                  }

rTermMatch :: Emb (UTerm t :*: String :*: [UCaseAlternative t (UTerm t)] :*: t :*: Nil) (UTerm t)
rTermMatch = Emb { to = \(e :*: c :*: alts :*: t :*: Nil) -> UTerm_Match e c alts t
                 , from = \x -> case x of
                                 UTerm_Match e c alts t -> Just (e :*: c :*: alts :*: t :*: Nil)
                                 _                      -> Nothing
                 , labels = Nothing
                 , name = "UTerm_Match"
                 , fixity = Nonfix
                 }

rCaseAlternative :: Emb (UTermVar t :*: [UTermVar t] :*: f :*: t :*: Nil) (UCaseAlternative t f)
rCaseAlternative = Emb { to = \(v :*: vs :*: e :*: t :*: Nil) -> UCaseAlternative v vs e t
                       , from = \(UCaseAlternative v vs e t) -> Just (v :*: vs :*: e :*: t :*: Nil)
                       , labels = Nothing
                       , name = "UCaseAlternative"
                       , fixity = Nonfix
                       }

instance Alpha t => Alpha (UTerm t)
instance Alpha t => Alpha (UCaseAlternative t (UTerm t))
instance ( Alpha t, Subst (UTerm t) t, Subst (UTerm t) (UCaseAlternative t (UTerm t))
         , Subst t Constraint, Subst t MonoType, Subst t PolyType ) => Subst (UTerm t) (UTerm t) where
  isvar (UTerm_Var v _) = Just (SubstName v)
  isvar _               = Nothing
instance (Alpha t, Subst t t, Subst t PolyType) => Subst t (UTerm t)
instance (Alpha t, Subst t t, Subst t PolyType) => Subst t (UCaseAlternative t (UTerm t))

instance (Subst t PolyType, Subst t Constraint, Subst t MonoType) => Subst (UTerm t) PolyType
instance (Subst t MonoType) => Subst (UTerm t) MonoType
instance (Subst t Constraint, Subst t PolyType, Subst t MonoType) => Subst (UTerm t) Constraint
