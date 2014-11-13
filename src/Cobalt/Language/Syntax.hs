{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Cobalt.Language.Syntax (
  -- * Terms
  RawTermVar
, RawTerm
, TyTermVar
, TyTerm
  -- ** Generic annotated terms
, TermVar
, Term(..)
, atAnn
, getAnn
  -- * Whole program structure
  -- ** Environment
, FnEnv
, DataEnv
, initialDataEnv
, AxiomEnv
, Env(Env)
, fnE
, dataE
, axiomE
  -- * Definitions
, RawDefn
, TyDefn
) where

import Control.Lens hiding ((.=), from, to)
import Data.List (intercalate)
import Unbound.LocallyNameless hiding (close)

import Cobalt.Types

type RawTermVar = TermVar ()
type RawTerm    = Term ()
type TyTermVar  = TermVar MonoType
type TyTerm     = Term MonoType

type TermVar t = Name (Term t)
data Term t = Term_IntLiteral Integer t
            | Term_Var    (TermVar t) t
            | Term_Abs    (Bind (TermVar t) (Term t)) t
            | Term_AbsAnn (Bind (TermVar t) (Term t)) PolyType t
            | Term_App    (Term t) (Term t) t
            | Term_Let    (Bind ((TermVar t), Embed (Term t)) (Term t)) t
            | Term_LetAnn (Bind ((TermVar t), Embed (Term t)) (Term t)) PolyType t
            | Term_Match  (Term t) String [((TermVar t), Bind [TermVar t] (Term t))] t

atAnn :: (Alpha a, Alpha b) => (a -> b) -> Term a -> Term b
atAnn f = runFreshM . atAnn' f

atAnn' :: (Fresh m, Alpha a, Alpha b) => (a -> b) -> Term a -> m (Term b)
atAnn' f (Term_IntLiteral n t) = return $ Term_IntLiteral n (f t)
atAnn' f (Term_Var v t) = return $ Term_Var (translate v) (f t)
atAnn' f (Term_Abs b t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ Term_Abs (bind (translate x) inner) (f t)
atAnn' f (Term_AbsAnn b p t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ Term_AbsAnn (bind (translate x) inner) p (f t)
atAnn' f (Term_App a b t) = do
  e1 <- atAnn' f a
  e2 <- atAnn' f b
  return $ Term_App e1 e2 (f t)
atAnn' f (Term_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ Term_Let (bind (translate x, embed s1) s2) (f t)
atAnn' f (Term_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ Term_LetAnn (bind (translate x, embed s1) s2) p (f t)
atAnn' f (Term_Match e c bs t) = do
  e' <- atAnn' f e
  b' <- mapM (\(d,b) -> do (xs,expr) <- unbind b
                           expr' <- atAnn' f expr
                           return $ (translate d, bind (map translate xs) expr')) bs
  return $ Term_Match e' c b' (f t)

getAnn :: Term t -> t
getAnn (Term_IntLiteral _ t) = t
getAnn (Term_Var _ t)        = t
getAnn (Term_Abs _ t)        = t
getAnn (Term_AbsAnn _ _ t)   = t
getAnn (Term_App _ _ t)      = t
getAnn (Term_Let _ t)        = t
getAnn (Term_LetAnn _ _ t)   = t
getAnn (Term_Match _ _ _ t)  = t

type FnEnv    = [(RawTermVar, PolyType)]
type DataEnv  = [(String, [TyVar])]
type AxiomEnv = [Axiom]
data Env      = Env { _fnE    :: FnEnv
                    , _dataE  :: DataEnv
                    , _axiomE :: AxiomEnv }

$(makeLenses ''Env)

type RawDefn = (RawTermVar, RawTerm, Maybe PolyType)
type TyDefn  = (TyTermVar,  TyTerm,  PolyType)

initialDataEnv :: DataEnv
initialDataEnv = [("Int",     [])
                 ,("List",    [string2Name "a"])
                 ,("Tuple2",  [string2Name "a", string2Name "b"])]

-- Hand-written `RepLib` instance for `unbound`
instance Rep t => Rep (Term t) where
  rep = Data (DT "Term" ((rep :: R t) :+: MNil))
             [ Con rIntLiteral ((rep :: R Integer) :+: (rep :: R t) :+: MNil)
             , Con rTermVar    ((rep :: R (TermVar t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbs    ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R t) :+: MNil)
             , Con rTermAbsAnn ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermApp    ((rep :: R (Term t)) :+: (rep :: R (Term t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLet    ((rep :: R ((Bind ((TermVar t), Embed (Term t)) (Term t)))) :+: (rep :: R t) :+: MNil)
             , Con rTermLetAnn ((rep :: R ((Bind ((TermVar t), Embed (Term t)) (Term t)))) :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermMatch  ((rep :: R (Term t)) :+: (rep :: R String) :+: (rep :: R [((TermVar t), Bind [TermVar t] (Term t))]) :+: (rep :: R t) :+: MNil)
             ]

instance ( Rep t, Sat (ctx t), Sat (ctx (Term t)), Sat (ctx (TermVar t))
         , Sat (ctx Integer), Sat (ctx String), Sat (ctx PolyType)
         , Sat (ctx (Bind (TermVar t) (Term t))), Sat (ctx (Bind ((TermVar t), Embed (Term t)) (Term t)))
         , Sat (ctx [((TermVar t), Bind [TermVar t] (Term t))])) => Rep1 ctx (Term t) where
  rep1 = rAnnTerm1 dict dict dict dict dict dict dict dict dict

rAnnTerm1 :: forall t ctx. Rep t
          => ctx t -> ctx (Term t) -> ctx (TermVar t)
          -> ctx Integer -> ctx String -> ctx PolyType
          -> ctx (Bind (TermVar t) (Term t)) -> ctx (Bind ((TermVar t), Embed (Term t)) (Term t))
          -> ctx [((TermVar t), Bind [TermVar t] (Term t))] -> R1 ctx (Term t)
rAnnTerm1 ct ctt ctv ci cs cp cb1 cb2 cbl =
  Data1 (DT "Term" ((rep :: R t) :+: MNil))
        [ Con rIntLiteral (ci  :+: ct :+: MNil)
        , Con rTermVar    (ctv :+: ct :+: MNil)
        , Con rTermAbs    (cb1 :+: ct :+: MNil)
        , Con rTermAbsAnn (cb1 :+: cp :+: ct :+: MNil)
        , Con rTermApp    (ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLet    (cb2 :+: ct :+: MNil)
        , Con rTermLetAnn (cb2 :+: cp :+: ct :+: MNil)
        , Con rTermMatch  (ctt :+: cs :+: cbl :+: ct :+: MNil)
        ]

rIntLiteral :: Emb (Integer :*: t :*: Nil) (Term t)
rIntLiteral = Emb { to = \(n :*: t :*: Nil) -> Term_IntLiteral n t
                  , from = \x -> case x of
                                   Term_IntLiteral n t -> Just (n :*: t :*: Nil)
                                   _                   -> Nothing
                  , labels = Nothing
                  , name = "Term_IntLiteral"
                  , fixity = Nonfix
                  }

rTermVar :: Emb ((TermVar t) :*: t :*: Nil) (Term t)
rTermVar = Emb { to = \(v :*: t :*: Nil) -> Term_Var v t
               , from = \x -> case x of
                                Term_Var v t -> Just (v :*: t :*: Nil)
                                _            -> Nothing
               , labels = Nothing
               , name = "Term_Var"
               , fixity = Nonfix
               }

rTermAbs :: Emb ((Bind (TermVar t) (Term t)) :*: t :*: Nil) (Term t)
rTermAbs = Emb { to = \(b :*: t :*: Nil) -> Term_Abs b t
               , from = \x -> case x of
                               Term_Abs b t -> Just (b :*: t :*: Nil)
                               _            -> Nothing
               , labels = Nothing
               , name = "Term_Abs"
               , fixity = Nonfix
               }

rTermAbsAnn :: Emb ((Bind (TermVar t) (Term t)) :*: PolyType :*: t :*: Nil) (Term t)
rTermAbsAnn = Emb { to = \(b :*: p :*: t :*: Nil) -> Term_AbsAnn b p t
                  , from = \x -> case x of
                                  Term_AbsAnn b p t -> Just (b :*: p :*: t :*: Nil)
                                  _                 -> Nothing
                  , labels = Nothing
                  , name = "Term_AbsAnn"
                  , fixity = Nonfix
                  }

rTermApp :: Emb (Term t :*: Term t :*: t :*: Nil) (Term t)
rTermApp = Emb { to = \(t1 :*: t2 :*: t :*: Nil) -> Term_App t1 t2 t
               , from = \x -> case x of
                               Term_App t1 t2 t -> Just (t1 :*: t2 :*: t :*: Nil)
                               _                -> Nothing
               , labels = Nothing
               , name = "Term_App"
               , fixity = Nonfix
               }

rTermLet :: Emb ((Bind ((TermVar t), Embed (Term t)) (Term t)) :*: t :*: Nil) (Term t)
rTermLet = Emb { to = \(b :*: t :*: Nil) -> Term_Let b t
               , from = \x -> case x of
                               Term_Let b t -> Just (b :*: t :*: Nil)
                               _            -> Nothing
               , labels = Nothing
               , name = "Term_Let"
               , fixity = Nonfix
               }

rTermLetAnn :: Emb ((Bind ((TermVar t), Embed (Term t)) (Term t)) :*: PolyType :*: t :*: Nil) (Term t)
rTermLetAnn = Emb { to = \(b :*: p :*: t :*: Nil) -> Term_LetAnn b p t
                  , from = \x -> case x of
                                  Term_LetAnn b p t -> Just (b :*: p :*: t :*: Nil)
                                  _                 -> Nothing
                  , labels = Nothing
                  , name = "Term_LetAnn"
                  , fixity = Nonfix
                  }

rTermMatch :: Emb (Term t :*: String :*: [((TermVar t), Bind [TermVar t] (Term t))] :*: t :*: Nil) (Term t)
rTermMatch = Emb { to = \(e :*: c :*: alts :*: t :*: Nil) -> Term_Match e c alts t
                 , from = \x -> case x of
                                 Term_Match e c alts t -> Just (e :*: c :*: alts :*: t :*: Nil)
                                 _                     -> Nothing
                 , labels = Nothing
                 , name = "Term_Match"
                 , fixity = Nonfix
                 }

instance Alpha t => Alpha (Term t)
instance (Alpha t, Subst (Term t) t, Subst t Constraint, Subst t MonoType, Subst t PolyType) => Subst (Term t) (Term t) where
  isvar (Term_Var v _) = Just (SubstName v)
  isvar _              = Nothing
instance (Alpha t, Subst t t, Subst t PolyType) => Subst t (Term t)

instance (Subst t PolyType, Subst t Constraint, Subst t MonoType) => Subst (Term t) PolyType
instance (Subst t MonoType) => Subst (Term t) MonoType
instance (Subst t Constraint, Subst t PolyType, Subst t MonoType) => Subst (Term t) Constraint

-- Show instances

instance (Alpha t, Show t) => Show (Term t) where
  show = showAnnTerm id

showAnnTerm :: (Alpha a, Show b) => (a -> b) -> Term a -> String
showAnnTerm f = unlines . runFreshM . (showAnnTerm' f)

showAnnTerm' :: (Fresh m, Alpha a, Show b) => (a -> b) -> Term a -> m [String]
showAnnTerm' f (Term_IntLiteral n t) = return $ [show n ++ " ==> " ++ show (f t)]
showAnnTerm' f (Term_Var v t) = return $ [show v ++ " ==> " ++ show (f t)]
showAnnTerm' f (Term_Abs b t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\" ++ show x ++ " -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (Term_AbsAnn b p t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\(" ++ show x ++ " :: " ++ show p ++ ") -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (Term_App a b t) = do
  e1 <- showAnnTerm' f a
  e2 <- showAnnTerm' f b
  let line1 = "@ ==> " ++ show (f t)
  return $ line1 : map ("  " ++) (e1 ++ e2)
showAnnTerm' f (Term_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)
showAnnTerm' f (Term_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " :: " ++ show p ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)
showAnnTerm' f (Term_Match e c bs t) = do
  e'  <- showAnnTerm' f e
  bs' <- mapM (\(d,b) -> do (xs,es) <- unbind b
                            es' <- showAnnTerm' f es
                            let line1 = "| " ++ intercalate " " (map show (d:xs)) ++ " ->"
                            return $ line1 : map ("    " ++) es') bs
  let firstPart  = "match " : map ("  " ++) e'
      line2      = "with " ++ c ++ " ==> " ++ show (f t)
      secondPart = line2 : concat bs'
  return $ firstPart ++ secondPart

deriving instance Show Env