{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.HigherRank.Syntax where

import Unbound.LocallyNameless

type TyVar = Name MonoType
data PolyType = PolyType_Inst   (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Equal  (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Mono   MonoType
              | PolyType_Bottom

instance Show PolyType where
  show (PolyType_Inst  b) = show b
  show (PolyType_Equal b) = show b
  show (PolyType_Mono  m) = show m
  show (PolyType_Bottom)  = "_|_"

data MonoType = MonoType_Int
              | MonoType_List  MonoType
              | MonoType_Tuple MonoType MonoType
              | MonoType_Arrow MonoType MonoType
              | MonoType_Var   TyVar

instance Show MonoType where
  show (MonoType_Int) = "Integer"
  show (MonoType_List t) = "[" ++ show t ++ "]"
  show (MonoType_Tuple t1 t2) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MonoType_Arrow s t) = let ss = show s
                               in if ' ' `elem` ss
                                     then "(" ++ ss ++ ")"
                                     else ss
                                  ++ "->" ++ show t
  show (MonoType_Var v) = show v

pVar :: TyVar -> PolyType
pVar = PolyType_Mono . mVar

mVar :: TyVar -> MonoType
mVar = MonoType_Var

(-->) :: MonoType -> MonoType -> MonoType
(-->) = MonoType_Arrow

type TermVar = Name Term
data Term = Term_IntLiteral Integer
          | Term_Var    TermVar
          | Term_Abs    (Bind TermVar Term)
          | Term_AbsAnn (Bind TermVar Term) PolyType
          | Term_App    Term Term
          | Term_Let    (Bind (TermVar, Embed Term) Term)
          | Term_LetAnn (Bind (TermVar, Embed Term) Term) PolyType
          deriving Show

type AnnTermVar = Name AnnTerm
data AnnTerm = AnnTerm_IntLiteral Integer MonoType
             | AnnTerm_Var    AnnTermVar MonoType
             | AnnTerm_Abs    (Bind AnnTermVar AnnTerm) MonoType
             | AnnTerm_AbsAnn (Bind AnnTermVar AnnTerm) PolyType MonoType
             | AnnTerm_App    AnnTerm AnnTerm MonoType
             | AnnTerm_Let    (Bind (AnnTermVar, Embed AnnTerm) AnnTerm) MonoType
             | AnnTerm_LetAnn (Bind (AnnTermVar, Embed AnnTerm) AnnTerm) PolyType MonoType
             deriving Show

data BasicConstraint = BasicConstraint_Inst  TyVar PolyType
                     | BasicConstraint_Equal TyVar PolyType

instance Show BasicConstraint where
  show (BasicConstraint_Inst  v p) = show v ++ " > " ++ show p
  show (BasicConstraint_Equal v p) = show v ++ " = " ++ show p

data Constraint = Constraint_Unify MonoType MonoType
                | Constraint_Inst  MonoType PolyType
                | Constraint_Equal MonoType PolyType
                | Constraint_Exists [TyVar] [BasicConstraint] [Constraint]

instance Show Constraint where
  show (Constraint_Unify t p) = show t ++ " ~ " ++ show p
  show (Constraint_Inst  t p) = show t ++ " > " ++ show p
  show (Constraint_Equal t p) = show t ++ " = " ++ show p
  show (Constraint_Exists vs cs c) = "exists " ++ show vs ++ "(" ++ show cs ++ " => " ++ show c ++ ")"

-- Derive `unbound` instances
$(derive [''PolyType, ''MonoType, ''Term, ''AnnTerm, ''BasicConstraint, ''Constraint])

instance Alpha PolyType
instance Subst MonoType PolyType
instance Subst Term PolyType
instance Subst AnnTerm PolyType

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var v) = Just (SubstName v)
  isvar _                = Nothing
instance Subst Term MonoType
instance Subst AnnTerm MonoType

instance Alpha Term
instance Subst Term Term where
  isvar (Term_Var v) = Just (SubstName v)
  isvar _            = Nothing
instance Subst MonoType Term

instance Alpha AnnTerm
instance Subst AnnTerm AnnTerm where
  isvar (AnnTerm_Var v _) = Just (SubstName v)
  isvar _                 = Nothing
instance Subst MonoType AnnTerm

instance Alpha BasicConstraint
instance Subst MonoType BasicConstraint

instance Alpha Constraint
instance Subst MonoType Constraint
