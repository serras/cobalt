{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.HigherRank.Syntax where

import Unbound.LocallyNameless

type TyVar = Name MonoType
data PolyType = PolyType_Quant (Bind [TyVar] RhoType)
              deriving Show
data RhoType  = RhoType_Mono MonoType
              | RhoType_Arrow PolyType RhoType
              deriving Show
data MonoType = MonoType_Int
              | MonoType_List  MonoType
              | MonoType_Tuple MonoType MonoType
              | MonoType_Arrow MonoType MonoType
              | MonoType_Var   TyVar
              deriving Show

type TermVar = Name Term
data Term = Term_IntLiteral Integer
          | Term_Var    TermVar
          | Term_Abs    (Bind TermVar Term)
          | Term_AnnAbs (Bind TermVar Term) PolyType
          | Term_App    Term Term
          | Term_Let    (Bind (TermVar, Embed Term) Term)
          | Term_Ann    Term PolyType
          deriving Show

data Constraint = Constraint_Eq   RhoType RhoType
                | Constraint_Inst PolyType RhoType
                deriving Show

-- Derive `unbound` instances
$(derive [''PolyType, ''RhoType, ''MonoType, ''Term, ''Constraint])

instance Alpha PolyType
instance Subst MonoType PolyType

instance Alpha RhoType
instance Subst MonoType RhoType

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var v) = Just (SubstName v)
  isvar _                = Nothing

instance Alpha Term
instance Subst Term Term where
  isvar (Term_Var v) = Just (SubstName v)
  isvar _            = Nothing
instance Subst Term PolyType
instance Subst Term RhoType
instance Subst Term MonoType
