{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Syntax (
  TyVar
, PolyType(..)
, MonoType(..)
, intTy
, listTy
, tupleTy
, pVar
, mVar
, (-->)
, TermVar
, Term(..)
, AnnTermVar
, AnnTerm(..)
, showAnnTerm
, atAnn
, getAnn
, BasicConstraint(..)
, Constraint(..)
, Env
, Defn
, AnnDefn
) where

import Data.List
import Unbound.LocallyNameless

type TyVar = Name MonoType
data PolyType = PolyType_Inst   (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Equal  (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Mono   MonoType
              | PolyType_Bottom

instance Show PolyType where
  show = runFreshM . showPolyType'

showPolyType' :: PolyType -> FreshM String
showPolyType' (PolyType_Inst b) = do
  ((x, unembed -> p),r) <- unbind b
  showR <- showPolyType' r
  case p of
    PolyType_Bottom -> return $ "{" ++ show x ++ "} " ++ showR
    _ -> do showP <- showPolyType' p
            return $ "{" ++ show x ++ " > " ++ showP ++ "} " ++ showR
showPolyType' (PolyType_Equal b) = do
  ((x, unembed -> p),r) <- unbind b
  showR <- showPolyType' r
  showP <- showPolyType' p
  return $ "{" ++ show x ++ " = " ++ showP ++ "} " ++ showR
showPolyType' (PolyType_Mono m) = return $ show m
showPolyType' PolyType_Bottom   = return "_|_"

data MonoType = MonoType_Con   String [MonoType]
              -- | MonoType_Int
              -- | MonoType_List  MonoType
              -- | MonoType_Tuple MonoType MonoType
              | MonoType_Arrow MonoType MonoType
              | MonoType_Var   TyVar

intTy :: MonoType
intTy = MonoType_Con "Integer" []

listTy :: MonoType -> MonoType
listTy a = MonoType_Con "[]" [a]

tupleTy :: MonoType -> MonoType -> MonoType
tupleTy a b = MonoType_Con "(,)" [a,b]

instance Show MonoType where
  show (MonoType_Con "Integer" []) = "Integer"
  show (MonoType_Con "[]"  [t]) = "[" ++ show t ++ "]"
  show (MonoType_Con "(,)" [t1,t2]) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MonoType_Con c a) = c ++ " " ++ intercalate " " (map (doParens . show) a)
  show (MonoType_Arrow s t) = doParens (show s) ++ " -> " ++ show t
  show (MonoType_Var v) = show v

doParens :: String -> String
doParens s | ' ' `elem` s = '(' : s ++ ")"
           | otherwise    = s

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

instance Show AnnTerm where
  show = showAnnTerm id

showAnnTerm :: Show a => (MonoType -> a) -> AnnTerm -> String
showAnnTerm f = unlines . runFreshM . (showAnnTerm' f)

showAnnTerm' :: Show a => (MonoType -> a) -> AnnTerm -> FreshM [String]
showAnnTerm' f (AnnTerm_IntLiteral n t) = return $ [show n ++ " ==> " ++ show (f t)]
showAnnTerm' f (AnnTerm_Var v t) = return $ [show v ++ " ==> " ++ show (f t)]
showAnnTerm' f (AnnTerm_Abs b t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\" ++ show x ++ " -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (AnnTerm_AbsAnn b p t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\" ++ show x ++ " :: " ++ show p ++ " -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (AnnTerm_App a b t) = do
  e1 <- showAnnTerm' f a
  e2 <- showAnnTerm' f b
  let line1 = "@ ==> " ++ show (f t)
  return $ line1 : map ("  " ++) (e1 ++ e2)
showAnnTerm' f (AnnTerm_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)
showAnnTerm' f (AnnTerm_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " :: " ++ show p ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)

atAnn :: (MonoType -> MonoType) -> AnnTerm -> AnnTerm
atAnn f = runFreshM . atAnn' f

atAnn' :: (MonoType -> MonoType) -> AnnTerm -> FreshM AnnTerm
atAnn' f (AnnTerm_IntLiteral n t) = return $ AnnTerm_IntLiteral n (f t)
atAnn' f (AnnTerm_Var v t) = return $ AnnTerm_Var v (f t)
atAnn' f (AnnTerm_Abs b t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ AnnTerm_Abs (bind x inner) (f t)
atAnn' f (AnnTerm_AbsAnn b p t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ AnnTerm_AbsAnn (bind x inner) p (f t)
atAnn' f (AnnTerm_App a b t) = do
  e1 <- atAnn' f a
  e2 <- atAnn' f b
  return $ AnnTerm_App e1 e2 (f t)
atAnn' f (AnnTerm_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ AnnTerm_Let (bind (x, embed s1) s2) (f t)
atAnn' f (AnnTerm_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ AnnTerm_LetAnn (bind (x, embed s1) s2) p (f t)

getAnn :: AnnTerm -> MonoType
getAnn (AnnTerm_IntLiteral _ t) = t
getAnn (AnnTerm_Var _ t)        = t
getAnn (AnnTerm_Abs _ t)        = t
getAnn (AnnTerm_AbsAnn _ _ t)   = t
getAnn (AnnTerm_App _ _ t)      = t
getAnn (AnnTerm_Let _ t)        = t
getAnn (AnnTerm_LetAnn _ _ t)   = t

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

type Env     = [(TermVar, PolyType)]
type Defn    = (TermVar, Term)
type AnnDefn = (TermVar, AnnTerm, PolyType)

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
