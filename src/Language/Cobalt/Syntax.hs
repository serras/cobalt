{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
module Language.Cobalt.Syntax (
  -- * Types
  TyVar
  -- ** Polytypes
, PolyType(..)
, nf
  -- ** Monotypes
, MonoType(..)
  -- ** Built-in types
, intTy
, listTy
, tupleTy
, pVar
, mVar
, (-->)
  -- ** From poly to mono
, splitType
, closeType
, closeTypeWithException
  -- * Terms
, TermVar
, Term(..)
  -- ** Annotated terms
, AnnTermVar
, AnnTerm(..)
, showAnnTerm
, atAnn
, getAnn
  -- * Constraints
, Constraint(..)
, isExists
  -- * Whole program structure
, Env
, DataEnv
, initialDataEnv
, Defn
, AnnDefn
) where

import Control.Applicative ((<$>))
import Data.List ((\\), insert, intercalate)
import Unbound.LocallyNameless

type TyVar = Name MonoType
data PolyType = PolyType_Inst   (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Equal  (Bind (TyVar, Embed PolyType) PolyType)
              | PolyType_Mono   MonoType
              | PolyType_Bottom

instance Show PolyType where
  show = runFreshM . showPolyType'

showPolyType' :: Fresh m => PolyType -> m String
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

nf :: PolyType -> PolyType
nf = runFreshM . nf'
     where nf' PolyType_Bottom     = return PolyType_Bottom
           nf' m@(PolyType_Mono _) = return m
           nf' (PolyType_Inst  b)  = workWithBind PolyType_Inst b
           nf' (PolyType_Equal b)  = workWithBind PolyType_Equal b
           workWithBind f b = do
             ((x, unembed -> e), r) <- unbind b
             nfEmbed <- nf' e
             nfRest  <- nf' r
             case (x `elem` fv r, nfEmbed, nfRest) of
               (False, _, _) -> return nfRest
               (True, _, PolyType_Mono (MonoType_Var v)) | v == x -> return nfEmbed
               (True, PolyType_Mono monoEmbed, _) -> return $ subst x monoEmbed nfRest
               _ -> return $ f $ bind (x, embed nfEmbed) nfRest

data MonoType = MonoType_Con   String [MonoType]
              -- | MonoType_Int
              -- | MonoType_List  MonoType
              -- | MonoType_Tuple MonoType MonoType
              | MonoType_Arrow MonoType MonoType
              | MonoType_Var   TyVar
              deriving Eq

intTy :: MonoType
intTy = MonoType_Con "Integer" []

listTy :: MonoType -> MonoType
listTy a = MonoType_Con "List" [a]

tupleTy :: MonoType -> MonoType -> MonoType
tupleTy a b = MonoType_Con "Tuple2" [a,b]

instance Show MonoType where
  show (MonoType_Con "List"  [t]) = "[" ++ show t ++ "]"
  show (MonoType_Con "Tuple2" [t1,t2]) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MonoType_Con c a) = '\'':c ++ concatMap (\x -> " " ++ doParens (show x)) a
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

splitType :: (Fresh m, Functor m) => PolyType -> m ([Constraint], MonoType, [TyVar])
splitType (PolyType_Inst b) = do
  ((x, unembed -> s),r) <- unbind b
  (c, m, v) <- splitType r
  return (Constraint_Inst (mVar x) s : c, m, insert x v)
splitType (PolyType_Equal b) = do
  ((x, unembed -> s),r) <- unbind b
  (c, m, v) <- splitType r
  return (Constraint_Equal (mVar x) s : c, m, insert x v)
splitType (PolyType_Mono m) = return ([], m, [])
splitType PolyType_Bottom = do
  x <- fresh (string2Name "x")
  return ([Constraint_Inst (mVar x) PolyType_Bottom], mVar x, [x])

closeType :: [Constraint] -> MonoType -> PolyType
closeType cs m = closeTypeWithException cs m (const False)

-- TODO: Perform correct closing by ordering variables
closeTypeWithException :: [Constraint] -> MonoType -> (TyVar -> Bool) -> PolyType
closeTypeWithException cs m except = closeTypeA [] (PolyType_Mono m)
  where closeTypeA pre p = let nextC = filter (not . except) (fv p) \\ pre
                               filtC = filter (hasCsFv nextC) cs
                            in case filtC of
                                 [] -> closeRest nextC p
                                 _  -> let (inner,usedV) = closeType' filtC p
                                        in closeTypeA (usedV `union` pre) inner
        -- check if fv are there
        hasCsFv lst (Constraint_Inst  (MonoType_Var v) _) = v `elem` lst
        hasCsFv lst (Constraint_Equal (MonoType_Var v) _) = v `elem` lst
        hasCsFv _ _ = False
        -- close upon constraints
        closeType' ((Constraint_Inst (MonoType_Var v) t) : rest) p =
          let (p',v') = closeType' rest p
           in (PolyType_Inst $ bind (v,embed t) p', insert v v')
        closeType' ((Constraint_Equal (MonoType_Var v) t) : rest) p =
          let (p',v') = closeType' rest p
           in (PolyType_Equal $ bind (v,embed t) p', insert v v')
        closeType' (_ : rest) p = closeType' rest p
        closeType' [] p = (p, [])
        -- close rest
        closeRest [] p     = p
        closeRest (v:vs) p = PolyType_Inst $ bind (v, embed PolyType_Bottom) (closeRest vs p)

type TermVar = Name Term
data Term = Term_IntLiteral Integer
          | Term_Var    TermVar
          | Term_Abs    (Bind TermVar Term)
          | Term_AbsAnn (Bind TermVar Term) PolyType
          | Term_App    Term Term
          | Term_Let    (Bind (TermVar, Embed Term) Term)
          | Term_LetAnn (Bind (TermVar, Embed Term) Term) PolyType
          | Term_Match  Term String [(TermVar, Bind [TermVar] Term)]
          deriving Show

type AnnTermVar = Name AnnTerm
data AnnTerm = AnnTerm_IntLiteral Integer MonoType
             | AnnTerm_Var    AnnTermVar MonoType
             | AnnTerm_Abs    (Bind AnnTermVar AnnTerm) MonoType
             | AnnTerm_AbsAnn (Bind AnnTermVar AnnTerm) PolyType MonoType
             | AnnTerm_App    AnnTerm AnnTerm MonoType
             | AnnTerm_Let    (Bind (AnnTermVar, Embed AnnTerm) AnnTerm) MonoType
             | AnnTerm_LetAnn (Bind (AnnTermVar, Embed AnnTerm) AnnTerm) PolyType MonoType
             | AnnTerm_Match  AnnTerm String [(TermVar, Bind [TermVar] AnnTerm)] MonoType

instance Show AnnTerm where
  show = showAnnTerm id

showAnnTerm :: Show a => (MonoType -> a) -> AnnTerm -> String
showAnnTerm f = unlines . runFreshM . (showAnnTerm' f)

showAnnTerm' :: Fresh m => Show a => (MonoType -> a) -> AnnTerm -> m [String]
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
showAnnTerm' f (AnnTerm_Match e c bs t) = do
  e'  <- showAnnTerm' f e
  bs' <- mapM (\(d,b) -> do (xs,es) <- unbind b
                            es' <- showAnnTerm' f es
                            let line1 = "| " ++ intercalate " " (map show (d:xs)) ++ " ->"
                            return $ line1 : map ("    " ++) es') bs
  let firstPart  = "match " : map ("  " ++) e'
      line2      = "with " ++ c ++ " ==> " ++ show (f t)
      secondPart = line2 : concat bs'
  return $ firstPart ++ secondPart

atAnn :: (MonoType -> MonoType) -> AnnTerm -> AnnTerm
atAnn f = runFreshM . atAnn' f

atAnn' :: Fresh m => (MonoType -> MonoType) -> AnnTerm -> m AnnTerm
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
atAnn' f (AnnTerm_Match e c bs t) = do
  e' <- atAnn' f e
  b' <- mapM (\(d,b) -> do (xs,expr) <- unbind b
                           expr' <- atAnn' f expr
                           return $ (d,bind xs expr')) bs
  return $ AnnTerm_Match e' c b' (f t)

getAnn :: AnnTerm -> MonoType
getAnn (AnnTerm_IntLiteral _ t) = t
getAnn (AnnTerm_Var _ t)        = t
getAnn (AnnTerm_Abs _ t)        = t
getAnn (AnnTerm_AbsAnn _ _ t)   = t
getAnn (AnnTerm_App _ _ t)      = t
getAnn (AnnTerm_Let _ t)        = t
getAnn (AnnTerm_LetAnn _ _ t)   = t
getAnn (AnnTerm_Match _ _ _ t)  = t

data Constraint = Constraint_Unify MonoType MonoType
                | Constraint_Inst  MonoType PolyType
                | Constraint_Equal MonoType PolyType
                | Constraint_Exists (Bind [TyVar] ([Constraint],[Constraint]))

instance Show [Constraint] where
  show = runFreshM . showConstraintList

instance Show Constraint where
  show = runFreshM . showConstraint

showConstraintList :: (Fresh m, Functor m) => [Constraint] -> m String
showConstraintList [] = return "∅"
showConstraintList l  = intercalate " ∧ " <$> mapM showConstraint l

showConstraint :: (Fresh m, Functor m) => Constraint -> m String
showConstraint (Constraint_Unify t p) = return $ show t ++ " ~ " ++ show p
showConstraint (Constraint_Inst  t p) = do p' <- showPolyType' p
                                           return $ show t ++ " > " ++ p'
showConstraint (Constraint_Equal t p) = do p' <- showPolyType' p
                                           return $ show t ++ " = " ++ p'
showConstraint (Constraint_Exists b)  = do (x, (q,c)) <- unbind b
                                           q' <- showConstraintList q
                                           c' <- showConstraintList c
                                           return $ "∃" ++ show x ++ "(" ++ q' ++ " => " ++ c' ++ ")"

isExists :: Constraint -> Bool
isExists (Constraint_Exists _) = True
isExists _                     = False

type Env     = [(TermVar, PolyType)]
type DataEnv = [(String, [TyVar])]
type Defn    = (TermVar, Term, Maybe PolyType)
type AnnDefn = (TermVar, AnnTerm, PolyType)

initialDataEnv :: DataEnv
initialDataEnv = [("Integer", [])
                 ,("List",   [string2Name "a"])
                 ,("Tuple2", [string2Name "a", string2Name "b"])]

-- Derive `unbound` instances
$(derive [''PolyType, ''MonoType, ''Term, ''AnnTerm, ''Constraint])

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

{-
instance Alpha BasicConstraint
instance Subst MonoType BasicConstraint
-}

instance Alpha Constraint
instance Subst MonoType Constraint
