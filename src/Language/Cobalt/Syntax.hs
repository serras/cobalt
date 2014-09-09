{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Cobalt.Syntax (
  -- * Types
  TyVar
  -- ** Polytypes
, PolyType(..)
, nf
  -- ** Monotypes
, MonoType(..)
, pattern MonoType_Int
, pattern MonoType_List
, pattern MonoType_Tuple
, pattern (:-->:)
, arr
, var
  -- ** From poly to mono
, split
, close
, closeExn
  -- * Terms
, TermVar
, Term(..)
  -- ** Annotated terms
, AnnTermVar
, AnnTerm(..)
, showAnnTerm
, atAnn
, getAnn
  -- * Constraints and axioms
, Constraint(..)
, _Constraint_Unify
, _Constraint_Inst
, _Constraint_Equal
, _Constraint_Exists
, Axiom(..)
  -- * Whole program structure
, FnEnv
, DataEnv
, initialDataEnv
, AxiomEnv
, Env(Env)
, fnE
, dataE
, axiomE
, Defn
, AnnDefn
) where

import Control.Applicative ((<$>))
import Control.Lens
import Data.List (insert, intercalate, find, nub)
import Data.Maybe (isJust)
import Unbound.LocallyNameless hiding (close)

type TyVar = Name MonoType
data PolyType = PolyType_Bind (Bind TyVar PolyType)
              | PolyType_Mono [Constraint] MonoType
              | PolyType_Bottom

instance Show PolyType where
  show = runFreshM . showPolyType'

showPolyType' :: Fresh m => PolyType -> m String
showPolyType' (PolyType_Bind b) = do
  (x, r) <- unbind b
  showR <- showPolyType' r
  return $ "{" ++ show x ++ "} " ++ showR
showPolyType' (PolyType_Mono [] m) = return $ show m
showPolyType' (PolyType_Mono cs m) = return $ show cs ++ " => " ++ show m
showPolyType' PolyType_Bottom   = return "⊥"

-- TODO
-- nf in two steps: first put the constraints in order
-- second: replace those which needs to be replaced

nf :: PolyType -> PolyType
nf = runFreshM . nf' []
     where -- Run over Fresh monad
           nf' :: (Fresh m, Monad m, Functor m)
               => [TyVar] -> PolyType -> m PolyType
           nf' _ PolyType_Bottom = return PolyType_Bottom
           nf' bnders (PolyType_Bind b) = do
             (x, r) <- unbind b
             nf' (x:bnders) r
           nf' bnders (PolyType_Mono cs m) = nf'' bnders [] m cs
           -- Apply simplification under each constraint
           nf'' :: (Fresh m, Monad m, Functor m)
                => [TyVar] -> [Constraint] -> MonoType
                -> [Constraint] -> m PolyType
           nf'' bnders cs m [] = return $ reverseBind bnders (PolyType_Mono cs m)
           nf'' bnders accum m (x:xs) = case x of
             (Constraint_Inst (MonoType_Var v)  (PolyType_Mono [] p)) ->
               nf'' bnders [] m =<< mapM (nfC . subst v p) (accum ++ xs)
             (Constraint_Equal (MonoType_Var v) (PolyType_Mono [] p)) ->
               nf'' bnders [] m =<< mapM (nfC . subst v p) (accum ++ xs)
             (Constraint_Unify (MonoType_Var v) p) ->
               nf'' bnders [] m =<< mapM (nfC . subst v p) (accum ++ xs)
             _ -> nf'' bnders (x:accum) m xs
           -- Make normal form of constraints
           nfC :: (Fresh m, Monad m, Functor m) => Constraint -> m Constraint
           nfC (Constraint_Inst  m p) = Constraint_Inst  m <$> nf' [] p
           nfC (Constraint_Equal m p) = Constraint_Equal m <$> nf' [] p
           nfC c = return c
           -- Bind back all binders
           reverseBind :: [TyVar] -> PolyType -> PolyType
           reverseBind [] p = p
           reverseBind (x:xs) p
             | x `elem` fv p = reverseBind xs $ PolyType_Bind (bind x p)
             | otherwise     = p

data MonoType = MonoType_Con   String [MonoType]
              | MonoType_Fam   String [MonoType]
              | MonoType_Var   TyVar
              | MonoType_Arrow MonoType MonoType
              deriving Eq

pattern MonoType_Int       = MonoType_Con   "Integer" []
pattern MonoType_List  t   = MonoType_Con   "List" [t]
pattern MonoType_Tuple a b = MonoType_Con   "Tuple2" [a,b]
pattern s :-->: r          = MonoType_Arrow s r

arr :: MonoType -> ([MonoType],MonoType)
arr (s :-->: r) = let (s',r') = arr r in (s:s', r')
arr m = ([], m)

instance Show MonoType where
  show (MonoType_List t)      = "[" ++ show t ++ "]"
  show (MonoType_Tuple t1 t2) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MonoType_Con c a)     = '\'':c ++ concatMap (\x -> " " ++ doParens (show x)) a
  show (MonoType_Fam c a)     = '^':c ++ concatMap (\x -> " " ++ doParens (show x)) a
  show (s :-->: t)            = doParens (show s) ++ " -> " ++ show t
  show (MonoType_Var v)       = show v
  show _                      = error "Pattern matching check is not that good"

doParens :: String -> String
doParens s | ' ' `elem` s = '(' : s ++ ")"
           | otherwise    = s

class VariableInjection v where
  var :: TyVar -> v

instance VariableInjection PolyType where
  var = PolyType_Mono [] . var

instance VariableInjection MonoType where
  var = MonoType_Var

split :: (Fresh m, Functor m) => PolyType -> m ([Constraint], MonoType, [TyVar])
split (PolyType_Bind b) = do
  (x, r) <- unbind b
  (c, m, v) <- split r
  return (c, m, insert x v)
split (PolyType_Mono cs m) = return (cs, m, [])
split PolyType_Bottom = do
  x <- fresh (string2Name "x")
  return ([Constraint_Inst (var x) PolyType_Bottom], var x, [x])

close :: [Constraint] -> MonoType -> PolyType
close cs m = closeExn cs m (const False)

-- TODO: Perform correct closing by ordering variables
closeExn :: [Constraint] -> MonoType -> (TyVar -> Bool) -> PolyType
closeExn cs m except = let (cns, vars) = closeTypeA (filter (hasCsFv (fv m)) cs)
                        in finalClose (nub vars) (PolyType_Mono cns m)
  where closeTypeA preCs = let nextC = filter (not . except) (fv preCs)
                               filtC = filter (\c -> hasCsFv nextC c
                                                     && not (isJust (find (`aeq` c) preCs))) cs
                            in case filtC of
                                 [] -> (filter (hasCsFv (fv m)) cs, filter (not . except) (fv m))
                                 _  -> let (finalCs, finalVrs) = closeTypeA (preCs ++ filtC)
                                        in (finalCs ++ filtC, (fv filtC) ++ finalVrs)
        -- check if fv are there
        hasCsFv lst (Constraint_Inst  (MonoType_Var v) _) = v `elem` lst
        hasCsFv lst (Constraint_Equal (MonoType_Var v) _) = v `elem` lst
        hasCsFv lst (Constraint_Unify t1 t2) = any (`elem` lst) (fv t1) || any (`elem` lst) (fv t2)
        hasCsFv _ _ = False
        -- final close
        finalClose []     p = p
        finalClose (v:vs) p = PolyType_Bind (bind v (finalClose vs p))

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

$(makePrisms ''Constraint)

data Axiom = Axiom_Unify (Bind [TyVar] (MonoType, MonoType))

instance Show Axiom where
  show = runFreshM . showAxiom

showAxiom :: (Fresh m, Functor m) => Axiom -> m String
showAxiom (Axiom_Unify b) = do (xs, (lhs,rhs)) <- unbind b
                               return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs

type FnEnv    = [(TermVar, PolyType)]
type DataEnv  = [(String, [TyVar])]
type AxiomEnv = [Axiom]
data Env      = Env { _fnE    :: FnEnv
                    , _dataE  :: DataEnv
                    , _axiomE :: AxiomEnv }
                deriving Show

$(makeLenses ''Env)

type Defn    = (TermVar, Term, Maybe PolyType)
type AnnDefn = (TermVar, AnnTerm, PolyType)

initialDataEnv :: DataEnv
initialDataEnv = [("Integer", [])
                 ,("List",    [string2Name "a"])
                 ,("Tuple2",  [string2Name "a", string2Name "b"])]

-- Derive `unbound` instances
$(derive [''PolyType, ''MonoType, ''Term, ''AnnTerm, ''Constraint, ''Axiom])

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

instance Alpha Constraint
instance Subst MonoType Constraint
instance Subst Term Constraint
instance Subst AnnTerm Constraint

instance Alpha Axiom
instance Subst MonoType Axiom
