{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverlappingInstances #-}
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
, isFamilyFree
, arr
, var
  -- ** From poly to mono
, split
, close
, closeExn
  -- * Terms
, RawTermVar
, RawTerm
, TyTermVar
, TyTerm
  -- ** Generic annotated terms
, TermVar
, Term(..)
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
, Defn
, TyDefn
) where

import Control.Applicative ((<$>))
import Control.Lens hiding ((.=), from, to)
import Data.List (insert, intercalate, find, nub)
import Data.Maybe (isJust)
import Unbound.LocallyNameless hiding (close)

type TyVar = Name MonoType
data PolyType = PolyType_Bind (Bind TyVar PolyType)
              | PolyType_Mono [Constraint] MonoType
              | PolyType_Bottom

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
           nf'' _ _ (MonoType_Var v) (Constraint_Inst (MonoType_Var v') p : _)
             | v == v' = nf' [] p
           nf'' _ _ (MonoType_Var v) (Constraint_Equal (MonoType_Var v') p : _)
             | v == v' = nf' [] p
           nf'' bnders accum m (x:xs) = case x of
             (Constraint_Inst (MonoType_Var v)  (PolyType_Mono [] p)) ->
               nf'' bnders [] (subst v p m) =<< mapM (nfC . subst v p) (accum ++ xs)
             (Constraint_Equal (MonoType_Var v) (PolyType_Mono [] p)) ->
               nf'' bnders [] (subst v p m) =<< mapM (nfC . subst v p) (accum ++ xs)
             (Constraint_Unify (MonoType_Var v) p) ->
               nf'' bnders [] (subst v p m) =<< mapM (nfC . subst v p) (accum ++ xs)
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

pattern MonoType_Int       = MonoType_Con   "Int" []
pattern MonoType_List  t   = MonoType_Con   "List" [t]
pattern MonoType_Tuple a b = MonoType_Con   "Tuple2" [a,b]
pattern s :-->: r          = MonoType_Arrow s r

isFamilyFree :: MonoType -> Bool
isFamilyFree (MonoType_Con _ args)  = all isFamilyFree args
isFamilyFree (MonoType_Fam _ _)     = False
isFamilyFree (MonoType_Var _)       = True
isFamilyFree (MonoType_Arrow a1 a2) = isFamilyFree a1 && isFamilyFree a2

arr :: MonoType -> ([MonoType],MonoType)
arr (s :-->: r) = let (s',r') = arr r in (s:s', r')
arr m = ([], m)

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

data Constraint = Constraint_Unify MonoType MonoType
                | Constraint_Inst  MonoType PolyType
                | Constraint_Equal MonoType PolyType
                | Constraint_Exists (Bind [TyVar] ([Constraint],[Constraint]))

$(makePrisms ''Constraint)

data Axiom = Axiom_Unify (Bind [TyVar] (MonoType, MonoType))

type FnEnv    = [(RawTermVar, PolyType)]
type DataEnv  = [(String, [TyVar])]
type AxiomEnv = [Axiom]
data Env      = Env { _fnE    :: FnEnv
                    , _dataE  :: DataEnv
                    , _axiomE :: AxiomEnv }

$(makeLenses ''Env)

type Defn   = (RawTermVar, RawTerm, Maybe PolyType)
type TyDefn = (RawTermVar, TyTerm,  PolyType)

initialDataEnv :: DataEnv
initialDataEnv = [("Int",     [])
                 ,("List",    [string2Name "a"])
                 ,("Tuple2",  [string2Name "a", string2Name "b"])]

-- Derive `unbound` instances
$(derive [''PolyType, ''MonoType, ''Constraint, ''Axiom])

instance Rep t => Rep (Term t) where
  rep = Data (DT "Term" ((rep :: R t) :+: MNil))
             [ Con rIntLiteral ((rep :: R Integer) :+: (rep :: R t) :+: MNil)
             , Con rTermAbs    ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R t) :+: MNil)
             , Con rTermAbsAnn ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermApp    ((rep :: R (Term t)) :+: (rep :: R (Term t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLet    ((rep :: R ((Bind ((TermVar t), Embed (Term t)) (Term t)))) :+: (rep :: R t) :+: MNil)
             , Con rTermLetAnn ((rep :: R ((Bind ((TermVar t), Embed (Term t)) (Term t)))) :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermMatch  ((rep :: R (Term t)) :+: (rep :: R String) :+: (rep :: R [((TermVar t), Bind [TermVar t] (Term t))]) :+: (rep :: R t) :+: MNil)
             ]

instance ( Rep t, Sat (ctx t), Sat (ctx (Term t))
         , Sat (ctx Integer), Sat (ctx String), Sat (ctx PolyType)
         , Sat (ctx (Bind (TermVar t) (Term t))), Sat (ctx (Bind ((TermVar t), Embed (Term t)) (Term t)))
         , Sat (ctx [((TermVar t), Bind [TermVar t] (Term t))])) => Rep1 ctx (Term t) where
  rep1 = rAnnTerm1 dict dict dict dict dict dict dict dict

rAnnTerm1 :: forall t ctx. Rep t
          => ctx t -> ctx (Term t)
          -> ctx Integer -> ctx String -> ctx PolyType
          -> ctx (Bind (TermVar t) (Term t)) -> ctx (Bind ((TermVar t), Embed (Term t)) (Term t))
          -> ctx [((TermVar t), Bind [TermVar t] (Term t))] -> R1 ctx (Term t)
rAnnTerm1 ct ctt ci cs cp cb1 cb2 cbl =
  Data1 (DT "Term" ((rep :: R t) :+: MNil))
        [ Con rIntLiteral (ci :+: ct :+: MNil)
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

instance Alpha PolyType
instance Subst MonoType PolyType
instance (Subst t PolyType, Subst t Constraint, Subst t MonoType) => Subst (Term t) PolyType

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var v) = Just (SubstName v)
  isvar _                = Nothing
instance (Subst t MonoType) => Subst (Term t) MonoType

instance Alpha t => Alpha (Term t)
instance (Alpha t, Subst (Term t) t, Subst t Constraint, Subst t MonoType, Subst t PolyType) => Subst (Term t) (Term t) where
  isvar (Term_Var v _) = Just (SubstName v)
  isvar _              = Nothing
instance (Alpha t, Subst t t, Subst t PolyType) => Subst t (Term t)

instance Alpha Constraint
instance Subst MonoType Constraint
instance (Subst t Constraint, Subst t PolyType, Subst t MonoType) => Subst (Term t) Constraint

instance Alpha Axiom
instance Subst MonoType Axiom

-- Show instances

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

instance Show Axiom where
  show = runFreshM . showAxiom

showAxiom :: (Fresh m, Functor m) => Axiom -> m String
showAxiom (Axiom_Unify b) = do (xs, (lhs,rhs)) <- unbind b
                               return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs

deriving instance Show Env
