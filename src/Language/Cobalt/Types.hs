{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.Cobalt.Types (
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
  -- * Constraints and axioms
, Constraint(..)
, _Constraint_Unify
, _Constraint_Inst
, _Constraint_Equal
, _Constraint_Class
, _Constraint_Exists
, Axiom(..)
) where

import Control.Applicative ((<$>))
import Control.Lens hiding ((.=), from, to)
import Data.List (insert, intercalate, find, nub, sortBy, (\\))
import Data.Maybe (isJust)
import Unbound.LocallyNameless hiding (close, GT)

import Language.Cobalt.Util

type TyVar = Name MonoType
data PolyType = PolyType_Bind (Bind TyVar PolyType)
              | PolyType_Mono [Constraint] MonoType
              | PolyType_Bottom

instance Eq PolyType where
  PolyType_Bind b1   == PolyType_Bind b2 = runFreshM $ do
    s <- unbind2 b1 b2
    case s of
      Just (_,p1,_,p2) -> return $ p1 == p2
      Nothing          -> return False
  PolyType_Mono c1 m1 == PolyType_Mono c2 m2 = c1 == c2 && m1 == m2
  PolyType_Bottom     == PolyType_Bottom     = True
  _                   == _                   = False

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
           nf'' bnders cs m [] = return $ reverseBind bnders (PolyType_Mono (sortBy orderConstraint cs) m)
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

orderConstraint :: Constraint -> Constraint -> Ordering
orderConstraint (Constraint_Unify t1 t2) (Constraint_Unify s1 s2) = compare (t1,t2) (s1,s2)
orderConstraint (Constraint_Unify _ _) _ = LT
orderConstraint _ (Constraint_Unify _ _) = GT
orderConstraint (Constraint_Inst t1 _) (Constraint_Inst s1 _) = compare t1 s1
orderConstraint (Constraint_Inst _ _) _ = LT
orderConstraint _ (Constraint_Inst _ _) = GT
orderConstraint (Constraint_Equal t1 _) (Constraint_Equal s1 _) = compare t1 s1
orderConstraint (Constraint_Equal _ _) _ = LT
orderConstraint _ (Constraint_Equal _ _) = GT
orderConstraint (Constraint_Class c1 ts1) (Constraint_Class c2 ts2) = compare (c1,ts1) (c2,ts2)
orderConstraint (Constraint_Class _ _) _ = LT
orderConstraint _ (Constraint_Class _ _) = GT
orderConstraint _ _ = EQ

data MonoType = MonoType_Fam   String [MonoType]
              | MonoType_Var   TyVar
              | MonoType_Con   String [MonoType]
              | MonoType_Arrow MonoType MonoType
              deriving (Eq, Ord)

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

close :: [Constraint] -> MonoType -> (PolyType, [Constraint])
close cs m = closeExn cs m (const False)

closeExn :: [Constraint] -> MonoType -> (TyVar -> Bool) -> (PolyType, [Constraint])
closeExn cs m except = let (cns, vars) = closeTypeA (filter (hasCsFv (fv m)) cs)
                        in (finalClose (nub vars) (PolyType_Mono cns m), cs \\ cns)
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
        hasCsFv lst (Constraint_Class _ t)   = any (`elem` lst) (fv t)
        hasCsFv _ _ = False
        -- final close
        finalClose []     p = p
        finalClose (v:vs) p = PolyType_Bind (bind v (finalClose vs p))

data Constraint = Constraint_Unify MonoType MonoType
                | Constraint_Inst  MonoType PolyType
                | Constraint_Equal MonoType PolyType
                | Constraint_Class String [MonoType]
                | Constraint_Exists (Bind [TyVar] ([Constraint],[Constraint]))

$(makePrisms ''Constraint)

instance Eq Constraint where
  Constraint_Unify m1 m2 == Constraint_Unify n1 n2 = m1 == n1 && m2 == n2
  Constraint_Inst  m1 m2 == Constraint_Inst  n1 n2 = m1 == n1 && m2 == n2
  Constraint_Equal m1 m2 == Constraint_Equal n1 n2 = m1 == n1 && m2 == n2
  Constraint_Class c1 a1 == Constraint_Class c2 a2 = c1 == c2 && a1 == a2
  Constraint_Exists b1   == Constraint_Exists b2 = runFreshM $ do
    s <- unbind2 b1 b2
    case s of
      Just (_,c1,_,c2) -> return $ c1 == c2
      Nothing          -> return False
  _ == _ = False

data Axiom = Axiom_Unify (Bind [TyVar] (MonoType, MonoType))
           | Axiom_Class (Bind [TyVar] ([Constraint], String, [MonoType]))

-- Derive `unbound` instances
$(derive [''PolyType, ''MonoType, ''Constraint, ''Axiom])

instance Alpha PolyType
instance Subst MonoType PolyType

instance Alpha MonoType
instance Subst MonoType MonoType where
  isvar (MonoType_Var v) = Just (SubstName v)
  isvar _                = Nothing

instance Alpha Constraint
instance Subst MonoType Constraint

instance Alpha Axiom
instance Subst MonoType Axiom

-- Derive `Show` instances  
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
showConstraint (Constraint_Class c t) = do let ps = map (doParens . show) t
                                           return $ "$" ++ c ++ " " ++ intercalate " " ps
showConstraint (Constraint_Exists b)  = do (x, (q,c)) <- unbind b
                                           q' <- showConstraintList q
                                           c' <- showConstraintList c
                                           return $ "∃" ++ show x ++ "(" ++ q' ++ " => " ++ c' ++ ")"

instance Show Axiom where
  show = runFreshM . showAxiom

showAxiom :: (Fresh m, Functor m) => Axiom -> m String
showAxiom (Axiom_Unify b) = do (xs, (lhs,rhs)) <- unbind b
                               return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs
showAxiom (Axiom_Class b) = do (xs, (ctx,c,ms)) <- unbind b
                               let ps = map (doParens . show) ms
                               return $ "∀" ++ show xs ++ " " ++ show ctx ++
                                        " => $" ++ c ++ " " ++ intercalate " " ps
