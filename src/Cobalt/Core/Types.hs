{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cobalt.Core.Types (
  -- * Types
  TyVar
  -- ** Polytypes
, PolyType(..)
, nf
, ftype
, showPolyTypeAsSystemF
  -- ** Monotypes
, MonoType(..)
, MonoTypes
, pattern MonoType_Int
, pattern MonoType_Char
, pattern MonoType_String
, pattern MonoType_List
, pattern MonoType_Tuple
, pattern (:-->:)
, isFamilyFree
, arr
, unarr
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
, _Constraint_FType
, _Constraint_Later
, _Constraint_Cond
, showConstraintList
, orderConstraint
, Axiom(..)
, isTresspasable
) where

#if MIN_VERSION_base(4,8,0)
#else
import Control.Applicative ((<$>))
#endif
import Control.Lens hiding ((.=), from, to, mapping)
import Control.Lens.Extras (is)
import Data.List (insert, intercalate, find, nub, sortBy, (\\), partition)
import Data.Maybe (isJust)
import Unbound.LocallyNameless hiding (close, GT)

import Util.Show

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
             Constraint_Inconsistent -> error "Inconsistent constraints not allowed in polytypes"
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
             | x `elem` (fv p :: [TyVar]) = reverseBind xs $ PolyType_Bind (bind x p)
             | otherwise                  = reverseBind xs p

-- System F type with less inner polymirphism possible
-- Based on Daan Leijen's Flexible Types paper
ftype :: PolyType -> PolyType
ftype = nf . runFreshM . ft . nf
        where ft :: (Fresh m, Monad m, Functor m) => PolyType -> m PolyType
              ft PolyType_Bottom     = return PolyType_Bottom
              ft (PolyType_Bind b)   = do (x, r) <- unbind b
                                          ftR <- ft r
                                          return $ PolyType_Bind (bind x ftR)
              ft (PolyType_Mono c m) = do (c', m', v') <- ftMono m c [] []
                                          return $ foldr (\x ftR -> PolyType_Bind (bind x ftR)) (PolyType_Mono c' m') v'
              -- Embed > constraints
              ftMono m [] c v = return (c, m, v)  -- We have finished
              ftMono m (Constraint_Inst (MonoType_Var v) p : cs) csAccum vs = do
                (m', c', v') <- ftReplacement v p m (cs ++ csAccum)
                ftMono m' c' [] (v' ++ vs)
              ftMono _ (Constraint_Inst _ _ : _) _ _ = error "Cannot handle non-variable > in ftype"
              ftMono m (c : cs) csAccum vs = ftMono m cs (c : csAccum) vs
              -- Introduce the constraints
              ftReplacement :: (Fresh m, Monad m, Functor m)
                            => TyVar -> PolyType -> MonoType -> [Constraint]
                            -> m (MonoType, [Constraint], [TyVar])
              ftReplacement _ PolyType_Bottom   m c = return (m, c, [])
              ftReplacement v (PolyType_Bind b) m c = do
                (x, r) <- unbind b
                (m', c', v') <- ftReplacement v r m c
                return (m', c', x:v')
              ftReplacement v (PolyType_Mono cs inner) m c =
                let m' = subst v inner m
                    c' = subst v inner c
                 in return (m', c' ++ cs, [])


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
orderConstraint (Constraint_Exists _) (Constraint_Exists _) = EQ
orderConstraint (Constraint_Exists _) _ = LT
orderConstraint _ (Constraint_Exists _) = GT
orderConstraint (Constraint_FType v1) (Constraint_FType v2) = compare v1 v2
orderConstraint (Constraint_FType _) _ = LT
orderConstraint _ (Constraint_FType _) = GT
orderConstraint (Constraint_Later _ _) (Constraint_Later _ _) = EQ
orderConstraint (Constraint_Later _ _) _ = LT
orderConstraint _ (Constraint_Later _ _) = GT
orderConstraint (Constraint_Cond _ _ _) (Constraint_Cond _ _ _) = EQ
orderConstraint (Constraint_Cond _ _ _) _ = LT
orderConstraint _ (Constraint_Cond _ _ _) = GT
orderConstraint Constraint_Inconsistent Constraint_Inconsistent = EQ

data MonoType = MonoType_Fam   String [MonoType]
              | MonoType_Var   TyVar
              | MonoType_Con   String [MonoType]
              | MonoType_Arrow MonoType MonoType
              deriving (Eq, Ord)

type MonoTypes = [MonoType]

pattern MonoType_Int       = MonoType_Con   "Int"    []
pattern MonoType_Char      = MonoType_Con   "Char"   []
pattern MonoType_String    = MonoType_List  MonoType_Char
pattern MonoType_List  t   = MonoType_Con   "List"   [t]
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

unarr :: [MonoType] -> MonoType -> MonoType
unarr []     m = m
unarr (a:as) m = a :-->: (unarr as m)

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
        hasCsFv :: [TyVar] -> Constraint -> Bool
        hasCsFv lst (Constraint_Inst  (MonoType_Var v) _) = v `elem` lst
        hasCsFv lst (Constraint_Equal (MonoType_Var v) _) = v `elem` lst
        hasCsFv lst (Constraint_Unify t1 t2) = any (`elem` lst) (fv t1 :: [TyVar]) || any (`elem` lst) (fv t2 :: [TyVar])
        hasCsFv lst (Constraint_Class _ t)   = any (`elem` lst) (fv t :: [TyVar])
        hasCsFv _ _ = False
        -- final close
        finalClose []     p = p
        finalClose (v:vs) p = PolyType_Bind (bind v (finalClose vs p))

data Constraint = Constraint_Unify MonoType MonoType
                | Constraint_Inst  MonoType PolyType
                | Constraint_Equal MonoType PolyType
                | Constraint_Class String [MonoType]
                | Constraint_Exists (Bind [TyVar] ([Constraint],[Constraint]))
                | Constraint_FType MonoType
                | Constraint_Later String [Constraint]
                | Constraint_Cond  [Constraint] [Constraint] [Constraint]
                | Constraint_Inconsistent

$(makePrisms ''Constraint)

instance Eq Constraint where
  Constraint_Unify m1 m2 == Constraint_Unify n1 n2 = m1 == n1 && m2 == n2
  Constraint_Inst  m1 m2 == Constraint_Inst  n1 n2 = m1 == n1 && m2 == n2
  Constraint_Equal m1 m2 == Constraint_Equal n1 n2 = m1 == n1 && m2 == n2
  Constraint_Class c1 a1 == Constraint_Class c2 a2 = c1 == c2 && a1 == a2
  Constraint_Exists b1   == Constraint_Exists b2   = runFreshM $ do
    s <- unbind2 b1 b2
    case s of
      Just (_,c1,_,c2) -> return $ c1 == c2
      Nothing          -> return False
  Constraint_Inconsistent  == Constraint_Inconsistent  = True
  Constraint_FType v1      == Constraint_FType v2      = v1 == v2
  Constraint_Later _ l1    == Constraint_Later _ l2    = l1 == l2
  Constraint_Cond c1 t1 e1 == Constraint_Cond c2 t2 e2 = c1 == c2 && t1 == t2 && e1 == e2
  _ == _ = False

data Axiom = Axiom_Unify (Bind [TyVar] (MonoType, MonoType))
           | Axiom_Class (Bind [TyVar] ([Constraint], String, [MonoType]))
           | Axiom_Injective String  -- Injective type families
           | Axiom_Defer     String  -- Deferred type families

isTresspasable :: Axiom -> Bool
isTresspasable (Axiom_Injective _) = True
isTresspasable (Axiom_Defer     _) = True
isTresspasable _                   = False

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
showPolyType' (PolyType_Mono cs m) = return $ showConstraintList cs ++ " => " ++ show m
showPolyType' PolyType_Bottom   = return "⊥"

showPolyTypeAsSystemF :: PolyType -> String
showPolyTypeAsSystemF = fst . runFreshM . sptF [] . nf
  where -- For polytypes
        sptF :: (Fresh m, Functor m, Monad m)
             => [(TyVar, String)] -> PolyType -> m (String, [TyVar])
        sptF mapping (PolyType_Bind b) = do
          (x, r) <- unbind b
          (typ, removed) <- sptF mapping r
          let typ' = if x `notElem` removed then "{" ++ show x ++ "} " ++ typ else typ
          return (typ', removed)
        sptF _ PolyType_Bottom = do
          v :: TyVar <- fresh (s2n "a")
          return ("{" ++ show v ++ "} " ++ show v, [])
        sptF mapping (PolyType_Mono cs m) = do
          let (inner, qs) = partition (is _Constraint_Equal) cs
          newMapping <- flip mapM inner $ \(Constraint_Equal (MonoType_Var v) p) ->
                                             do { pF <- sptF mapping p ; return (v, fst pF) }
          let completeMapping = mapping ++ newMapping
              qsF = map (sptFConstraint completeMapping) qs
              mF  = sptFMono completeMapping m
              typ = if null qs then mF else intercalate ", " qsF ++ " => " ++ mF
          return ( typ, map fst newMapping )  -- return variables replaced in this round
        -- For monotypes
        sptFMono :: [(TyVar, String)] -> MonoType -> String
        sptFMono m (MonoType_List t)      = "[" ++ sptFMono m t ++ "]"
        sptFMono m (MonoType_Tuple t1 t2) = "(" ++ sptFMono m t1 ++ "," ++ sptFMono m t2 ++ ")"
        sptFMono m (MonoType_Con c a)     = '\'':c ++ concatMap (\x -> " " ++ doParens (sptFMono m x)) a
        sptFMono m (MonoType_Fam c a)     = '^':c ++ concatMap (\x -> " " ++ doParens (sptFMono m x)) a
        sptFMono m (s :-->: t)            = doParens (sptFMono m s) ++ " -> " ++ sptFMono m t
        sptFMono m (MonoType_Var v)       = case lookup v m of
                                              Just p  -> p
                                              Nothing -> show v
        sptFMono _ _                      = error "Pattern matching check is not that good"
        -- For constraints
        sptFConstraint :: [(TyVar, String)] -> Constraint -> String
        sptFConstraint m (Constraint_Unify t p) = sptFMono m t ++ " ~ " ++ sptFMono m p
        sptFConstraint m (Constraint_Class c t) = "$" ++ c ++ " " ++ intercalate " " (map (doParens . sptFMono m) t)
        sptFConstraint m (Constraint_Inst  v p) = show v ++ " > " ++ fst (runFreshM (sptF m p))
        sptFConstraint _ (Constraint_Equal _ _) = error "this should never happen"
        sptFConstraint _ c                      = error ("constraint " ++ show c ++ " must not appear in a System F type")

instance Show MonoType where
  show (MonoType_List t)      = "[" ++ show t ++ "]"
  show (MonoType_Tuple t1 t2) = "(" ++ show t1 ++ "," ++ show t2 ++ ")"
  show (MonoType_Con c a)     = '\'':c ++ concatMap (\x -> " " ++ doParens (show x)) a
  show (MonoType_Fam c a)     = '^':c ++ concatMap (\x -> " " ++ doParens (show x)) a
  show (s :-->: t)            = doParens (show s) ++ " -> " ++ show t
  show (MonoType_Var v)       = show v
  show _                      = error "Pattern matching check is not that good"

{-
instance Show [Constraint] where
  show = runFreshM . showConstraintList
-}

instance Show Constraint where
  show = runFreshM . showConstraint

showConstraintList :: [Constraint] -> String
showConstraintList = runFreshM . showConstraintList'

showConstraintList' :: (Fresh m, Functor m) => [Constraint] -> m String
showConstraintList' [] = return "∅"
showConstraintList' l  = intercalate " ∧ " <$> mapM showConstraint l

showConstraint :: (Fresh m, Functor m) => Constraint -> m String
showConstraint (Constraint_Unify t p) = return $ show t ++ " ~ " ++ show p
showConstraint (Constraint_Inst  t p) = do p' <- showPolyType' p
                                           return $ show t ++ " > " ++ p'
showConstraint (Constraint_Equal t p) = do p' <- showPolyType' p
                                           return $ show t ++ " = " ++ p'
showConstraint (Constraint_Class c t) = do let ps = map (doParens . show) t
                                           return $ "$" ++ c ++ " " ++ intercalate " " ps
showConstraint (Constraint_Exists b)  = do (x, (q,c)) <- unbind b
                                           q' <- showConstraintList' q
                                           c' <- showConstraintList' c
                                           return $ "∃" ++ show x ++ "(" ++ q' ++ " => " ++ c' ++ ")"
showConstraint (Constraint_Inconsistent) = return "⊥"
showConstraint (Constraint_FType v)    = return $ "ftype[" ++ show v ++ "]"
showConstraint (Constraint_Later s l)  = do l' <- showConstraintList' l
                                            return $ "later \"" ++ s ++ "\" [" ++ l' ++ "]"
showConstraint (Constraint_Cond c t e) = do c' <- showConstraintList' c
                                            t' <- showConstraintList' t
                                            e' <- showConstraintList' e
                                            return $ "cond [" ++ c' ++ "] [" ++ t' ++ "] [" ++ e' ++ "]"

instance Show Axiom where
  show = runFreshM . showAxiom

showAxiom :: (Fresh m, Functor m) => Axiom -> m String
showAxiom (Axiom_Unify b) = do (xs, (lhs,rhs)) <- unbind b
                               return $ "∀" ++ show xs ++ " " ++ show lhs ++ " ~ " ++ show rhs
showAxiom (Axiom_Class b) = do (xs, (ctx,c,ms)) <- unbind b
                               let ps = map (doParens . show) ms
                               return $ "∀" ++ show xs ++ " " ++ show ctx ++
                                        " => $" ++ c ++ " " ++ intercalate " " ps
showAxiom (Axiom_Injective f) = return $ "injective ^" ++ f
showAxiom (Axiom_Defer f) = return $ "defer ^" ++ f
