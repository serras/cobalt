{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Infer (
  Gathered(..)
, GMonad
, gather
, Solution(..)
, solve
, toSolution
, closeType
) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error
import Unbound.LocallyNameless

import Language.Cobalt.Step
import Language.Cobalt.Syntax

data Gathered = Gathered { ty      :: MonoType
                         , annTerm :: AnnTerm
                         , givenC  :: [Constraint]
                         , wantedC :: [Constraint]
                         } deriving Show
type GMonad = ReaderT Env (ErrorT String FreshM)

lookupEnv :: TermVar -> GMonad PolyType
lookupEnv v = do optT <- asks (lookup v)
                 case optT of
                   Nothing -> throwError $ "Cannot find " ++ show v
                   Just t  -> return t

extendEnv :: TermVar -> PolyType -> GMonad a -> GMonad a
extendEnv v s = local ((v,s) :)

-- Phase 1: constraint gathering

gather :: Term -> GMonad Gathered
gather (Term_IntLiteral n) =
  return $ Gathered intTy (AnnTerm_IntLiteral n intTy) [] []
gather (Term_Var x) =
  do sigma <- lookupEnv x
     tau <- mVar <$> fresh (string2Name "tau")
     return $ Gathered tau (AnnTerm_Var (translate x) tau)
                       [] [Constraint_Inst tau sigma]
gather (Term_Abs b) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x (pVar alpha) $ gather e
     let arrow = mVar alpha --> tau
     return $ Gathered arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
gather (Term_AbsAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do (x,e) <- unbind b
     Gathered tau ann ex c <- extendEnv x mt $ gather e
     let arrow = m --> tau
     return $ Gathered arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
gather (Term_AbsAnn b t) = -- Case polytype
  do (x,e) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x t $ gather e
     let arrow = mVar alpha --> tau
     return $ Gathered arrow (AnnTerm_AbsAnn (bind (translate x) ann) t arrow)
                     (ex ++ [Constraint_Equal (mVar alpha) t]) c
gather (Term_App e1 e2) =
  do Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- gather e2
     alpha <- mVar <$> fresh (string2Name "alpha")
     return $ Gathered alpha (AnnTerm_App ann1 ann2 alpha)
                       (ex1 ++ ex2)
                       (c1 ++ c2 ++ [Constraint_Unify tau1 (tau2 --> alpha)])
gather (Term_Let b) =
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x (PolyType_Mono tau1) $ gather e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2)
gather (Term_LetAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x mt $ gather e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
{-
gather (Term_LetAnn b t) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x mt $ gather e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
-}

-- Phase 2: constraint solving

data Solution = Solution { smallGiven   :: [Constraint]
                         , residual     :: [Constraint]
                         , substitution :: [(TyVar, MonoType)]
                         } deriving Show

solve :: [Constraint] -> [Constraint] -> SMonad Solution
solve g w = myTrace ("Solve " ++ show g ++ " ||- " ++ show w) $ simpl g w

-- Phase 2a: simplifier

simpl :: [Constraint] -> [Constraint] -> SMonad Solution
simpl given wanted = do (g,_) <- whileApplicable (\c -> do
                           (canonicalG,apGC)  <- whileApplicable (stepOverList "canon" canon') c
                           (interactedG,apGI) <- whileApplicable (stepOverProductList "inter" interact_) canonicalG
                           return (interactedG, apGC || apGI)) given
                        (s,_) <- whileApplicable (\c -> do
                           (canonical,apC)  <- whileApplicable (stepOverList "canon" canon') c
                           (interacted,apI) <- whileApplicable (stepOverProductList "inter" interact_) canonical
                           (simplified,apS) <- whileApplicable (stepOverTwoLists "simpl" simplifies g) interacted
                           return (simplified, apC || apI || apS)) wanted
                        return $ toSolution g s

canon' :: [Constraint] -> Constraint -> SMonad SolutionStep
canon' _ = canon

canon :: Constraint -> SMonad SolutionStep
-- Basic unification
canon (Constraint_Unify t1 t2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2) | v1 == v2  -> return $ Applied []  -- Refl
                                     | v1 > v2   -> return $ Applied [Constraint_Unify t2 t1]  -- Orient
                                     | otherwise -> return NotApplicable
  (MonoType_Var v, _) | v `elem` fv t2 -> throwError $ "Infinite type: " ++ show t1 ++ " ~ " ++ show t2
                      | otherwise      -> return NotApplicable
  (t, v@(MonoType_Var _)) -> return $ Applied [Constraint_Unify v t]  -- Orient
  -- Next are Tdec and Faildec
  (MonoType_Arrow s1 r1, MonoType_Arrow s2 r2) ->
    return $ Applied [Constraint_Unify s1 s2, Constraint_Unify r1 r2]
  (MonoType_Con c1 a1, MonoType_Con c2 a2)
    | c1 == c2 && length a1 == length a2 -> return $ Applied $ zipWith Constraint_Unify a1 a2
  (_, _) -> throwError $ "Different constructor heads: " ++ show t1 ++ " ~ " ++ show t2
-- Convert from monotype > or = into monotype ~
canon (Constraint_Inst  t (PolyType_Mono m)) = return $ Applied [Constraint_Unify t m]
canon (Constraint_Equal t (PolyType_Mono m)) = return $ Applied [Constraint_Unify t m]
-- This is not needed
canon (Constraint_Inst _ PolyType_Bottom)   = return $ Applied []
-- Constructors and <= and ==
canon (Constraint_Inst (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Inst (MonoType_Var v) nfP]
canon (Constraint_Inst x p) = do
  (c,t) <- instantiate p  -- Perform instantiation
  return $ Applied $ (Constraint_Unify x t) : c
canon (Constraint_Equal (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Equal (MonoType_Var v) nfP]
canon (Constraint_Equal t1 t2) = throwError $ "Constructor and polytype cannot be equal: " ++ show t1 ++ " == " ++ show t2
-- Rest
canon _ = return NotApplicable

instantiate :: PolyType -> SMonad ([Constraint], MonoType)
instantiate (PolyType_Inst b) = do
  ((v,unembed -> s),i) <- unbind b
  (c,t) <- instantiate i
  return ((Constraint_Inst (mVar v) s) : c, t)
instantiate (PolyType_Equal b) = do
  ((v,unembed -> s),i) <- unbind b
  (c,t) <- instantiate i
  return ((Constraint_Equal (mVar v) s) : c, t)
instantiate (PolyType_Mono m) = return ([],m)
instantiate PolyType_Bottom = do
  v <- fresh (string2Name "b")
  return ([], mVar v)

-- Change w.r.t. OutsideIn -> return only second constraint
interact_ :: [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
-- Two unifications
interact_ _ (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
-- Replace something over another constraint
interact_ _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ _ (Constraint_Unify _ _) _ = return NotApplicable  -- only vars are replaced
interact_ _ _ (Constraint_Unify _ _) = return NotApplicable  -- treated symmetric cases
-- Two equalities
interact_ ctx (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = do b <- checkEquivalence ctx p1 p2
                   return $ if b then Applied [] else NotApplicable
  | otherwise = return NotApplicable
interact_ ctx (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = do b <- checkSubsumption ctx p2 p1
                   return $ if b then Applied [] else NotApplicable
  | otherwise = return NotApplicable
interact_ _ (Constraint_Inst _ _) (Constraint_Equal _ _) = return NotApplicable  -- treated sym
interact_ ctx (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = (do b <- checkSubsumption ctx p2 p1
                    return $ if b then Applied [] else NotApplicable)
                `catchError`
                -- If it cannot match, check the other direction
                -- If this returns fail, it means that we could not
                -- match in any direction, and thus we should fail
                (\_ -> do _ <- checkSubsumption ctx p1 p2
                          return $ NotApplicable)
  | otherwise = return NotApplicable
-- Existentials do not interact
interact_ _ (Constraint_Exists _ _ _) _ = return NotApplicable
interact_ _ _ (Constraint_Exists _ _ _) = return NotApplicable

simplifies :: [Constraint] -> [Constraint]
           -> Constraint -> Constraint -> SMonad SolutionStep
-- WARNING: The unify part should be similar to the one in interact_
simplifies _ _ (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1, t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
simplifies _ _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
simplifies _ _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
simplifies _ _ (Constraint_Unify _ _) _ = return NotApplicable  -- only vars are replaced
-- Simplify with a given > constraint
simplifies ctxG ctxW (Constraint_Inst (MonoType_Var v1) t1) (Constraint_Unify (MonoType_Var v2) t2)
  | v1 == v2 = do _ <- checkSubsumption (ctxG ++ ctxW) t1 (PolyType_Mono t2)  -- check if correct
                  return NotApplicable
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Inst (MonoType_Var v1) t1) (Constraint_Inst (MonoType_Var v2) t2)
  | v1 == v2 = (do b <- checkSubsumption (ctxG ++ ctxW) t2 t1  -- t2 <= t1 < v
                   return $ if b then Applied [] else NotApplicable)
               `catchError`
               -- If it cannot match, check the other direction
               -- If this returns fail, it means that we could not
               -- match in any direction, and thus we should fail
               (\_ -> do _ <- checkSubsumption (ctxG ++ ctxW) t1 t2
                         return $ NotApplicable)
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Inst (MonoType_Var v1) t1) (Constraint_Equal (MonoType_Var v2) t2)
  | v1 == v2 = do _ <- checkSubsumption (ctxG ++ ctxW) t2 t1  -- v = t2 <= t1 < v
                  return NotApplicable
  | otherwise = return NotApplicable
simplifies _ _ (Constraint_Inst _ _) _ = return NotApplicable -- only work with vars
-- Simplify with a given = constraint
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Unify (MonoType_Var v2) t2)
  | v1 == v2 = do _ <- checkEquivalence (ctxG ++ ctxW) t1 (PolyType_Mono t2)  -- check if correct
                  return NotApplicable
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Inst (MonoType_Var v2) t2)
  | v1 == v2 = do _ <- checkSubsumption (ctxG ++ ctxW) t2 t1  -- check subsumption
                  return NotApplicable
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Equal (MonoType_Var v2) t2)
  | v1 == v2 = do _ <- checkEquivalence (ctxG ++ ctxW) t1 t2  -- check equivalence
                  return NotApplicable
  | otherwise = return NotApplicable
simplifies _ _ (Constraint_Equal _ _) _ = return NotApplicable -- only work with vars
-- No exists
simplifies _ _ (Constraint_Exists _ _ _) _ = return NotApplicable

-- Checks that p1 <= p2, that is, that p2 is an instance of p1
-- Fails if not unification is possible between bodies
-- TODO: What to do if solve returns _|_
checkSubsumption :: [Constraint] -> PolyType -> PolyType -> SMonad Bool
checkSubsumption ctx p1 p2 =
  if p1 `aeq` p2 then return True -- fast alpha-equivalence check
  else do (q1,t1) <- splitType p1
          (q2,t2) <- splitType p2
          case match t1 t2 of
            Nothing -> throwError $ "Subsumption check failed: " ++ show t1 ++ " <= " ++ show t2
            Just m  -> do let q1' = substs m q1
                              t1' = substs m t1
                          s <- solve (ctx ++ q2) (Constraint_Unify t1' t2 : q1')
                          return $ null (residual s)

-- Checks that p1 == p2, that is, that they are equivalent
checkEquivalence :: [Constraint] -> PolyType -> PolyType -> SMonad Bool
checkEquivalence ctx p1 p2 = (&&) <$> checkSubsumption ctx p1 p2
                                  <*> checkSubsumption ctx p2 p1

-- Checks whether t2 is [a -> t]t1 for some t
match :: MonoType -> MonoType -> Maybe [(TyVar,MonoType)]
match (MonoType_Var v) m = return [(v,m)]
match (MonoType_Con c1 a1) (MonoType_Con c2 a2)
  | c1 == c2  = concat <$> zipWithM match a1 a2
  | otherwise = Nothing
match (MonoType_Arrow s1 r1) (MonoType_Arrow s2 r2) = do
  m1 <- match s1 s2
  m2 <- match r1 r2
  return $ m1 ++ m2
match _ _ = Nothing

-- Phase 2b: convert to solution

toSolution :: [Constraint] -> [Constraint] -> Solution
toSolution gs rs = let initialSubst = map (\x -> (x, mVar x)) (fv rs)
                       finalSubst   = runSubst initialSubst
                       doFinalSubst = map (substs finalSubst)
                    in Solution (doFinalSubst gs) (doFinalSubst (notUnifyConstraints rs)) (runSubst initialSubst)
  where runSubst s = let vars = concatMap (\(_,mt) -> fv mt) s
                         unif = concatMap (\v -> filter (isVarUnifyConstraint (== v)) rs) vars
                         sub = map (\(Constraint_Unify (MonoType_Var v) t) -> (v,t)) unif
                      in case s of
                           [] -> s
                           _  -> map (\(v,t) -> (v, substs sub t)) s
        notUnifyConstraints = filter (not . isVarUnifyConstraint (const True))

isVarUnifyConstraint :: (TyVar -> Bool) -> Constraint -> Bool
isVarUnifyConstraint extra (Constraint_Unify (MonoType_Var v) _) = extra v
isVarUnifyConstraint _ _ = False
