{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Infer (
  Gathered(..)
, GMonad
, gather
, Solution
, solve
, toSubst
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
                         }
type GMonad = FreshMT (ReaderT Env (Either String))

lookupEnv :: TermVar -> GMonad PolyType
lookupEnv v = do optT <- asks (lookup v)
                 case optT of
                   Nothing -> throwError $ "Cannot find " ++ show v
                   Just t  -> return t

extendEnv :: TermVar -> PolyType -> GMonad a -> GMonad a
extendEnv v s = local ((v,s) :)

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

type Solution = [Constraint]

solve :: [Constraint] -> [Constraint] -> SMonad Solution
solve given wanted = do (g,_) <- whileApplicable (\c -> do
                           (canonicalG,apGC)  <- whileApplicable (stepOverList "canon" canon) c
                           (interactedG,apGI) <- whileApplicable (stepOverProductList "inter" interact_) canonicalG
                           return (interactedG, apGC || apGI)) given
                        (s,_) <- whileApplicable (\c -> do
                           (canonical,apC)  <- whileApplicable (stepOverList "canon" canon) c
                           (interacted,apI) <- whileApplicable (stepOverProductList "inter" interact_) canonical
                           (simplified,apS) <- whileApplicable (stepOverTwoLists "simpl" simplifies g) interacted
                           return (simplified, apC || apI || apS)) wanted
                        return s

canon :: Constraint -> SMonad SolutionStep
-- Basic unification
canon (Constraint_Unify t1 t2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2) | v1 == v2  -> return $ Applied []  -- Refl
                                     | v1 > v2   -> return $ Applied [Constraint_Unify t2 t1]  -- Orient
                                     | otherwise -> return NotApplicable
  (MonoType_Var _, _) -> return NotApplicable
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
canon (Constraint_Inst (MonoType_Var _) _)  = return NotApplicable
canon (Constraint_Inst x p) = do
  (c,t) <- instantiate p
  return $ Applied $ (Constraint_Unify x t) : c
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
interact_ :: Constraint -> Constraint -> SMonad SolutionStep
-- Two unifications
interact_ (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
-- Replace something over another constraint
interact_ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ (Constraint_Unify _ _) _ = return NotApplicable  -- only vars are replaced
interact_ _ (Constraint_Unify _ _) = return NotApplicable  -- treated symmetric cases
-- Two equalities
interact_ (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 `aeq` t2 = return NotApplicable
  | otherwise   = return NotApplicable
interact_ (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 `aeq` t2 = return NotApplicable
  | otherwise   = return NotApplicable
interact_ (Constraint_Inst _ _) (Constraint_Equal _ _) = return NotApplicable  -- treated sym
interact_ (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 `aeq` t2 = return NotApplicable
  | otherwise   = return NotApplicable
-- Existentials do not interact
interact_ (Constraint_Exists _ _ _) _ = return NotApplicable
interact_ _ (Constraint_Exists _ _ _) = return NotApplicable

simplifies :: Constraint -> Constraint -> SMonad SolutionStep
simplifies _ _ = return NotApplicable

toSubst :: [Constraint] -> ([Constraint], [(TyVar,MonoType)])
toSubst cs = let initialSubst = map (\x -> (x, mVar x)) (fv cs)
                 finalSubst = runSubst initialSubst
              in (map (substs finalSubst) (notUnifyConstraints cs), runSubst initialSubst)
  where runSubst s = let vars = concatMap (\(_,mt) -> fv mt) s
                         unif = concatMap (\v -> filter (\c -> case c of
                                                                 Constraint_Unify (MonoType_Var v1) _ -> v1 == v
                                                                 _ -> False) cs) vars
                         sub = map (\(Constraint_Unify (MonoType_Var v) t) -> (v,t)) unif
                      in case s of
                           [] -> s
                           _  -> map (\(v,t) -> (v, substs sub t)) s
        notUnifyConstraints = filter (\c -> case c of
                                              Constraint_Unify _ _ -> False
                                              _ -> True)

closeType :: [Constraint] -> MonoType -> PolyType
-- closeType bs cs m = -- TODO: change this stupid implementation
closeType ((Constraint_Inst (MonoType_Var v) t) : rest) m =
  PolyType_Inst $ bind (v,embed t) (closeType rest m)
closeType ((Constraint_Equal (MonoType_Var v) t) : rest) m =
  PolyType_Equal $ bind (v,embed t) (closeType rest m)
closeType (_ : rest) m = closeType rest m
closeType [] m = PolyType_Mono m
