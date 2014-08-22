{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Infer (
  Result(..)
, infer
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

data Result = Result { ty      :: MonoType
                     , annTerm :: AnnTerm
                     , givenC  :: [Constraint]
                     , wantedC :: [Constraint]
                     }
type TcMonad = FreshMT (ReaderT Env (Either String))

lookupEnv :: TermVar -> TcMonad PolyType
lookupEnv v = do optT <- asks (lookup v)
                 case optT of
                   Nothing -> throwError $ "Cannot find " ++ show v
                   Just t  -> return t

extendEnv :: TermVar -> PolyType -> TcMonad a -> TcMonad a
extendEnv v s = local ((v,s) :)

infer :: Term -> TcMonad Result
infer (Term_IntLiteral n) =
  return $ Result intTy (AnnTerm_IntLiteral n intTy) [] []
infer (Term_Var x) =
  do sigma <- lookupEnv x
     tau <- mVar <$> fresh (string2Name "tau")
     return $ Result tau (AnnTerm_Var (translate x) tau)
                     [] [Constraint_Inst tau sigma]
infer (Term_Abs b) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Result tau ann ex c <- extendEnv x (pVar alpha) $ infer e
     let arrow = mVar alpha --> tau
     return $ Result arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
infer (Term_AbsAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do (x,e) <- unbind b
     Result tau ann ex c <- extendEnv x mt $ infer e
     let arrow = m --> tau
     return $ Result arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
infer (Term_AbsAnn b t) = -- Case polytype
  do (x,e) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     alpha <- fresh (string2Name "alpha")
     Result tau ann ex c <- extendEnv x t $ infer e
     let arrow = mVar alpha --> tau
     return $ Result arrow (AnnTerm_AbsAnn (bind (translate x) ann) t arrow)
                     (ex ++ [Constraint_Equal (mVar alpha) t]) c
infer (Term_App e1 e2) =
  do Result tau1 ann1 ex1 c1 <- infer e1
     Result tau2 ann2 ex2 c2 <- infer e2
     alpha <- mVar <$> fresh (string2Name "alpha")
     return $ Result alpha (AnnTerm_App ann1 ann2 alpha)
                     (ex1 ++ ex2)
                     (c1 ++ c2 ++ [Constraint_Unify tau1 (tau2 --> alpha)])
infer (Term_Let b) =
  do ((x, unembed -> e1),e2) <- unbind b
     Result tau1 ann1 ex1 c1 <- infer e1
     Result tau2 ann2 ex2 c2 <- extendEnv x (PolyType_Mono tau1) $ infer e2
     return $ Result tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                     (ex1 ++ ex2) (c1 ++ c2)
infer (Term_LetAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     Result tau1 ann1 ex1 c1 <- infer e1
     Result tau2 ann2 ex2 c2 <- extendEnv x mt $ infer e2
     return $ Result tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                     (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
{-
infer (Term_LetAnn b t) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     Result tau1 ann1 ex1 c1 <- infer e1
     Result tau2 ann2 ex2 c2 <- extendEnv x mt $ infer e2
     return $ Result tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                     (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
-}

type Solution = [Constraint]

solve :: [Constraint] -> [Constraint] -> SMonad Solution
solve given wanted = do (_g,_) <- whileApplicable (stepOverList "canon" canon) given
                        (s,_) <- whileApplicable (\c -> do
                           (canonical,apC)  <- whileApplicable (stepOverList "canon" canon) c
                           (interacted,apI) <- whileApplicable (stepOverProductList "inter" interact_) canonical
                           return (interacted, apC || apI)) wanted
                        return s

canon :: Constraint -> SMonad StepResult
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
canon (Constraint_Inst _ PolyType_Bottom)   = return $ Applied []
-- Convert from monotype > into monotype ~
canon (Constraint_Inst t (PolyType_Mono m)) = return $ Applied [Constraint_Unify t m]
canon (Constraint_Inst (MonoType_Var _) _)  = return NotApplicable
canon (Constraint_Inst x p) = do
  (c,t) <- instantiate p
  return $ Applied $ (Constraint_Unify x t) : c
  
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
interact_ :: Constraint -> Constraint -> SMonad StepResult
interact_ (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
interact_ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
interact_ _ _ = return NotApplicable

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
