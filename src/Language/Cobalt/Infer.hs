{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Infer (
  Env
, infer
, Solution
, solve
, prettyType
) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Error
import Unbound.LocallyNameless

import Language.Cobalt.Syntax

import Debug.Trace

type Env = [(TermVar, PolyType)]
type Result = (MonoType, AnnTerm, [Constraint], [BasicConstraint])
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
  return (intTy, AnnTerm_IntLiteral n intTy,
          [], [])
infer (Term_Var x) =
  do sigma <- lookupEnv x
     tau <- mVar <$> fresh (string2Name "tau")
     return (tau, AnnTerm_Var (translate x) tau,
             [Constraint_Inst tau sigma], [])
infer (Term_Abs b) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     (tau,ann,c,ex) <- extendEnv x (pVar alpha) $ infer e
     let arrow = mVar alpha --> tau
     return (arrow, AnnTerm_Abs (bind (translate x) ann) arrow,
             c, ex)
infer (Term_AbsAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do (x,e) <- unbind b
     (tau,ann,c,ex) <- extendEnv x mt $ infer e
     let arrow = m --> tau
     return (arrow, AnnTerm_Abs (bind (translate x) ann) arrow,
             c, ex)
infer (Term_AbsAnn b t) = -- Case polytype
  do (x,e) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     alpha <- fresh (string2Name "alpha")
     (tau,ann,c,ex) <- extendEnv x t $ infer e
     let arrow = mVar alpha --> tau
     return (arrow, AnnTerm_Abs (bind (translate x) ann) arrow,
             c, ex ++ [BasicConstraint_Equal alpha t])
infer (Term_App e1 e2) =
  do (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- infer e2
     alpha <- mVar <$> fresh (string2Name "alpha")
     return (alpha, AnnTerm_App ann1 ann2 alpha,
             c1 ++ c2 ++ [Constraint_Unify tau1 (tau2 --> alpha)],
             ex1 ++ ex2)
infer (Term_Let b) =
  do ((x, unembed -> e1),e2) <- unbind b
     (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- extendEnv x (PolyType_Mono tau1) $ infer e2
     return (tau2, AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2,
             c1 ++ c2, ex1 ++ ex2)
infer (Term_LetAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- extendEnv x mt $ infer e2
     return (tau2, AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2,
             c1 ++ c2 ++ [Constraint_Unify tau1 m], ex1 ++ ex2)
{-
infer (Term_LetAnn b t) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     -- Check that dom(t) `subset` ftv(\Gamma)
     (tau1,ann1,c1,ex1) <- infer e1
     (tau2,ann2,c2,ex2) <- extendEnv x mt $ infer e2
     return (tau2, AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2,
             c1 ++ c2 ++ [Constraint_Unify tau1 m], ex1 ++ ex2)
-}

type Solution = [Constraint]
type SMonad = FreshMT (Either String)

solve :: [BasicConstraint] -> [Constraint] -> SMonad Solution
solve given wanted = do (s,_) <- whileApplicable (\c -> do
                           (canonical,apC)  <- whileApplicable (stepOverList "canon" canon) c
                           (interacted,apI) <- whileApplicable (stepOverProductList "inter" interact_) canonical
                           return (interacted, apC || apI)) wanted
                        return s

data StepResult = NotApplicable | Applied [Constraint]

whileApplicable :: ([Constraint] -> SMonad ([Constraint], Bool))
                -> [Constraint] -> SMonad ([Constraint], Bool)
whileApplicable f c = innerApplicable' c False
  where innerApplicable' cs atAll = do
          r <- f cs
          case r of
            (_,   False) -> return (cs, atAll)
            (newC,True)  -> innerApplicable' newC True

stepOverList :: String -> (Constraint -> SMonad StepResult)
             -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverList s f lst = stepOverList' lst [] False False
  where -- Finish cases: last two args are changed-in-this-loop, and changed-at-all
        stepOverList' [] accum True  _     = stepOverList' accum [] False True
        stepOverList' [] accum False atAll = return (accum, atAll)
        -- Rest of cases
        stepOverList' (x:xs) accum thisLoop atAll = do
          r <- f x
          case r of
            NotApplicable -> stepOverList' xs (x:accum) thisLoop atAll
            Applied newX  -> myTrace (s ++ " " ++ show x ++ " ==> " ++ show newX) $
                             stepOverList' xs (newX ++ accum) True True

stepOverProductList :: String -> (Constraint -> Constraint -> SMonad StepResult)
                    -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverProductList s f lst = stepOverProductList' lst [] False
  where stepOverProductList' [] accum atAll = return (accum, atAll)
        stepOverProductList' (x:xs) accum atAll =
          do r <- stepOverList (s ++ " " ++ show x) (f x) (xs ++ accum)
             case r of
               (_,     False) -> stepOverProductList' xs (x:accum) atAll
               (newLst,True)  -> stepOverProductList' (x:newLst) [] True

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

prettyType :: MonoType -> Solution -> PolyType
prettyType mt sln = PolyType_Mono (prettyTypePhase1 mt sln)

prettyTypePhase1 :: MonoType -> [Constraint] -> MonoType
prettyTypePhase1 mt cs =
  let s = concatMap (\v -> filter (\c -> case c of
                                           Constraint_Unify (MonoType_Var v1) _ | v1 == v -> True
                                           Constraint_Unify _ (MonoType_Var v1) | v1 == v -> True
                                           _ -> False) cs) (fv mt)
      applySubst m [] = m
      applySubst m ((Constraint_Unify (MonoType_Var v1) t1) : rest) | v1 `elem` fv mt
        = applySubst (subst v1 t1 m) rest
      applySubst m ((Constraint_Unify t1 (MonoType_Var v1)) : rest) | v1 `elem` fv mt
        = applySubst (subst v1 t1 m) rest
      applySubst _ _ = error "This should never happen"
   in case s of
        [] -> mt
        _  -> applySubst mt s

myTrace :: String -> a -> a
-- myTrace = trace
myTrace _ x = x
