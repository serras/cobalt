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
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.List (insert, find, delete, nub, partition)
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
                         , touchable    :: [TyVar]
                         } deriving Show

solve :: [Constraint] -> [Constraint] -> [TyVar] -> (ErrorT String FreshM) Solution
solve g w t = do evalStateT (solve' g w) t

solve' :: [Constraint] -> [Constraint] -> SMonad Solution
solve' g w = do myTrace ("Solve " ++ show g ++ " ||- " ++ show w) $ simpl g w

-- Utils for touchable variables

makeTouchable :: Monad m => TyVar -> StateT [TyVar] m ()
makeTouchable x = modify (insert x)

{-
makeTouchables :: Monad m => [TyVar] -> StateT [TyVar] m ()
makeTouchables x = modify (union x)
-}

isTouchable :: Monad m => TyVar -> StateT [TyVar] m Bool
isTouchable x = gets (x `elem`)

-- Phase 2a: simplifier

simpl :: [Constraint] -> [Constraint] -> SMonad Solution
simpl given wanted = do (g,_) <- whileApplicable (\c -> do
                           (canonicalG,apGC)  <- whileApplicable (stepOverList "canon" canon') c
                           (interactedG,apGI) <- stepOverProductList "inter" interact_ canonicalG
                           return (interactedG, apGC || apGI)) given
                        (s,_) <- whileApplicable (\c -> do
                           (interacted,apI) <- whileApplicable (\cc -> do
                             (canonical2,apC2)  <- whileApplicable (stepOverList "canon" canon') cc
                             (interacted2,apI2) <- stepOverProductList "inter" interact_ canonical2
                             return (interacted2, apC2 || apI2)) c
                           (simplified,apS) <- stepOverTwoLists "simpl" simplifies g interacted
                           return (simplified, apI || apS)) wanted
                        v <- get
                        myTrace ("touchables: " ++ show v) $ return $ toSolution g s v

canon' :: [Constraint] -> Constraint -> SMonad SolutionStep
canon' _ = canon

canon :: Constraint -> SMonad SolutionStep
-- Basic unification
canon (Constraint_Unify t1 t2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2  -> return $ Applied []  -- Refl
    | otherwise -> do touch1 <- isTouchable v1
                      touch2 <- isTouchable v2
                      case (touch1, touch2) of
                       (False, False) -> throwError $ "Unifying non-touchable variables: " ++ show v1 ++ " ~ " ++ show v2
                       (True,  False) -> return NotApplicable
                       (False, True)  -> return $ Applied [Constraint_Unify t2 t1]
                       (True,  True)  -> if v1 > v2 then return $ Applied [Constraint_Unify t2 t1]  -- Orient
                                                    else return NotApplicable
    | otherwise -> return NotApplicable
  (MonoType_Var v, _)
    | v `elem` fv t2 -> throwError $ "Infinite type: " ++ show t1 ++ " ~ " ++ show t2
    | otherwise      -> do b <- isTouchable v
                           if b then return NotApplicable
                                else throwError $ "Unifying non-touchable variable: " ++ show v ++ " ~ " ++ show t2
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
  (c,t) <- instantiate p True  -- Perform instantiation
  return $ Applied $ (Constraint_Unify x t) : c
canon (Constraint_Equal (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Equal (MonoType_Var v) nfP]
-- We need to instantiate, but keep record
-- of those variables which are not touchable
canon (Constraint_Equal x p) = do
  (c,t) <- instantiate p False  -- Perform instantiation
  return $ Applied $ (Constraint_Unify x t) : c
-- Rest
canon _ = return NotApplicable

instantiate :: PolyType -> Bool -> SMonad ([Constraint], MonoType)
instantiate (PolyType_Inst b) tch = do
  ((v,unembed -> s),i) <- unbind b
  when tch $ makeTouchable v
  (c,t) <- instantiate i tch
  return ((Constraint_Inst (mVar v) s) : c, t)
instantiate (PolyType_Equal b) tch = do
  ((v,unembed -> s),i) <- unbind b
  when tch $ makeTouchable v
  (c,t) <- instantiate i tch
  return ((Constraint_Equal (mVar v) s) : c, t)
instantiate (PolyType_Mono m) _tch = return ([],m)
instantiate PolyType_Bottom tch = do
  v <- fresh (string2Name "b")
  when tch $ makeTouchable v
  return ([], mVar v)

-- Perform common part of interact_ and simplifies
-- dealing with unifications in canonical form
unifyInteract :: Constraint -> Constraint -> SMonad SolutionStep
unifyInteract (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
-- Replace something over another constraint
unifyInteract (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
unifyInteract (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
-- Constructors are not canonical
unifyInteract (Constraint_Unify _ _) _ = return NotApplicable
unifyInteract _ _ = return NotApplicable

-- Change w.r.t. OutsideIn -> return only second constraint
interact_ :: [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
-- First is an unification
interact_ _ c1@(Constraint_Unify _ _) c2 = unifyInteract c1 c2
interact_ _ _ (Constraint_Unify _ _)     = return NotApplicable -- treated sym
-- == and >=
interact_ ctx (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = checkEquivalence ctx p1 p2
  | otherwise = return NotApplicable
interact_ ctx (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = checkSubsumption ctx p2 p1
  | otherwise = return NotApplicable
interact_ _ (Constraint_Inst _ _) (Constraint_Equal _ _) = return NotApplicable  -- treated sym
interact_ ctx (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = do equiv <- areEquivalent ctx p1 p2
                   if equiv then checkEquivalence ctx p1 p2
                   else do (Applied q,p) <- findLub ctx p1 p2
                           return $ Applied (Constraint_Inst t1 p : q)
  | otherwise = return NotApplicable
-- Existentials do not interact
interact_ _ (Constraint_Exists _ _ _) _ = return NotApplicable
interact_ _ _ (Constraint_Exists _ _ _) = return NotApplicable

-- Very similar to interact_, but taking care of symmetric cases
simplifies :: [Constraint] -> [Constraint]
           -> Constraint -> Constraint -> SMonad SolutionStep
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
  | v1 == v2  = checkSubsumption (ctxG ++ ctxW) t1 (PolyType_Mono t2)
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Inst (MonoType_Var v1) t1) (Constraint_Inst (MonoType_Var v2) t2)
  | v1 == v2  = checkSubsumption (ctxG ++ ctxW) t2 t1  -- t2 <= t1 < v
                `catchError`
                -- If it cannot match, check the other direction
                -- If this returns fail, it means that we could not
                -- match in any direction, and thus we should fail
                (\_ -> do _ <- checkSubsumption (ctxG ++ ctxW) t1 t2
                          return $ NotApplicable)
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Inst (MonoType_Var v1) t1) (Constraint_Equal (MonoType_Var v2) t2)
  | v1 == v2  = do _ <- checkSubsumption (ctxG ++ ctxW) t2 t1
                   return NotApplicable
  | otherwise = return NotApplicable
simplifies _ _ (Constraint_Inst _ _) _ = return NotApplicable -- only work with vars
-- Simplify with a given = constraint
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Unify (MonoType_Var v2) t2)
  | v1 == v2  = checkEquivalence (ctxG ++ ctxW) t1 (PolyType_Mono t2)
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Inst (MonoType_Var v2) t2)
  | v1 == v2  = checkSubsumption (ctxG ++ ctxW) t2 t1
  | otherwise = return NotApplicable
simplifies ctxG ctxW (Constraint_Equal (MonoType_Var v1) t1) (Constraint_Equal (MonoType_Var v2) t2)
  | v1 == v2  = checkEquivalence (ctxG ++ ctxW) t1 t2
  | otherwise = return NotApplicable
simplifies _ _ (Constraint_Equal _ _) _ = return NotApplicable -- only work with vars
-- No exists
simplifies _ _ (Constraint_Exists _ _ _) _ = return NotApplicable

findLub :: [Constraint] -> PolyType -> PolyType -> SMonad (SolutionStep, PolyType)
findLub ctx p1 p2 = do
  -- equiv <- areEquivalent ctx p1 p2
  if p1 `aeq` p2 then return (Applied [], p1)
  else do (q1,t1,v1)  <- splitType p1
          (q2,t2,v2) <- splitType p2
          tau <- fresh $ string2Name "tau"
          let cs = [Constraint_Unify (mVar tau) t1, Constraint_Unify (mVar tau) t2]
          tch <- get
          Solution _ r s _ <- lift $ solve ctx (cs ++ q1 ++ q2) (tau : tch ++ v1 ++ v2)
          let s' = substitutionInTermsOf tch s
              r' = map (substs s') r ++ map (\(v,t) -> Constraint_Unify (MonoType_Var v) t) s'
              (floatR, closeR) = partition (\c -> all (`elem` tch) (fv c)) r'
          return (Applied floatR, closeTypeWithException closeR (substs s' (mVar tau)) (`elem` tch))

-- Returning NotApplicable means that we could not prove it
-- because some things would float out of the types
checkSubsumption :: [Constraint] -> PolyType -> PolyType -> SMonad SolutionStep
checkSubsumption ctx p1 p2 =
  if p1 `aeq` p2 then return (Applied [])
  else do (q1,t1,v1)  <- splitType p1
          (q2,t2,_v2) <- splitType p2
          tch <- get
          Solution _ r s _ <- lift $ solve (ctx ++ q2) (Constraint_Unify t1 t2 : q1) (tch `union` v1)
          let s' = substitutionInTermsOf tch s
              r' = map (substs s') r ++ map (\(v,t) -> Constraint_Unify (MonoType_Var v) t)
                                            (filter (\(v,_) -> v `elem` tch) s')
              allFvs = nub $ concatMap fv r'
          if all (`elem` tch) allFvs
             then return $ Applied r'
             else return NotApplicable

substitutionInTermsOf :: [TyVar] -> [(TyVar,MonoType)] -> [(TyVar,MonoType)]
substitutionInTermsOf tys s =
  case find (\c -> case c of
                     (_,MonoType_Var v) -> v `elem` tys
                     _                  -> False) s of
    Nothing -> s
    Just (out,inn) -> map (\(v,t) -> (v, subst out inn t)) $ delete (out,inn) s

areEquivalent :: [Constraint] -> PolyType -> PolyType -> SMonad Bool
areEquivalent ctx p1 p2 = (do _ <- checkEquivalence ctx p1 p2
                              return True)
                          `catchError` (\_ -> return False)

-- Checks that p1 == p2, that is, that they are equivalent
checkEquivalence :: [Constraint] -> PolyType -> PolyType -> SMonad SolutionStep
checkEquivalence _ p1 p2 | p1 `aeq` p2 = return $ Applied []
checkEquivalence ctx p1 p2 = do
  c1 <- checkSubsumption ctx p1 p2
  c2 <- checkSubsumption ctx p2 p1
  case (c1,c2) of
    (NotApplicable, _) -> throwError $ "Equivalence check failed: " ++ show p1 ++ " = " ++ show p2
    (_, NotApplicable) -> throwError $ "Equivalence check failed: " ++ show p1 ++ " = " ++ show p2
    (Applied a1, Applied a2) -> return $ Applied (a1 ++ a2)

-- Phase 2b: convert to solution

toSolution :: [Constraint] -> [Constraint] -> [TyVar] -> Solution
toSolution gs rs vs = let initialSubst = map (\x -> (x, mVar x)) (fv rs)
                          finalSubst   = runSubst initialSubst
                          doFinalSubst = map (substs finalSubst)
                       in Solution (doFinalSubst gs)
                                   (doFinalSubst (notUnifyConstraints rs))
                                   (runSubst initialSubst) vs
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
