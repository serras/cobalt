{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Cobalt.Solver (
  SMonad
, Solution(..)
, solve
, toSolution
) where

import Control.Applicative ((<$>))
import Control.Lens.Extras
import Control.Monad.Except
import Control.Monad.State
import Data.List (insert, find, delete, partition, nub)
import Unbound.LocallyNameless

import Language.Cobalt.Solver.Step
import Language.Cobalt.Types
import Language.Cobalt.Util ()

-- Phase 2: constraint solving

data Solution = Solution { smallGiven   :: [Constraint]
                         , residual     :: [Constraint]
                         , substitution :: [(TyVar, MonoType)]
                         , touchable    :: [TyVar]
                         } deriving Show

solve :: [Constraint] -> [Constraint] -> [TyVar] -> (ExceptT String FreshM) Solution
solve g w t = do evalStateT (solve' g w) t

solve' :: [Constraint] -> [Constraint] -> SMonad Solution
solve' g w = myTrace ("Solve " ++ show g ++ " ||- " ++ show w) $ do
  let (implic, simple) = partition (is _Constraint_Exists) w
  s@(Solution _ rs theta _) <- simpl g simple
  solveImpl (g ++ rs) (substs theta implic)
  return $ s

solveImpl :: [Constraint] -> [Constraint] -> SMonad ()
solveImpl _ [] = return ()
solveImpl g (Constraint_Exists b : rest) = do
  (vars,(q,c)) <- unbind b
  Solution _ rs _ _ <- lift $ solve (g ++ q) c vars
  if null rs then solveImpl g rest
             else throwError $ "Could not discharge: " ++ show c
solveImpl _ _ = error "This should never happen (solveImpl)"

-- Utils for touchable variables

makeTouchable :: Monad m => TyVar -> StateT [TyVar] m ()
makeTouchable x = modify (insert x)

isTouchable :: Monad m => TyVar -> StateT [TyVar] m Bool
isTouchable x = gets (x `elem`)

-- Phase 2a: simplifier

simpl :: [Constraint] -> [Constraint] -> SMonad Solution
simpl given wanted = do (g,_) <- whileApplicable (\c -> do
                           (interactedGU,apGIU) <- whileApplicable (\cc -> do
                             (canonicalG,apGC)   <- whileApplicable (stepOverList "canong" (canon True) []) cc
                             (interactedGU,apGU) <- stepOverProductList "unifyg" unifyInteract [] canonicalG
                             return (interactedGU, apGC || apGU)) c
                           (interactedG,apGI) <- stepOverProductListDeleteBoth "interg" interact_ [] interactedGU
                           return (interactedG, apGIU || apGI)) given
                        (s,_) <- whileApplicable (\c -> do
                           (interacted,apI) <- whileApplicable (\cc -> do
                             (interactedU,apU) <- whileApplicable (\ccc -> do
                               (canonical2,apC2)  <- whileApplicable (stepOverList "canonw" (canon False) g) ccc
                               (interacted2,apI2) <- stepOverProductList "unifyw" unifyInteract g canonical2
                               return (interacted2, apC2 || apI2)) cc
                             (interacted2,apI2) <- stepOverProductListDeleteBoth "interw" interact_ g interactedU
                             return (interacted2, apU || apI2)) c
                           (simplified,apS) <- stepOverTwoLists "simplw" simplifies g interacted
                           return (simplified, apI || apS)) wanted
                        v <- get
                        myTrace ("touchables: " ++ show v) $ return $ toSolution g s v

canon :: Bool -> [Constraint] -> Constraint -> SMonad SolutionStep
-- Basic unification
canon isGiven _ (Constraint_Unify t1 t2) = case (t1,t2) of
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
    | v `elem` fv t2, isFamilyFree t2
                      -> throwError $ "Infinite type: " ++ show t1 ++ " ~ " ++ show t2
    | isFamilyFree t2 -> do b <- isTouchable v  -- Check touchability when no family
                            if b || isGiven
                               then return NotApplicable
                               else throwError $ "Unifying non-touchable variable: " ++ show v ++ " ~ " ++ show t2
    | otherwise -> case t2 of
                     MonoType_Con c vs -> do (vs2, cons, vars) <- unfamilys vs
                                             when (not isGiven) (mapM_ makeTouchable vars)
                                             return $ Applied $ Constraint_Unify (MonoType_Var v) (MonoType_Con c vs2) : cons
                     s2 :-->: r2       -> do (s2', con1, vars1) <- unfamily s2
                                             (r2', con2, vars2) <- unfamily r2
                                             when (not isGiven) (mapM_ makeTouchable (vars1 ++ vars2))
                                             return $ Applied $ Constraint_Unify (MonoType_Var v) (s2' :-->: r2') : con1 ++ con2
                     _ | t1 > t2   -> return $ Applied [Constraint_Unify t2 t1]  -- Orient
                       | otherwise -> return NotApplicable
  -- Type families
  (MonoType_Fam f ts, _) | any (not . isFamilyFree) ts -> -- ts has type families we can get out
                   do (ts2, cons, vars) <- unfamilys ts
                      when (not isGiven) (mapM_ makeTouchable vars)
                      return $ Applied $ Constraint_Unify (MonoType_Fam f ts2) t2 : cons
  -- Next are Tdec and Faildec
  (s1 :-->: r1, s2 :-->: r2) ->
    return $ Applied [Constraint_Unify s1 s2, Constraint_Unify r1 r2]
  (_ :-->: _, MonoType_Con _ _) -> throwError $ "Different constructor heads: " ++ show t1 ++ " ~ " ++ show t2
  (MonoType_Con _ _, _ :-->: _) -> throwError $ "Different constructor heads: " ++ show t1 ++ " ~ " ++ show t2
  (MonoType_Con c1 a1, MonoType_Con c2 a2)
    | c1 == c2 && length a1 == length a2 -> return $ Applied $ zipWith Constraint_Unify a1 a2
    | c1 /= c2 -> throwError $ "Different constructor heads: " ++ show t1 ++ " ~ " ++ show t2
    | length a1 /= length a2 -> throwError $ "Different number of arguments: " ++ show t1 ++ " ~ " ++ show t2
  -- Orient
  (_, _) | t1 > t2   -> return $ Applied [Constraint_Unify t2 t1]
         | otherwise -> return NotApplicable
-- Convert from monotype > or = into monotype ~
canon _ _ (Constraint_Inst  t (PolyType_Mono [] m)) = return $ Applied [Constraint_Unify t m]
canon _ _ (Constraint_Equal t (PolyType_Mono [] m)) = return $ Applied [Constraint_Unify t m]
-- This is not needed
canon _ _ (Constraint_Inst _ PolyType_Bottom)   = return $ Applied []
-- Constructors and <= and ==
canon _ _ (Constraint_Inst (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Inst (MonoType_Var v) nfP]
canon _ _ (Constraint_Inst x p) = do
  (c,t) <- instantiate p True  -- Perform instantiation
  return $ Applied $ (Constraint_Unify x t) : c
canon _ _ (Constraint_Equal (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Equal (MonoType_Var v) nfP]
-- We need to instantiate, but keep record
-- of those variables which are not touchable
canon _ _ (Constraint_Equal x p) = do
  (c,t) <- instantiate p False  -- Perform instantiation
  return $ Applied $ (Constraint_Unify x t) : c
-- Type classes
canon isGiven _ (Constraint_Class c ts)
  | any (not . isFamilyFree) ts = do (ts2, cons, vars) <- unfamilys ts
                                     when (not isGiven) (mapM_ makeTouchable vars)
                                     return $ Applied $ Constraint_Class c ts2 : cons
  | otherwise = return NotApplicable
-- Rest
canon _ _ (Constraint_Exists _) = return NotApplicable

instantiate :: PolyType -> Bool -> SMonad ([Constraint], MonoType)
instantiate (PolyType_Bind b) tch = do
  (v,i) <- unbind b
  when tch $ makeTouchable v
  (c,t) <- instantiate i tch
  return (c, t)
instantiate (PolyType_Mono cs m) _tch = return (cs,m)
instantiate PolyType_Bottom tch = do
  v <- fresh (string2Name "b")
  when tch $ makeTouchable v
  return ([], var v)

unfamilys :: [MonoType] -> SMonad ([MonoType], [Constraint], [TyVar])
unfamilys ts = do (args,cons,vars) <- unzip3 <$> mapM unfamily ts
                  return (args, concat cons, concat vars)

unfamily :: MonoType -> SMonad (MonoType, [Constraint], [TyVar])
unfamily (MonoType_Fam f vs) = do v <- fresh (string2Name "beta")
                                  return (var v, [Constraint_Unify (var v) (MonoType_Fam f vs)], [v])
unfamily (MonoType_Con c as) = do (args,cons,vars) <- unzip3 <$> mapM unfamily as
                                  return (MonoType_Con c args, concat cons, concat vars)
unfamily (s :-->: t)         = do (s',c1,v1) <- unfamily s
                                  (t',c2,v2) <- unfamily t
                                  return (s' :-->: t', c1 ++ c2, v1 ++ v2)
unfamily t                   = return (t, [], [])

unifyInteract :: [Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
unifyInteract _ _ = unifyInteract'

-- Perform common part of interact_ and simplifies
-- dealing with unifications in canonical form
unifyInteract' :: Constraint -> Constraint -> SMonad SolutionStep
unifyInteract' (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2, isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv s2, isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  (MonoType_Var v1, MonoType_Fam _ args)
    | isFamilyFree s1, all isFamilyFree args, v1 `elem` fv t2 || v1 `elem` fv s2, isFamilyFree s2 ->
        return $ Applied [Constraint_Unify (subst v1 s1 t2) (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  (MonoType_Fam f1 a1, MonoType_Fam f2 a2)
    | f1 == f2, a1 == a2, isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify s1 s2]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
-- Replace something over another constraint
unifyInteract' (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2, isFamilyFree s1
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
unifyInteract' (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` fv t2 || v1 `elem` fv s2, isFamilyFree s1
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
unifyInteract' (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Class c ss2)
  | v1 `elem` fv ss2, all isFamilyFree ss2
  = return $ Applied [Constraint_Class c (subst v1 s1 ss2)]
-- Constructors are not canonical
unifyInteract' (Constraint_Unify _ _) _ = return NotApplicable
unifyInteract' _ (Constraint_Unify _ _) = return NotApplicable -- treated sym
unifyInteract' _ _ = return NotApplicable

-- Makes two constraints interact and removes both of them
interact_ :: [Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
-- First is an unification
interact_ _ _ (Constraint_Unify _ _) _ = return NotApplicable  -- treated in unifyInteract
interact_ _ _ _ (Constraint_Unify _ _) = return NotApplicable
-- == and >=
interact_ given ctx (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = checkEquivalence (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
interact_ given ctx (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = checkSubsumption (given ++ ctx) p2 p1
  | otherwise = return NotApplicable
interact_ _ _ (Constraint_Inst _ _) (Constraint_Equal _ _) = return NotApplicable  -- treated sym
interact_ given ctx (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = do equiv <- areEquivalent (given ++ ctx) p1 p2
                   if equiv then checkEquivalence ctx p1 p2
                   else do (Applied q,p) <- findLub ctx p1 p2
                           return $ Applied (Constraint_Inst t1 p : q)
  | otherwise = return NotApplicable
-- Remove duplicated class constraint
interact_ _ _ (Constraint_Class c1 a1) (Constraint_Class c2 a2)
  | c1 == c2, a1 == a2 = return $ Applied [Constraint_Class c1 a1]
-- Existentials do not interact
interact_ _ _ (Constraint_Exists _) _ = return NotApplicable
interact_ _ _ _ (Constraint_Exists _) = return NotApplicable
-- Rest of things
interact_ _ _ _ _ = return NotApplicable

-- Very similar to interact_, but taking care of symmetric cases
simplifies :: [Constraint] -> [Constraint]
           -> Constraint -> Constraint -> SMonad SolutionStep
-- Cases for unification on the given constraint
simplifies _ _ c1@(Constraint_Unify _ _) c2 = unifyInteract' c1 c2
-- Case for = in the given constraint
simplifies given ctx (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = checkEquivalence (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
simplifies given ctx (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = checkSubsumption (given ++ ctx) p2 p1
  | otherwise = return NotApplicable
simplifies _given _ctx (Constraint_Equal t1 p1) (Constraint_Unify t2 p2)
  | t1 == t2  = return $ Applied [Constraint_Equal p2 p1]
  | otherwise = return NotApplicable
-- Case for > in the given constraint
simplifies given ctx (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = do equiv <- areEquivalent (given ++ ctx) p1 p2
                   if equiv then checkEquivalence ctx p1 p2
                   else do (Applied q,p) <- findLub ctx p1 p2
                           return $ Applied (Constraint_Inst t1 p : q)
  | otherwise = return NotApplicable
simplifies given ctx (Constraint_Inst t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = checkSubsumption (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
simplifies _given _ctx (Constraint_Inst t1 p1) (Constraint_Unify t2 p2)
  | t1 == t2  = return $ Applied [Constraint_Inst p2 p1]
  | otherwise = return NotApplicable
-- Remove duplicated class constraint
simplifies _ _ (Constraint_Class c1 a1) (Constraint_Class c2 a2)
  | c1 == c2, a1 == a2 = return $ Applied []
-- Existentials do not interact
simplifies _ _ (Constraint_Exists _) _ = return NotApplicable
simplifies _ _ _ (Constraint_Exists _) = return NotApplicable
-- Rest of things
simplifies _ _ _ _ = return NotApplicable

findLub :: [Constraint] -> PolyType -> PolyType -> SMonad (SolutionStep, PolyType)
findLub ctx p1 p2 = do
  -- equiv <- areEquivalent ctx p1 p2
  if p1 `aeq` p2 then return (Applied [], p1)
  else do (q1,t1,v1) <- split p1
          (q2,t2,v2) <- split p2
          tau <- fresh $ string2Name "tau"
          let cs = [Constraint_Unify (var tau) t1, Constraint_Unify (var tau) t2]
          tch <- get
          Solution _ r s _ <- lift $ solve ctx (cs ++ q1 ++ q2) (tau : tch ++ v1 ++ v2)
          let s' = substitutionInTermsOf tch s
              r' = map (substs s') r ++ map (\(v,t) -> Constraint_Unify (MonoType_Var v) t) s'
              (floatR, closeR) = partition (\c -> all (`elem` tch) (fv c)) r'
              (closedR, _) = closeExn closeR (substs s' (var tau)) (`elem` tch)
          return (Applied floatR, closedR)

-- Returning NotApplicable means that we could not prove it
-- because some things would float out of the types
checkSubsumption :: [Constraint] -> PolyType -> PolyType -> SMonad SolutionStep
checkSubsumption ctx p1 p2 =
  if p1 `aeq` p2 then return (Applied [])
  else do (q1,t1,v1)  <- split p1
          (q2,t2,_v2) <- split p2
          tch <- get
          Solution _ r s _ <- lift $ solve (ctx ++ q2) (Constraint_Unify t1 t2 : q1) (tch `union` v1)
          let s' = substitutionInTermsOf tch s
              r' = map (substs s') r ++ map (\(v,t) -> Constraint_Unify (MonoType_Var v) t)
                                            (filter (\(v,_) -> v `elem` tch) s')
              allFvs = unionMap fv r'
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
toSolution gs rs vs = let initialSubst = map (\x -> (x, var x)) (fv rs)
                          finalSubst   = runSubst initialSubst
                          doFinalSubst = map (substs finalSubst)
                       in Solution (doFinalSubst gs)
                                   (doFinalSubst (notUnifyConstraints rs))
                                   (runSubst initialSubst) vs
  where runSubst s = let vars = unionMap (\(_,mt) -> fv mt) s
                         unif = concatMap (\v -> filter (isVarUnifyConstraint (== v)) rs) vars
                         sub = map (\(Constraint_Unify (MonoType_Var v) t) -> (v,t)) unif
                      in case s of
                           [] -> s
                           _  -> map (\(v,t) -> (v, substs sub t)) s
        notUnifyConstraints = filter (not . isVarUnifyConstraint (const True))

isVarUnifyConstraint :: (TyVar -> Bool) -> Constraint -> Bool
isVarUnifyConstraint extra (Constraint_Unify (MonoType_Var v) _) = extra v
isVarUnifyConstraint _ _ = False

-- Utils

unionMap :: Ord b => (a -> [b]) -> [a] -> [b]
unionMap f = nub . concat . map f
