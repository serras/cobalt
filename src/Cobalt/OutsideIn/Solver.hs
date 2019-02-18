{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
module Cobalt.OutsideIn.Solver (
  SMonad
, Solution(..)
, solve
, entails
, toSolution
, simpl
) where

#if MIN_VERSION_base(4,8,0)
#else
import Control.Applicative ((<$>))
#endif
import Control.Lens.Extras
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (insert, find, delete, partition, nub, (\\))
import Unbound.LocallyNameless
import Debug.Trace

import Cobalt.Core
import Cobalt.OutsideIn.Solver.Step
import Util.ExceptTIsFresh ()

-- import Debug.Trace

-- Phase 2: constraint solving

data Solution = Solution { smallGiven   :: [Constraint]
                         , residual     :: [Constraint]
                         , substitution :: [(TyVar, MonoType)]
                         , touchable    :: [TyVar]
                         } deriving Show

solve :: [Axiom] -> [Constraint] -> [Constraint] -> [TyVar] -> FreshM (Either NamedSolverError Solution, Graph)
solve a g w t = runWriterT (runExceptT (runReaderT (evalStateT (solve' g w) (t, Nothing)) a))

entails :: [Axiom] -> [Constraint] -> [Constraint] -> [TyVar] -> Bool
entails a g w t = case runFreshM $ solve a g w t of
  (Left _, _) -> False
  (Right (Solution _ rs ss _), _) ->
    let tchSubst = filter (\(v,_) -> v `elem` t) (substitutionInTermsOf t ss)
     in null rs && null tchSubst -- No residual constraints

solve' :: [Constraint] -> [Constraint] -> SMonad Solution
solve' g w = myTrace ("Solve " ++ show g ++ " ||- " ++ show w) $ do
  let (implicAndFType, simple) = partition (\x -> is _Constraint_Exists x || is _Constraint_FType x) w
      (implic, ftyped) = partition (is _Constraint_Exists) implicAndFType
  (g',w',s') <- simpl g simple
  -- FType time
  let extraCts = map (\(Constraint_FType v) -> obtainFTypeConstraint (g' ++ w') s' v) ftyped
  (g2,w2,s2) <- simpl g' (w' ++ extraCts)
  -- Implication time
  let s@(Solution sg rs theta _) = toSolution g2 w2 s2
  let theta' = concatMap (\x -> case x of
          (Constraint_Unify (MonoType_Var v) m) -> [(v, m)]
          _ -> []
          ) sg
  solveImpl (g2 ++ rs) (substs (theta ++ theta') implic)
  return s

solveImpl :: [Constraint] -> [Constraint] -> SMonad ()
solveImpl _ [] = return ()
solveImpl g (existsC@(Constraint_Exists b) : rest) = do
  (vars,(q,c)) <- unbind b
  axioms <- ask
  -- Run inner computation
  (result, graph) <- lift $ lift $ lift $ lift $ solve axioms (g ++ q) c vars
  -- Always add the graph here
  tell graph
  case result of
    Left e -> throwError e  -- Rethrow errors
    Right (Solution sg rs _ _ ) -> do
      -- Continue with next implications
      mapM_ (\x -> tell $ singletonEdge existsC x "exists") (q ++ c)
      -- Continue with the rest, if possible
      if null (rs \\ sg) then solveImpl g rest
                 else throwError $ NamedSolverError (Nothing, SolverError_CouldNotDischarge rs)
solveImpl _ _ = error "This should never happen (solveImpl)"

solveApartWithAxioms :: [Constraint] -> [Constraint] -> [TyVar] -> SMonad Solution
solveApartWithAxioms given wanted vars = do
  axioms <- ask
  (result, _) <- lift $ lift $ lift $ lift $ solve axioms given wanted vars
  case result of
    Left  e -> throwError e
    Right s -> return s

solveApartWithoutAxioms :: [Constraint] -> [Constraint] -> [TyVar] -> SMonad Solution
solveApartWithoutAxioms given wanted vars = do
  axioms <- ask
  (result, _) <- lift $ lift $ lift $ lift $ solve (filter isTresspasable axioms) given wanted vars
  case result of
    Left  e -> throwError e
    Right s -> return s

obtainFTypeConstraint :: [Constraint] -> [TyVar] -> MonoType -> Constraint
obtainFTypeConstraint cs tch v = let (poly, _) = closeExn cs v (not . (`elem` tch))
                                  in -- trace (show v ++ " from " ++ show (nf poly) ++ " to " ++ show (ftype poly)) $
                                     Constraint_Inst v (ftype poly)

-- Utils for touchable variables

makeTouchable :: Monad m => TyVar -> StateT ([TyVar], a) m ()
makeTouchable x = modify $ \(v,y) -> (insert x v, y)

isTouchable :: Monad m => TyVar -> StateT ([TyVar], a) m Bool
isTouchable x = gets $ \(v,_) -> x `elem` v

getTchVars :: Monad m => StateT ([TyVar], a) m [TyVar]
getTchVars = gets fst

setLaterMessage :: Monad m => String -> StateT (a, Maybe String) m ()
setLaterMessage m = modify $ \(v, _) -> (v, Just m)

--- Utils for throwing errors

throwNamedError :: (MonadState (a, Maybe String) m, MonadError NamedSolverError m)
                => SolverError -> m b
throwNamedError e = do theLater <- gets snd
                       throwError $ NamedSolverError (theLater, e)

-- Phase 2a: simplifier

simpl :: [Constraint] -> [Constraint] -> SMonad ([Constraint], [Constraint], [TyVar])
simpl given wanted =
  do axioms <- ask
     let injP = isInjectiveFamily axioms
         defP = shouldDeferFamily axioms
     (g,_) <- whileApplicable (\ccTop -> do
                (interactedG2,apIG2) <- whileApplicable (\c -> do
                  (interactedGU,apGIU) <- whileApplicable (\cc -> do
                    (canonicalG,apGC)   <- whileApplicable (stepOverList "canong" (canon True injP) []) cc
                    (interactedGU,apGU) <- stepOverProductList "unifyg" (unifyInteract injP) [] canonicalG
                    return (interactedGU, apGC || apGU)) c
                  (interactedG,apGI) <- stepOverProductListDeleteBoth "interg" interact_ [] interactedGU
                  return (interactedG, apGIU || apGI)) ccTop
                (reactedG, apRG) <- stepOverAxioms "topReact" (\ax _ -> topReact True defP injP ax) axioms [] interactedG2
                return (reactedG, apIG2 || apRG)) given
     (s,_) <- whileApplicable (\ccLater -> do
                (reacted2,apR2) <- whileApplicable (\ccTop -> do
                  (simplified2,apS2) <- whileApplicable (\c -> do
                    (interacted,apI) <- whileApplicable (\cc -> do
                      (interactedU,apU) <- whileApplicable (\ccc -> do
                        (canonical2,apC2)  <- whileApplicable (stepOverList "canonw" (canon False injP) g) ccc
                        (interacted2,apI2) <- stepOverProductList "unifyw" (unifyInteract injP) g canonical2
                        return (interacted2, apC2 || apI2)) cc
                      (interacted2,apI2) <- stepOverProductListDeleteBoth "interw" interact_ g interactedU
                      return (interacted2, apU || apI2)) c
                    (simplified,apS) <- stepOverTwoLists "simplw" (simplifies injP) g interacted
                    return (simplified, apI || apS)) ccTop
                  (reactedW, apRW) <- stepOverAxioms "topReact" (\ax _ -> topReact True defP injP ax) axioms g simplified2
                  return (reactedW, apS2 || apRW)) ccLater
                (laterW, apLW) <- stepOverList "later" (const doLater) g reacted2
                return (laterW, apR2 || apLW)) wanted
     -- Output information
     v <- getTchVars
     myTrace ("touchables: " ++ show v) $ return (g,s,v)

isInjectiveFamily :: [Axiom] -> String -> Bool
isInjectiveFamily [] _ = False
isInjectiveFamily (Axiom_Injective f1 : _) f2
  | f1 == f2  = True
isInjectiveFamily (_ : rest) f2 = isInjectiveFamily rest f2

shouldDeferFamily :: [Axiom] -> String -> Bool
shouldDeferFamily [] _ = False
shouldDeferFamily (Axiom_Defer f1 : _) f2
  | f1 == f2  = True
shouldDeferFamily (_ : rest) f2 = shouldDeferFamily rest f2

canon :: Bool -> (String -> Bool) -> [Constraint] -> Constraint -> SMonad SolutionStep
-- Basic unification
canon isGiven injectiveP rest (Constraint_Unify t1 t2) = case (t1,t2) of
  -- Variables
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2  -> return $ Applied []  -- Refl
    | otherwise -> do touch1 <- isTouchable v1
                      touch2 <- isTouchable v2
                      case (touch1, touch2) of
                       (False, False) -> do -- Note: if we have two variables being unified to equal polytypes
                                            -- it is allowed to unify them, since they represent the same type
                         let findVar vToSearch (Constraint_Inst  (MonoType_Var v) _) | v == vToSearch = True
                             findVar vToSearch (Constraint_Equal (MonoType_Var v) _) | v == vToSearch = True
                             findVar _ _ = False
                             possible1 = filter (findVar v1) rest
                             possible2 = filter (findVar v2) rest
                         let errMsg = SolverError_NonTouchable [v1,v2]
                         ps <- case (possible1, possible2) of
                           ([],_) -> throwNamedError errMsg
                           (_,[]) -> throwNamedError errMsg
                           ([Constraint_Inst  (MonoType_Var _) p1],[Constraint_Inst  (MonoType_Var _) p2]) -> return $ Just (p1,p2)
                           ([Constraint_Equal (MonoType_Var _) p1],[Constraint_Equal (MonoType_Var _) p2]) -> return $ Just (p1,p2)
                           _ -> return Nothing
                         case ps of
                           Nothing -> return NotApplicable
                           Just (p1,p2) -> do equiv <- areEquivalent rest p1 p2
                                              if equiv then return NotApplicable
                                                       else throwNamedError errMsg
                       (True,  False) -> return NotApplicable
                       (False, True)  -> return $ Applied [Constraint_Unify t2 t1]
                       (True,  True)  -> if v1 > v2 then return $ Applied [Constraint_Unify t2 t1]  -- Orient
                                                    else return NotApplicable
    | otherwise -> return NotApplicable
  (MonoType_Var v, _)
    | v `elem` (fv t2 :: [TyVar]), isFamilyFree t2
                      -> throwNamedError (SolverError_Infinite v t2)
    | isFamilyFree t2 -> do b <- isTouchable v  -- Check touchability when no family
                            if b || isGiven
                               then return NotApplicable
                               else return NotApplicable --throwNamedError (SolverError_NonTouchable [v])
    | otherwise -> case t2 of
                     MonoType_Con _    -> return NotApplicable
                     MonoType_App c a  -> do (a2, con1, vars1) <- unfamily a
                                             (c2, con2, vars2) <- unfamily c
                                             unless isGiven (mapM_ makeTouchable (vars1 ++ vars2))
                                             return $ Applied (Constraint_Unify (MonoType_Var v) (MonoType_App c2 a2) : con1 ++ con2)
                     _ | t1 > t2   -> return $ Applied [Constraint_Unify t2 t1]  -- Orient
                       | otherwise -> return NotApplicable
  -- Type families
  (MonoType_Fam f1 ts1, MonoType_Fam f2 ts2) -- Injective type families
    | f1 == f2, injectiveP f1, length ts1 == length ts2 -> return $ Applied (zipWith Constraint_Unify ts1 ts2)
    | f1 == f2, injectiveP f1, length ts1 /= length ts2 -> throwNamedError (SolverError_Unify UnifyErrorReason_NumberOfArgs t1 t2)
  (MonoType_Fam f ts, _) | any (not . isFamilyFree) ts -> -- ts has type families we can get out
                   do (ts2, cons, vars) <- unfamilys ts
                      unless isGiven (mapM_ makeTouchable vars)
                      return $ Applied (Constraint_Unify (MonoType_Fam f ts2) t2 : cons)
  -- Next are Tdec and Faildec
  (s1 :-->: r1, s2 :-->: r2) ->
    return $ Applied [Constraint_Unify s1 s2, Constraint_Unify r1 r2]
  (_ :-->: _, MonoType_Con _) -> throwNamedError (SolverError_Unify UnifyErrorReason_Head t1 t2)
  (MonoType_Con _, _ :-->: _) -> throwNamedError (SolverError_Unify UnifyErrorReason_Head t1 t2)
  (MonoType_Con c1, MonoType_Con c2) 
    | c1 == c2 -> return $ Applied []
    | c1 /= c2 -> throwNamedError  (SolverError_Unify UnifyErrorReason_Head (MonoType_Con c1) (MonoType_Con c2))
  (MonoType_App f1 a1, MonoType_App f2 a2) -> return $ Applied [Constraint_Unify f1 f2, Constraint_Unify a1 a2]
  -- Orient
  (_, _) | t1 > t2   -> return $ Applied [Constraint_Unify t2 t1]
         | otherwise -> return NotApplicable
-- Convert from monotype > or = into monotype ~
canon _ _ _ (Constraint_Inst  t (PolyType_Mono [] m)) = return $ Applied [Constraint_Unify t m]
canon _ _ _ (Constraint_Equal t (PolyType_Mono [] m)) = return $ Applied [Constraint_Unify t m]
-- This is not needed
canon _ _ _ (Constraint_Inst _ PolyType_Bottom)   = return $ Applied []
-- Constructors and <= and ==
canon _ _ _ (Constraint_Inst (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Inst (MonoType_Var v) nfP]
canon _ _ _ (Constraint_Inst x p) = do
  (c,t) <- instantiate p True  -- Perform instantiation
  return $ Applied (Constraint_Unify x t : c)
canon _ _ _ (Constraint_Equal (MonoType_Var v) p)  =
  let nfP = nf p
   in if nfP `aeq` p then return NotApplicable
                     else return $ Applied [Constraint_Equal (MonoType_Var v) nfP]
-- We need to instantiate, but keep record
-- of those variables which are not touchable
canon _ _ _ (Constraint_Equal x p) = do
  (c,t) <- instantiate p False  -- Perform instantiation
  return $ Applied (Constraint_Unify x t : c)
-- Type classes
canon isGiven _ _ (Constraint_Class c ts)
  | any (not . isFamilyFree) ts = do (ts2, cons, vars) <- unfamilys ts
                                     unless isGiven (mapM_ makeTouchable vars)
                                     return $ Applied (Constraint_Class c ts2 : cons)
  | otherwise = return NotApplicable
-- Rest
canon _ _ _ (Constraint_Exists _)   = return NotApplicable
canon _ _ _ (Constraint_FType _)    = return NotApplicable
canon _ _ _ Constraint_Inconsistent = throwNamedError SolverError_Inconsistency
canon True  _ _ (Constraint_Later _ l) = return $ Applied l   -- on given, later is no-op
canon False _ _ (Constraint_Later _ _) = return NotApplicable -- on wanted, later is taken care... later
canon True  _ _ (Constraint_Cond _ _ e) = return $ Applied e   -- on given, return the else part
canon False _ _ (Constraint_Cond _ _ _) = return NotApplicable -- on wanted, cond is taken care... also later

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
unfamily (MonoType_App s t)  = do (s',c1,v1) <- unfamily s
                                  (t',c2,v2) <- unfamily t
                                  return (s' :-->: t', c1 ++ c2, v1 ++ v2)
unfamily t                   = return (t, [], [])

unifyInteract :: (String -> Bool) -> [Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
unifyInteract injectiveP _ _ = unifyInteract' injectiveP

-- Perform common part of interact_ and simplifies
-- dealing with unifications in canonical form
unifyInteract' :: (String -> Bool) -> Constraint -> Constraint -> SMonad SolutionStep
unifyInteract' injectiveP (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2, isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` (fv s2 :: [TyVar]), isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  (MonoType_Var v1, MonoType_Fam _ args)
    | isFamilyFree s1, all isFamilyFree args, v1 `elem` (fv t2 :: [TyVar]) || v1 `elem` (fv s2 :: [TyVar]), isFamilyFree s2 ->
        return $ Applied [Constraint_Unify (subst v1 s1 t2) (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  (MonoType_Fam f1 a1, MonoType_Fam f2 a2)
    | f1 == f2, a1 == a2, isFamilyFree s1, isFamilyFree s2 -> return $ Applied [Constraint_Unify s1 s2]
    | f1 == f2, injectiveP f1, s1 == s2 -> return $ Applied [Constraint_Unify t1 t2]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
-- Replace something over another constraint
unifyInteract' _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Inst t2 s2)
  | v1 `elem` (fv t2 :: [TyVar]) || v1 `elem` (fv s2 :: [TyVar]), isFamilyFree s1
  = return $ Applied [Constraint_Inst (subst v1 s1 t2) (subst v1 s1 s2)]
unifyInteract' _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Equal t2 s2)
  | v1 `elem` (fv t2 :: [TyVar]) || v1 `elem` (fv s2 :: [TyVar]), isFamilyFree s1
  = return $ Applied [Constraint_Equal (subst v1 s1 t2) (subst v1 s1 s2)]
unifyInteract' _ (Constraint_Unify (MonoType_Var v1) s1) (Constraint_Class c ss2)
  | v1 `elem` (fv ss2 :: [TyVar]), all isFamilyFree ss2
  = return $ Applied [Constraint_Class c (subst v1 s1 ss2)]
-- Special case for instantiating a variable appearing in a type family
unifyInteract' _ (Constraint_Unify (MonoType_Fam _ vs) _) (Constraint_Inst v@(MonoType_Var _) p)
  | v `elem` vs
  = do (c,t) <- instantiate p True  -- Perform instantiation
       return $ Applied (Constraint_Unify v t : c)
unifyInteract' _ (Constraint_Class _ vs) (Constraint_Inst v@(MonoType_Var _) p)
  | v `elem` vs
  = do (c,t) <- instantiate p True  -- Perform instantiation
       return $ Applied (Constraint_Unify v t : c)
-- Constructors are not canonical
unifyInteract' _ (Constraint_Unify _ _) _ = return NotApplicable
unifyInteract' _ _ (Constraint_Unify _ _) = return NotApplicable -- treated sym
unifyInteract' _ _ _ = return NotApplicable

-- Makes two constraints interact and removes both of them
interact_ :: [Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep
-- First is an unification
interact_ _ _ (Constraint_Unify _ _) _ = return NotApplicable  -- treated in unifyInteract
interact_ _ _ _ (Constraint_Unify _ _) = return NotApplicable
-- == and >=
interact_ given ctx c1@(Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = addExtraConstraint c1 $ checkEquivalence (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
interact_ given ctx c1@(Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = addExtraConstraint c1 $ checkSubsumption (given ++ ctx) p2 p1
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
simplifies :: (String -> Bool) -> [Constraint] -> [Constraint]
           -> Constraint -> Constraint -> SMonad SolutionStep
-- Cases for unification on the given constraint
simplifies injP _ _ c1@(Constraint_Unify _ _) c2 = unifyInteract' injP c1 c2
-- Case for = in the given constraint
simplifies _ given ctx (Constraint_Equal t1 p1) (Constraint_Equal t2 p2)
  | t1 == t2  = checkEquivalence (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
simplifies _ given ctx (Constraint_Equal t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = checkSubsumption (given ++ ctx) p2 p1
  | otherwise = return NotApplicable
simplifies _ _given _ctx (Constraint_Equal t1 p1) (Constraint_Unify t2 p2)
  | t1 == t2  = return $ Applied [Constraint_Equal p2 p1]
  | otherwise = return NotApplicable
-- Case for > in the given constraint
simplifies _ given ctx (Constraint_Inst t1 p1) (Constraint_Inst t2 p2)
  | t1 == t2  = do equiv <- areEquivalent (given ++ ctx) p1 p2
                   if equiv then checkEquivalence ctx p1 p2
                   else do (Applied q,p) <- findLub ctx p1 p2
                           return $ Applied (Constraint_Inst t1 p : q)
  | otherwise = return NotApplicable
simplifies _ given ctx (Constraint_Inst t1 p1) c2@(Constraint_Equal t2 p2)
  | t1 == t2  = addExtraConstraint c2 $ checkSubsumption (given ++ ctx) p1 p2
  | otherwise = return NotApplicable
simplifies _ _given _ctx (Constraint_Inst t1 p1) (Constraint_Unify t2 p2)
  | t1 == t2  = return $ Applied [Constraint_Inst p2 p1]
  | otherwise = return NotApplicable
-- Remove duplicated class constraint
simplifies _ _ _ (Constraint_Class c1 a1) (Constraint_Class c2 a2)
  | c1 == c2, a1 == a2 = return $ Applied []
-- Existentials do not interact
simplifies _ _ _ (Constraint_Exists _) _ = return NotApplicable
simplifies _ _ _ _ (Constraint_Exists _) = return NotApplicable
-- Rest of things
simplifies _ _ _ _ _ = return NotApplicable

addExtraConstraint :: Constraint -> SMonad SolutionStep -> SMonad SolutionStep
addExtraConstraint c s = do ss <- s
                            case ss of
                              Applied t -> return $ Applied (c:t)
                              other     -> return other

findLub :: [Constraint] -> PolyType -> PolyType -> SMonad (SolutionStep, PolyType)
findLub ctx p1 p2 =
  -- equiv <- areEquivalent ctx p1 p2
  if p1 `aeq` p2 then return (Applied [], p1)
  else do (q1,t1,v1) <- split p1
          (q2,t2,v2) <- split p2
          tau <- fresh $ string2Name "tau"
          let cs = [Constraint_Unify (var tau) t1, Constraint_Unify (var tau) t2]
          tch <- getTchVars
          Solution _ r s _ <- solveApartWithAxioms ctx (cs ++ q1 ++ q2) (tau : tch ++ v1 ++ v2)
          let s' = substitutionInTermsOf tch s
              r' = map (substs s') r ++ map (\(v,t) -> Constraint_Unify (MonoType_Var v) t) s'
              (floatR, closeR) = partition (\x -> all (`elem` tch) (fv x :: [TyVar])) r'
              (closedR, _) = closeExn closeR (substs s' (var tau)) (`elem` tch)
          return (Applied floatR, closedR)

-- Returning NotApplicable means that we could not prove it
-- because some things would float out of the types
checkSubsumption :: [Constraint] -> PolyType -> PolyType -> SMonad SolutionStep
checkSubsumption ctx p1 p2 =
  if p1 `aeq` p2 then return (Applied [])
  else do (q1,t1,v1)  <- split p1
          (q2,t2,_v2) <- split p2
          tch <- getTchVars
          Solution _ r s _ <- solveApartWithAxioms (ctx ++ q2) (Constraint_Unify t1 t2 : q1) (tch `union` v1)
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
    (NotApplicable, _) -> throwNamedError (SolverError_Equiv p1 p2)
    (_, NotApplicable) -> throwNamedError (SolverError_Equiv p1 p2)
    (Applied a1, Applied a2) -> return $ Applied (a1 ++ a2)

topReact :: Bool -> (String -> Bool) -> (String -> Bool) -> Axiom -> Constraint -> SMonad SolutionStep
topReact _ deferP _ (Axiom_Unify _) (Constraint_Unify (MonoType_Fam f ms) (MonoType_Var v))
  | deferP f, v `notElem` (fv ms :: [TyVar]) = return NotApplicable  -- deferred type family
topReact _ _ injP ax@(Axiom_Unify b) (Constraint_Unify fam@(MonoType_Fam f ms) t)
  | all isFamilyFree ms, isFamilyFree t = do
      (aes, (lhs, rhs)) <- unbind b
      case lhs of
        MonoType_Fam lF lMs | f == lF -> do
          Solution _ r s _ <- solveApartWithoutAxioms [] (zipWith Constraint_Unify ms lMs) (aes \\ (fv ax :: [TyVar]))
          case r of
            [] -> return $ Applied [Constraint_Unify (substs s rhs) t]
            _  -> injChance
          `catchError` (\_ -> injChance)
          where injChance = if injP f  -- second chance if f is injective
                            then do
                              Solution _ r2 s2 _ <- solveApartWithoutAxioms [] [Constraint_Unify t rhs] (aes \\ (fv ax :: [TyVar]))
                              case r2 of
                                [] -> return $ Applied [Constraint_Unify (substs s2 lhs) fam]
                                _  -> return NotApplicable
                              `catchError` (\_ -> return NotApplicable)
                            else return NotApplicable
        _ -> return NotApplicable
topReact _ _ _ ax@(Axiom_Class b) (Constraint_Class c ms)
  | all isFamilyFree ms = do
      (aes, (ctx, cls, args)) <- unbind b
      if cls == c
         then do let bes = fv ax :: [TyVar]
                 Solution _ r s _ <- solveApartWithoutAxioms [] (zipWith Constraint_Unify ms args) (aes \\ bes)
                 case r of
                   [] -> return $ Applied (substs s ctx)
                   _  -> return NotApplicable -- Could not match terms
                 `catchError` (\_ -> return NotApplicable)
         else return NotApplicable -- Not same class
topReact _ _ _ _ _ = return NotApplicable

doLater :: Constraint -> SMonad SolutionStep
doLater (Constraint_Later m l)  = setLaterMessage m >> return (Applied l)
doLater (Constraint_Cond _ _ _) = error "Cond should not appear here!"
doLater _                       = return NotApplicable

-- Phase 2b: convert to solution

toSolution :: [Constraint] -> [Constraint] -> [TyVar] -> Solution
toSolution gs rs vs = let initialSubst = map (\x -> (x, var x)) vs
                          finalSubst   = runSubst initialSubst
                          doFinalSubst = map (substs finalSubst)
                       in Solution (nub $ doFinalSubst gs)
                                   (nub $ doFinalSubst (notUnifyConstraints rs))
                                   (nub $ runSubst initialSubst) (nub vs)
  where runSubst s = let vars = unionMap (\(_,mt) -> fv mt) s
                         unif = concatMap (\v -> filter (isVarUnifyConstraint (== v)) rs) vars
                         sub = map (\(Constraint_Unify (MonoType_Var v) t) -> (v,t)) unif
                      in case s of
                           [] -> s
                           _  -> map (\(v,t) -> (v, substs sub t)) s
        notUnifyConstraints = filter (not . isVarUnifyConstraint (`elem` vs))

isVarUnifyConstraint :: (TyVar -> Bool) -> Constraint -> Bool
isVarUnifyConstraint extra (Constraint_Unify (MonoType_Var v) _) = extra v
isVarUnifyConstraint _ _ = False

-- Utils

unionMap :: Ord b => (a -> [b]) -> [a] -> [b]
unionMap f = nub . concatMap f
