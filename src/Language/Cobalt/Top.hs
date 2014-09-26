{-# LANGUAGE ScopedTypeVariables #-}
module Language.Cobalt.Top (
  gDefn
, gDefns
, tcDefn
, tcDefns
) where

import Control.Lens hiding ((.=))
import Control.Lens.Extras
import Data.Maybe (catMaybes)
import Control.Monad.Except
import Control.Monad.Reader
import Unbound.LocallyNameless

import Language.Cobalt.Gather
import Language.Cobalt.Graph
import Language.Cobalt.Solver
import Language.Cobalt.Syntax
import Language.Cobalt.Types

-- import Debug.Trace

tcNextEnv :: Env -> (TyDefn,a,b) -> Env
tcNextEnv e ((n,_,t),_,_) = e & fnE %~ ((translate n,t):)

doPerDefn' :: (Env -> RawDefn -> ExceptT String FreshM a)
           -> (Env -> a -> Env)
           -> Env -> [(RawDefn,Bool)]
           -> [(Either (RawTermVar,String) a, Bool)]
doPerDefn' f nx e d = runFreshM (doPerDefn f nx e d)

doPerDefn :: (Env -> RawDefn -> ExceptT String FreshM a)
          -> (Env -> a -> Env)
          -> Env -> [(RawDefn,Bool)]
          -> FreshM [(Either (RawTermVar,String) a, Bool)]
doPerDefn _ _ _ [] = return []
doPerDefn f nx e (((n,t,p),b):xs) = do r <- runExceptT (f e (n,t,p))
                                       case r of
                                         Left err -> do rest <- doPerDefn f nx e xs
                                                        return $ (Left (n,err),b) : rest
                                         Right ok -> do rest <- doPerDefn f nx (nx e ok) xs
                                                        return $ (Right ok,b) : rest

-- | Gather constrains from a definition
gDefn :: UseHigherRanks -> Env -> RawDefn -> ExceptT String FreshM (TyTermVar, Gathered, [TyVar])
gDefn h e (n,t,Nothing) = do r@(Gathered _ a _ w) <- runReaderT (gather h t) e
                             return (translate n, r, fv (getAnn a) `union` fv w)
gDefn h e (n,t,Just p)  = do -- Add the annotated type to the environment
                             let e' = e & fnE %~ ((n,p) :)
                             Gathered typ a g w <- runReaderT (gather h t) e'
                             (q1,t1,_) <- split p
                             let extra = Constraint_Unify (getAnn a) t1
                             return (translate n, Gathered typ a (g ++ q1) (extra:w), fv (getAnn a) `union` fv w)

-- | Gather constraints from a list of definitions
gDefns :: UseHigherRanks -> Env -> [(RawDefn,Bool)]
       -> [(Either (RawTermVar,String) (TyTermVar,Gathered,[TyVar]), Bool)]
gDefns higher = doPerDefn' (gDefn higher) const

-- | Typecheck a definition
tcDefn :: UseHigherRanks -> Env -> RawDefn -> ExceptT String FreshM (TyDefn, [Constraint], Graph)
tcDefn h e (n,t,annP) = do
  (n', Gathered _ a g w, tch) <- gDefn h e (n,t,annP)
  (Solution smallG rs sb tch', graph) <- solve (e^.axiomE) g w tch
  let thisAnn = atAnn (substs sb) a
  case annP of
    Nothing -> do let (almostFinalT, restC) = closeExn (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
                      finalT = nf $ almostFinalT
                  -- trace (show (restC,finalT,smallG ++ rs,thisAnn)) $
                  tcCheckErrors restC finalT
                  return ((n',thisAnn,finalT),rs,graph)
    Just p  -> if not (null rs) then throwError $ "Could not deduce: " ++ show rs
                                else return ((n',thisAnn,p),rs,graph)

tcCheckErrors :: [Constraint] -> PolyType -> ExceptT String FreshM ()
tcCheckErrors rs t = do checkRigidity t
                        checkAmbiguity rs
                        checkLeftUnclosed rs

checkRigidity :: PolyType -> ExceptT String FreshM ()
checkRigidity t = do let fvT :: [TyVar] = fv t
                     when (not (null fvT)) $ throwError $ case fvT of
                       [x] -> show x ++ " is a rigid type variable in: " ++ show t
                       _   -> show fvT ++ " are rigid type variables in: " ++ show t

checkAmbiguity :: [Constraint] -> ExceptT String FreshM ()
checkAmbiguity cs = do let vars = catMaybes $ map getVar cs
                           dup  = findDuplicate vars
                       case dup of
                         Nothing -> return ()
                         Just v  -> let cs' = filter (\c -> getVar c == Just v) cs
                                     in throwError $ "Ambiguous variable " ++ show v ++ ": " ++ show cs'

getVar :: Constraint -> Maybe TyVar
getVar (Constraint_Inst  (MonoType_Var v) _) = Just v
getVar (Constraint_Equal (MonoType_Var v) _) = Just v
getVar _ = Nothing

findDuplicate :: Eq a => [a] -> Maybe a
findDuplicate []     = Nothing
findDuplicate (x:xs) = if x `elem` xs then Just x else findDuplicate xs

checkLeftUnclosed :: [Constraint] -> ExceptT String FreshM ()
checkLeftUnclosed cs = let cs' = filter (\x -> not (is _Constraint_Inst x) && not (is _Constraint_Equal x)) cs
                        in case cs' of
                             [] -> return ()
                             _  -> throwError $ "Could not deduce: " ++ show cs'

-- | Typecheck some definitions
tcDefns :: UseHigherRanks -> Env -> [(RawDefn,Bool)]
        -> [(Either (RawTermVar,String) (TyDefn,[Constraint],Graph), Bool)]
tcDefns higher = doPerDefn' (tcDefn higher) tcNextEnv
