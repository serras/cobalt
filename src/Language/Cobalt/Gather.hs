{-# LANGUAGE ViewPatterns #-}
module Language.Cobalt.Gather (
  Gathered(..)
, GMonad
, gather
) where

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad.Error
import Control.Monad.Reader
import Data.List (partition, nub, (\\))
import Unbound.LocallyNameless

import Language.Cobalt.Syntax

data Gathered = Gathered { ty      :: MonoType
                         , annTerm :: AnnTerm
                         , givenC  :: [Constraint]
                         , wantedC :: [Constraint]
                         } deriving Show
type GMonad = ReaderT (Env,DataEnv) (ErrorT String FreshM)

lookupEnv :: TermVar -> GMonad PolyType
lookupEnv v = do optT <- asks (\(env,_dataenv) -> lookup v env)
                 case optT of
                   Nothing -> throwError $ "Cannot find " ++ show v
                   Just t  -> return t

lookupDataEnv :: String -> GMonad [TyVar]
lookupDataEnv n = do optT <- asks (\(_env,dataenv) -> lookup n dataenv)
                     case optT of
                       Nothing -> throwError $ "Cannot find data " ++ show n
                       Just t  -> return t

extendEnv :: TermVar -> PolyType -> GMonad a -> GMonad a
extendEnv v s = local $ ((v,s) :) *** id

extendsEnv :: [(TermVar, PolyType)] -> GMonad a -> GMonad a
extendsEnv v = local $ (v ++) *** id

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
gather (Term_LetAnn b PolyType_Bottom) = -- Case bottom
  gather (Term_Let b)
gather (Term_LetAnn b mt@(PolyType_Mono m)) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x mt $ gather e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
gather (Term_LetAnn b t) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     (q1,t1,_) <- splitType t
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x t $ gather e2
     env <- ask
     let vars = fv tau1 `union` fv c1 \\ fv env
         extra = Constraint_Exists $ bind vars (q1 ++ ex1, Constraint_Unify t1 tau1 : c1)
     return $ Gathered tau2 (AnnTerm_LetAnn (bind (translate x, embed ann1) ann2) t tau2)
                       ex2 (extra : c2)
gather (Term_Match e dname bs) =
  do Gathered tau ann ex c <- gather e
     -- Work on alternatives
     tyvars <- mapM fresh =<< lookupDataEnv dname
     resultvar <- fresh $ string2Name "beta"
     alternatives <- mapM (gatherAlternative dname tyvars resultvar) bs
     let allExtras = concatMap (givenC  . snd) alternatives
         allCs     = concatMap (wantedC . snd) alternatives
         bindings  = map (\((con,vars),g) -> (con, bind vars (annTerm g))) alternatives
         extra     = Constraint_Unify (MonoType_Con dname (map mVar tyvars)) tau
     return $ Gathered (mVar resultvar) (AnnTerm_Match ann dname bindings (mVar resultvar))
                       (ex ++ allExtras) (extra : c ++ allCs)

gatherAlternative :: String -> [TyVar] -> TyVar -> (TermVar, Bind [TermVar] Term)
                  -> GMonad ((TermVar, [TermVar]), Gathered)
gatherAlternative dname tyvars resultvar (con, b) =
  do -- Get information about constructor
     sigma    <- lookupEnv con
     (q,v,_)  <- splitType sigma
     let (argsT,resultT) = splitArrow v
     case resultT of
       MonoType_Con dname2 convars | dname == dname2 -> do
         (args,e) <- unbind b
         let (rest,unifs) = generateExtraUnifications tyvars convars
             argsT' = map (PolyType_Mono . substs unifs) argsT
         Gathered taui anni exi ci <- extendsEnv (zip args argsT') $ gather e
         let extraVars  = unions (map fv argsT') \\ tyvars
             extraQs    = q ++ rest
             trivial    = all isTrivialConstraint extraQs
             withResult = Constraint_Unify taui (mVar resultvar) : ci
         if trivial && null extraVars
            then return $ ((con, args), Gathered taui anni exi withResult)
            else do env <- ask
                    let deltai = (fv taui `union` fv ci) \\ (fv env `union` tyvars)
                        extrai = map (substs unifs) (filter (not . isTrivialConstraint) extraQs) ++ exi
                    return $ ((con, args), Gathered taui anni [] [Constraint_Exists (bind deltai (extrai,withResult))])
       _ -> throwError $ "Match alternative " ++ show con ++ " does not correspond to data " ++ dname

splitArrow :: MonoType -> ([MonoType],MonoType)
splitArrow (MonoType_Arrow s r) = let (s',r') = splitArrow r
                                   in (s:s', r')
splitArrow m = ([],m)

generateExtraUnifications :: [TyVar] -> [MonoType] -> ([Constraint],[(TyVar,MonoType)])
generateExtraUnifications vars ms =
  let initial = zip vars ms
      (unifs, rest) = partition (\(_, m) -> case m of
                                   MonoType_Var v -> length (filter (\(_,m2) -> case m2 of
                                                                        MonoType_Var v2 -> v2 == v
                                                                        _               -> False) initial) == 1
                                   _              -> False) initial
   in (map (\(v,m) -> Constraint_Unify (mVar v) m) rest,
       map (\(v,MonoType_Var v2) -> (v2, mVar v)) unifs)

isTrivialConstraint :: Constraint -> Bool
isTrivialConstraint (Constraint_Inst _ PolyType_Bottom) = True
isTrivialConstraint (Constraint_Unify t1 t2) | t1 == t2 = True
isTrivialConstraint (Constraint_Equal t1 (PolyType_Mono t2)) | t1 == t2 = True
isTrivialConstraint (Constraint_Inst  t1 (PolyType_Mono t2)) | t1 == t2 = True
isTrivialConstraint _ = False

unions :: Eq a => [[a]] -> [a]
unions = nub . concat
