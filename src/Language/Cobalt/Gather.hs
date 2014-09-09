{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Cobalt.Gather (
  Gathered(..)
, GMonad
, UseHigherRanks(..)
, gather
) where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Data.List (partition, nub, (\\))
import Unbound.LocallyNameless

import Language.Cobalt.Syntax
import Language.Cobalt.Util ()

data Gathered = Gathered { ty      :: MonoType
                         , annTerm :: AnnTerm
                         , givenC  :: [Constraint]
                         , wantedC :: [Constraint]
                         } deriving Show
type GMonad = ReaderT Env (ExceptT String FreshM)

lookupFail :: (Show a, Eq a) => Lens' Env [(a,b)] -> a -> GMonad b
lookupFail p v = do place <- asks (^. p)
                    case lookup v place of
                      Nothing -> throwError $ "Cannot find " ++ show v
                      Just t  -> return t

extendEnv :: TermVar -> PolyType -> GMonad a -> GMonad a
extendEnv v s = local $ \(Env f d x) -> Env ((v,s):f) d x

extendsEnv :: [(TermVar, PolyType)] -> GMonad a -> GMonad a
extendsEnv v = local $ \(Env f d x) -> Env (v ++ f) d x

-- Phase 1: constraint gathering

data UseHigherRanks = UseHigherRanks | NoHigherRanks

gather :: UseHigherRanks -> Term -> GMonad Gathered
gather _ (Term_IntLiteral n) =
  return $ Gathered MonoType_Int (AnnTerm_IntLiteral n MonoType_Int) [] []
gather higher (Term_Var x) =
  do sigma <- lookupFail fnE x
     tau <- var <$> fresh (string2Name "tau")
     return $ Gathered tau (AnnTerm_Var (translate x) tau)
                       [] [Constraint_Inst tau sigma]
gather higher (Term_Abs b) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x (var alpha) $ gather higher e
     let arrow = var alpha :-->: tau
     return $ Gathered arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
gather higher (Term_AbsAnn b mt@(PolyType_Mono [] m)) = -- Case monotype
  do (x,e) <- unbind b
     Gathered tau ann ex c <- extendEnv x mt $ gather higher e
     let arrow = m :-->: tau
     return $ Gathered arrow (AnnTerm_Abs (bind (translate x) ann) arrow) ex c
gather higher (Term_AbsAnn b t) = -- Case polytype
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x t $ gather higher e
     let arrow = var alpha :-->: tau
     return $ Gathered arrow (AnnTerm_AbsAnn (bind (translate x) ann) t arrow)
                       (ex ++ [Constraint_Equal (var alpha) t]) c
gather higher (Term_App e1 e2) =
  do Gathered tau1 ann1 ex1 c1 <- gather higher e1
     Gathered tau2 ann2 ex2 c2 <- gather higher e2
     alpha <- var <$> fresh (string2Name "alpha")
     return $ Gathered alpha (AnnTerm_App ann1 ann2 alpha)
                       (ex1 ++ ex2)
                       (c1 ++ c2 ++ [Constraint_Unify tau1 (tau2 :-->: alpha)])
gather higher (Term_Let b) =
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather higher e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x (PolyType_Mono [] tau1) $ gather higher e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2)
gather higher (Term_LetAnn b PolyType_Bottom) = -- Case bottom
  gather higher (Term_Let b)
gather higher (Term_LetAnn b mt@(PolyType_Mono [] m)) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather higher e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x mt $ gather higher e2
     return $ Gathered tau2 (AnnTerm_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2) (c1 ++ c2 ++ [Constraint_Unify tau1 m])
gather higher (Term_LetAnn b t) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     (q1,t1,_) <- split t
     Gathered tau1 ann1 ex1 c1 <- gather higher e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x t $ gather higher e2
     env <- asks (^. fnE)
     let vars = fv tau1 `union` fv c1 \\ fv env
         extra = Constraint_Exists $ bind vars (q1 ++ ex1, Constraint_Unify t1 tau1 : c1)
     return $ Gathered tau2 (AnnTerm_LetAnn (bind (translate x, embed ann1) ann2) t tau2)
                       ex2 (extra : c2)
gather higher (Term_Match e dname bs) =
  do Gathered tau ann ex c <- gather higher e
     -- Work on alternatives
     tyvars <- mapM fresh =<< lookupFail dataE dname
     resultvar <- fresh $ string2Name "beta"
     alternatives <- mapM (gatherAlternative higher dname tyvars resultvar) bs
     let allExtras = concatMap (givenC  . snd) alternatives
         allCs     = concatMap (wantedC . snd) alternatives
         bindings  = map (\((con,vars),g) -> (con, bind vars (annTerm g))) alternatives
         extra     = Constraint_Unify (MonoType_Con dname (map var tyvars)) tau
     return $ Gathered (var resultvar) (AnnTerm_Match ann dname bindings (var resultvar))
                       (ex ++ allExtras) (extra : c ++ allCs)

gatherAlternative :: UseHigherRanks -> String -> [TyVar] -> TyVar -> (TermVar, Bind [TermVar] Term)
                  -> GMonad ((TermVar, [TermVar]), Gathered)
gatherAlternative higher dname tyvars resultvar (con, b) =
  do -- Get information about constructor
     sigma <- lookupFail fnE con
     (q,arr -> (argsT,resultT),_) <- split sigma
     case resultT of
       MonoType_Con dname2 convars | dname == dname2 -> do
         (args,e) <- unbind b
         let (rest,unifs) = generateExtraUnifications tyvars convars
             argsT' = map (PolyType_Mono [] . substs unifs) argsT
         Gathered taui anni exi ci <- extendsEnv (zip args argsT') $ gather higher e
         let extraVars  = unions (map fv argsT') \\ tyvars
             extraQs    = q ++ rest
             trivial    = all isTrivialConstraint extraQs
             withResult = Constraint_Unify taui (var resultvar) : ci
         if trivial && null extraVars
            then return $ ((con, args), Gathered taui anni exi withResult)
            else do env <- asks (^. fnE)
                    let deltai = (fv taui `union` fv ci) \\ (fv env `union` tyvars)
                        extrai = map (substs unifs) (filter (not . isTrivialConstraint) extraQs) ++ exi
                    return $ ((con, args), Gathered taui anni [] [Constraint_Exists (bind deltai (extrai,withResult))])
       _ -> throwError $ "Match alternative " ++ show con ++ " does not correspond to data " ++ dname

generateExtraUnifications :: [TyVar] -> [MonoType] -> ([Constraint],[(TyVar,MonoType)])
generateExtraUnifications vars ms =
  let initial = zip vars ms
      (unifs, rest) = partition (\(_, m) -> case m of
                                   MonoType_Var v -> length (filter (\(_,m2) -> case m2 of
                                                                        MonoType_Var v2 -> v2 == v
                                                                        _               -> False) initial) == 1
                                   _              -> False) initial
   in (map (\(v,m) -> Constraint_Unify (var v) m) rest,
       map (\(v,MonoType_Var v2) -> (v2, var v)) unifs)

isTrivialConstraint :: Constraint -> Bool
isTrivialConstraint (Constraint_Inst _ PolyType_Bottom) = True
isTrivialConstraint (Constraint_Unify t1 t2) | t1 == t2 = True
isTrivialConstraint (Constraint_Equal t1 (PolyType_Mono [] t2)) | t1 == t2 = True
isTrivialConstraint (Constraint_Inst  t1 (PolyType_Mono [] t2)) | t1 == t2 = True
isTrivialConstraint _ = False

unions :: Eq a => [[a]] -> [a]
unions = nub . concat
