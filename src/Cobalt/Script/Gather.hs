{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternSynonyms #-}
module Cobalt.Script.Gather (
  Gathered(..)
, GMonad
, gather
) where

import Control.Applicative
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Data.List (partition, nub, (\\))
import Unbound.LocallyNameless

import Cobalt.Language.Syntax
import Cobalt.Script.Script
import Cobalt.Types
import Cobalt.Util ()

data Gathered = Gathered { ty      :: MonoType
                         , annTerm :: TyTerm
                         , givenC  :: [Constraint]
                         , wantedC :: TyScript
                         } deriving Show
type GMonad = ReaderT Env (ExceptT String FreshM)

lookupFail :: (Show a, Eq a) => Lens' Env [(a,b)] -> a -> GMonad b
lookupFail p v = do place <- asks (^. p)
                    case lookup v place of
                      Nothing -> throwError $ "Cannot find " ++ show v
                      Just t  -> return t

extendEnv :: RawTermVar -> PolyType -> GMonad a -> GMonad a
extendEnv v s = local $ \(Env f d x) -> Env ((v,s):f) d x

extendsEnv :: [(RawTermVar, PolyType)] -> GMonad a -> GMonad a
extendsEnv v = local $ \(Env f d x) -> Env (v ++ f) d x

-- Phase 1: constraint gathering

gather :: -> RawTerm -> GMonad Gathered
gather (Term_IntLiteral n _) =
  return $ Gathered MonoType_Int (Term_IntLiteral n MonoType_Int) [] Empty
gather (Term_Var x _) =
  do sigma <- lookupFail fnE x
     tau <- var <$> fresh (string2Name "tau")
     return $ Gathered tau (Term_Var (translate x) tau) []
                       (Singleton (Constraint_Inst tau sigma) "Not an instance")
gather (Term_Abs b _) =
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x (var alpha) $ gather e
     let arrow = var alpha :-->: tau
     return $ Gathered arrow (Term_Abs (bind (translate x) ann) arrow) ex c
gather (Term_AbsAnn b mt@(PolyType_Mono [] m) _) = -- Case monotype
  do (x,e) <- unbind b
     Gathered tau ann ex c <- extendEnv x mt $ gather e
     let arrow = m :-->: tau
     return $ Gathered arrow (Term_Abs (bind (translate x) ann) arrow) ex c
gather (Term_AbsAnn b t _) = -- Case polytype
  do (x,e) <- unbind b
     alpha <- fresh (string2Name "alpha")
     Gathered tau ann ex c <- extendEnv x t $ gather e
     let arrow = var alpha :-->: tau
     return $ Gathered arrow (Term_AbsAnn (bind (translate x) ann) t arrow)
                       (ex ++ [Constraint_Equal (var alpha) t]) c
gather higher (Term_App e1 e2 _) =
  do Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- gather e2
     alpha <- var <$> fresh (string2Name "alpha")
     return $ Gathered alpha (Term_App ann1 ann2 alpha)
                       (ex1 ++ ex2)
                       (Asym (Singleton (Constraint_Unify tau1 (tau2 :-->: alpha)))
                             (Merge [c1,c2] "Mismatch in types")
                             "The first argument is not an application")
gather higher (Term_Let b _) =
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x (PolyType_Mono [] tau1) $ gather e2
     return $ Gathered tau2 (Term_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2)
                       (Merge [c1,c2] "Mismatch in types")
gather (Term_LetAnn b PolyType_Bottom a) = -- Case bottom
  gather (Term_Let b a)
gather (Term_LetAnn b mt@(PolyType_Mono [] m) _) = -- Case monotype
  do ((x, unembed -> e1),e2) <- unbind b
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x mt $ gather e2
     return $ Gathered tau2 (Term_Let (bind (translate x, embed ann1) ann2) tau2)
                       (ex1 ++ ex2)
                       (Asym (Singleton (Constraint_Unify tau1 m) "Body is not of the specified type")
                             (Merge [c1,c2] "Mismatch in types")
                             "")
gather higher (Term_LetAnn b t _) = -- Case polytype
  do ((x, unembed -> e1),e2) <- unbind b
     (q1,t1,_) <- split t
     Gathered tau1 ann1 ex1 c1 <- gather e1
     Gathered tau2 ann2 ex2 c2 <- extendEnv x t $ gather e2
     env <- asks (^. fnE)
     let vars = fv tau1 `union` fv c1 \\ fv env
         extra = Constraint_Exists $ bind vars (q1 ++ ex1, Constraint_Unify t1 tau1 : c1)
     return $ Gathered tau2 (Term_LetAnn (bind (translate x, embed ann1) ann2) t tau2) ex2
              (Asym (Exists vars (q1 ++ ex1)
                            (Asym (Singleton (Constraint_Unify t1 tau1) "")
                                   c1 "Mismatch in body"))
                    c2 "")
gather (Term_Match e dname bs _) =
  do Gathered tau ann ex c <- gather higher e
     -- Work on alternatives
     tyvars <- mapM fresh =<< lookupFail dataE dname
     resultvar <- fresh $ string2Name "beta"
     alternatives <- mapM (gatherAlternative dname tyvars resultvar) bs
     let allExtras = concatMap (givenC  . snd) alternatives
         allCs     = concatMap (wantedC . snd) alternatives
         bindings  = map (\((con,vars),g) -> (con, bind vars (annTerm g))) alternatives
         extra     = Constraint_Unify (MonoType_Con dname (map var tyvars)) tau
     return $ Gathered (var resultvar) (Term_Match ann dname bindings (var resultvar))
                       (ex ++ allExtras) (extra : c ++ allCs)

gatherAlternative :: String -> [TyVar] -> TyVar -> (RawTermVar, Bind [RawTermVar] RawTerm)
                  -> GMonad ((TyTermVar, [TyTermVar]), Gathered)
gatherAlternative dname tyvars resultvar (con, b) =
  do -- Get information about constructor
     sigma <- lookupFail fnE con
     (q,arr -> (argsT,resultT),_) <- split sigma
     case resultT of
       MonoType_Con dname2 convars | dname == dname2 -> do
         (args,e) <- unbind b
         let (rest,unifs) = generateExtraUnifications tyvars convars
             argsT' = map (PolyType_Mono [] . substs unifs) argsT
         Gathered taui anni exi ci <- extendsEnv (zip args argsT') $ gather e
         let extraVars  = unions (map fv argsT') \\ tyvars
             extraQs    = q ++ rest
             trivial    = all isTrivialConstraint extraQs
             withResult = Constraint_Unify taui (var resultvar) : ci
         if trivial && null extraVars
            then return $ ( (translate con, map translate args)
                          , Gathered taui anni exi withResult )
            else do env <- asks (^. fnE)
                    let deltai = (fv taui `union` fv ci) \\ (fv env `union` tyvars)
                        extrai = map (substs unifs) (filter (not . isTrivialConstraint) extraQs) ++ exi
                    return $ ( (translate con, map translate args)
                             , Gathered taui anni [] [Constraint_Exists (bind deltai (extrai,withResult))] )
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
