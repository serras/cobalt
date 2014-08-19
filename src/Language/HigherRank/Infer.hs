{-# LANGUAGE ViewPatterns #-}
module Language.HigherRank.Infer (
  infer
, testString
) where

import Control.Applicative
import Control.Monad.Reader
import Text.Groom
import Text.Parsec
import Unbound.LocallyNameless

import Language.HigherRank.Parser
import Language.HigherRank.Syntax

type Env = [(TermVar, PolyType)]
type Result = (MonoType, AnnTerm, [Constraint], [BasicConstraint])
type TcMonad = FreshMT (ReaderT Env (Either String))

lookupEnv :: TermVar -> TcMonad PolyType
lookupEnv v = do optT <- asks (lookup v)
                 case optT of
                   Nothing -> fail $ "Cannot find " ++ show v
                   Just t  -> return t

extendEnv :: TermVar -> PolyType -> TcMonad a -> TcMonad a
extendEnv v s = local ((v,s) :)

infer :: Term -> TcMonad Result
infer (Term_IntLiteral n) =
  return (MonoType_Int, AnnTerm_IntLiteral n MonoType_Int,
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
             c, ex ++ [BasicConstraint_Inst alpha PolyType_Bottom])
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

type Solution = ([Constraint], [(TyVar, MonoType)])
type SMonad = FreshMT (Either String)

solve :: [BasicConstraint] -> [Constraint] -> SMonad Solution
solve given wanted = do (s,_) <- whileApplicable (\c -> do
                           (canonical,apC)  <- whileApplicable (stepOverList canon) c
                           (interacted,apI) <- whileApplicable (stepOverProductList interact_) canonical
                           return (interacted, apC || apI)) wanted
                        return (s, [])

data StepResult = NotApplicable | Applied [Constraint]

whileApplicable :: ([Constraint] -> SMonad ([Constraint], Bool)) -> [Constraint] -> SMonad ([Constraint], Bool)
whileApplicable f c = innerApplicable' c False
  where innerApplicable' cs atAll = do
          r <- f cs
          case r of
            (_,   False) -> return (cs, atAll)
            (newC,True)  -> innerApplicable' newC True

stepOverList :: (Constraint -> SMonad StepResult) -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverList f lst = stepOverList' lst [] False False
  where -- Finish cases: last two args are changed-in-this-loop, and changed-at-all
        stepOverList' [] accum True  _     = stepOverList' accum [] False True
        stepOverList' [] accum False atAll = return (accum, atAll)
        -- Rest of cases
        stepOverList' (x:xs) accum thisLoop atAll = do
          r <- f x
          case r of
            NotApplicable -> stepOverList' xs (x:accum) thisLoop atAll
            Applied newX  -> stepOverList' xs (newX ++ accum) True True

stepOverProductList :: (Constraint -> Constraint -> SMonad StepResult) -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverProductList f lst = stepOverProductList' lst [] False
  where stepOverProductList' [] accum atAll = return (accum, atAll)
        stepOverProductList' (x:xs) accum atAll =
          do r <- stepOverList (f x) (xs ++ accum)
             case r of
               (_,     False) -> stepOverProductList' xs (x:accum) atAll
               (newLst,True)  -> stepOverProductList' (x:newLst) [] True

canon :: Constraint -> SMonad StepResult
canon (Constraint_Unify t1 t2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2) | v1 == v2  -> return $ Applied []
                                     | v1 > v2   -> return $ Applied [Constraint_Unify t2 t1]
                                     | otherwise -> return NotApplicable
  (MonoType_Var _, _) -> return NotApplicable
  (t, v@(MonoType_Var _)) -> return $ Applied [Constraint_Unify v t]  -- Orient
  (MonoType_Int, MonoType_Int) -> return $ Applied []
  (MonoType_List l1, MonoType_List l2) ->
    return $ Applied [Constraint_Unify l1 l2]
  (MonoType_Tuple s1 r1, MonoType_Tuple s2 r2) ->
    return $ Applied [Constraint_Unify s1 s2, Constraint_Unify r1 r2]
  (MonoType_Arrow s1 r1, MonoType_Arrow s2 r2) ->
    return $ Applied [Constraint_Unify s1 s2, Constraint_Unify r1 r2]
  _ -> fail "Different constructor heads"  -- Different constructors
canon (Constraint_Inst _ PolyType_Bottom) = return $ Applied []
canon _ = return NotApplicable

-- Change w.r.t. OutsideIn -> return only second constraint
interact_ :: Constraint -> Constraint -> SMonad StepResult
interact_ (Constraint_Unify t1 s1) (Constraint_Unify t2 s2) = case (t1,t2) of
  (MonoType_Var v1, MonoType_Var v2)
    | v1 == v2 -> return $ Applied [Constraint_Unify s1 s2]
    | v1 `elem` fv v2 -> return $ Applied [Constraint_Unify t2 (subst v1 s1 s2)]
    | otherwise -> return NotApplicable
  _ -> return NotApplicable
interact_ _ _ = return NotApplicable

newtype TestResult = TestResult (AnnTerm, [BasicConstraint], [Constraint], Solution)
instance Show TestResult where
  show (TestResult (ann, given, wanted, end)) =
    "Term: " ++ groom ann ++ "\n" ++
    "Give: " ++ show given ++ "\n" ++
    "Want: " ++ show wanted ++ "\n" ++
    "Soln: " ++ show end

testString :: String -> Either String TestResult
testString s =
  case parse parseTerm "parse" s of
    Left  e -> Left (show e)
    Right t -> case runReaderT (runFreshMT $ infer t) [] of
      Left  e         -> Left e
      Right (_,a,c,q) -> case runFreshMT $ solve q c of
        Left  e  -> Left e
        Right sl -> Right $ TestResult (a,q,c,sl)
