{-# LANGUAGE TupleSections #-}
module Cobalt.Script.Solver where

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (union)
import Unbound.LocallyNameless hiding (union)

import Cobalt.Graph as G
import qualified Cobalt.OutsideIn.Solver as OIn
import Cobalt.Script.Script
import Cobalt.Types

type TyError = String
type OInState = ([Constraint],[Constraint],[TyVar])
-- First is a consistent solution
-- Second, the list of errors found
-- Third, the graph of constraints
type ScriptSolution = (OInState, [TyError], Graph)
type FinalSolution  = (OIn.Solution, [TyError], Graph)

solve :: [Axiom] -> [Constraint] -> [TyVar] -> TyScript
      -> FreshM FinalSolution
solve ax g tch w = do
  (((simplG,rs,vars),err,graph), extraExists) <- simpl ax g tch w
  let s@(OIn.Solution _simplG' rs' subst' _vars') = OIn.toSolution simplG rs vars
  solveImpl ax (g ++ rs') (map (substsScript subst') extraExists) (s,err,graph)

solveImpl :: [Axiom] -> [Constraint] -> [TyScript]
          -> FinalSolution -> FreshM FinalSolution
solveImpl _ _ [] sol = return sol
solveImpl ax g (Exists vars q c : rest) (curSol, currErr, currGraph) = do
  (thisSol, thisErr, thisGraph) <- solve ax (g ++ q) vars c
  let newGraph = mappend thisGraph currGraph -- : map (\x -> singletonNode _ x "exists") (q ++ c)
  case (thisSol, thisErr) of
    (OIn.Solution _ [] _ _, []) -> solveImpl ax g rest (curSol, currErr, newGraph)
    _ -> solveImpl ax g rest (curSol, ("Could not discharge: " ++ show c) : (currErr ++ thisErr), newGraph)
solveImpl _ _ _ _ = error "This should never happen"
      
-- Solve one layer of constraints
-- and return the list of extra Exists.
simpl :: [Axiom] -> [Constraint] -> [TyVar] -> TyScript
      -> FreshM (ScriptSolution, [TyScript])
simpl _ g tch Empty =
  return ((emptySolution g tch, [], G.empty), [])
simpl _ g tch me@(Exists _ _ _) =
  return ((emptySolution g tch, [], G.empty), [me])
simpl ax g tch (Singleton c _) =
  (,[]) <$> (solutionUp g tch <$> simpl' ax g [c] tch G.empty)
simpl ax g tch (Merge lst _) = do
  simpls <- mapM (simpl ax g tch) lst
  let (results, exs) = unzip simpls
  (newSol, newErr, newGraph) <- solutionUp g tch <$> simplMany' ax results
  let errs = map (\(_,e,_) -> e) results
  return ((newSol, newErr ++ concat errs, newGraph), concat exs)
simpl ax g tch (Asym s1 s2 info) = simpl ax g tch (Merge [s1,s2] info)

makeSATSolution :: TyError -> [Constraint] -> [TyVar] -> Graph -> ScriptSolution
makeSATSolution err g tch _ = (emptySolution g tch, [err], G.empty)


-- All the rest of this file is just converting back and forth
-- the OutsideIn representation and the Script representation

solutionUp :: [Constraint] -> [TyVar]
           -> (Either String OInState, Graph)
           -> ScriptSolution
solutionUp g tch (Left err, graph) = makeSATSolution err g tch graph
solutionUp _ _   (Right s,  graph) = (s, [], graph)

emptySolution :: [Constraint] -> [TyVar] -> OInState
emptySolution g tch = (g, [], tch)

-- Adapter for the OutsideIn solver
simpl' :: [Axiom] -> [Constraint] -> [Constraint] -> [TyVar] -> Graph
       -> FreshM (Either String OInState, Graph)
simpl' ax given wanted tch graph =
  runWriterT $
    runExceptT $
       flip runReaderT ax $
          flip evalStateT tch $ do
            tell graph
            OIn.simpl given wanted

-- Adapter for multiple OutsideIn solver
simplMany' :: [Axiom] -> [ScriptSolution]
           -> FreshM (Either String OInState, Graph)
simplMany' ax lst =
  let given  = unions $ map (\((g,_,_),_,_) -> g) lst
      wanted = unions $ map (\((_,w,_),_,_) -> w) lst
      tch    = unions $ map (\((_,_,t),_,_) -> t) lst
      graphs = map (\(_,_,g) -> g) lst
   in runWriterT $
        runExceptT $
          flip runReaderT ax $
            flip evalStateT tch $ do
              mapM_ tell graphs
              OIn.simpl given wanted

unions :: Eq a => [[a]] -> [a]
unions = foldr union []
