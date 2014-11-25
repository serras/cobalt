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
type ScriptSolution = (OInState, [TyError], Graph)

-- First is a consistent solution
-- Second, the list of errors found
-- Third, the graph of constraints
simpl :: [Axiom] -> [Constraint] -> [TyVar] -> TyScript
      -> FreshM ScriptSolution
simpl _ g tch Empty =
  return (emptySolution g tch, [], G.empty)
simpl ax g tch (Singleton c _) =
  solutionUp g tch <$> simpl' ax g [c] tch G.empty
simpl ax g tch (Merge lst _) = do
  results <- mapM (simpl ax g tch) lst
  (newSol, newErr, newGraph) <- solutionUp g tch <$> simplMany' ax results
  let errs = map (\(_,e,_) -> e) results
  return (newSol, newErr ++ concat errs, newGraph)
simpl ax g tch (Asym s1 s2 info) = simpl ax g tch (Merge [s1,s2] info)
simpl _  _ _   (Exists _ _ _)    = error "Not yet implemented"

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
