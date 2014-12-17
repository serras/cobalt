{-# LANGUAGE TupleSections #-}
module Cobalt.Script.Solver (
  solve
, simpl
, FinalSolution
, makeExplanation
, makeManyExplanation
) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (union, foldl')
import Data.Maybe (maybeToList)
import Text.Parsec.Pos (SourcePos)
import Unbound.LocallyNameless hiding (union)

import Cobalt.Errors
import Cobalt.Graph as G
import qualified Cobalt.OutsideIn.Solver as OIn
import Cobalt.Script.Script
import Cobalt.Types

type OInState = ([Constraint],[Constraint],[TyVar])
-- First is a consistent solution
-- Second, the list of errors found
-- Third, the graph of constraints
type ScriptSolution = (OInState, [ErrorExplanation], Graph)
type FinalSolution  = (OIn.Solution, [ErrorExplanation], Graph)

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
    _ -> let cList = toConstraintList' c
          in solveImpl ax g rest ( curSol
                                 , makeManyExplanation (SolverError_CouldNotDischarge cList) cList Nothing Nothing thisGraph : (currErr ++ thisErr)
                                 , newGraph)
solveImpl _ _ _ _ = error "This should never happen"
      
-- Solve one layer of constraints
-- and return the list of extra Exists.
simpl :: [Axiom] -> [Constraint] -> [TyVar] -> TyScript
      -> FreshM (ScriptSolution, [TyScript])
simpl _ g tch Empty =
  return ((emptySolution g tch, [], G.empty), [])
simpl _ g tch me@(Exists { }) =
  return ((emptySolution g tch, [], G.empty), [me])
simpl ax g tch (Singleton c (pos,cm)) = do
  let comment = map Comment_Pos (maybeToList pos) ++ map Comment_String (maybeToList cm)
  solved <- simplMany' ax [((g,[c],tch), [], G.singletonCommented c comment)]
  case solved of
    (Left err, graph) -> return ((emptySolution g tch, [makeExplanation err pos cm graph], G.empty), [])
    (Right s,  graph) -> return ((s, [], graph), [])
simpl ax g tch (Merge lst (pos,cm)) = do
  simpls <- mapM (simpl ax g tch) lst
  let (results, exs) = unzip simpls
      errs = map (\(_,e,_) -> e) results
  solved <- simplMany' ax results
  case solved of
    (Left err, graph) ->
       -- TODO: should be changed to use an heuristic
       let (fstSol, _, fstGraph) = head results
        in return ((fstSol, makeExplanation err pos cm graph : concat errs, fstGraph), concat exs)
    (Right s, graph) -> return ((s, concat errs, graph), concat exs)
simpl ax g tch (Asym s1 s2 info) = simpl ax g tch (Merge [s2,s1] info)

makeExplanation :: SolverError -> Maybe (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeExplanation err pos msg graph =
  SolverError { theError = err, thePoint = pos, theMessage = msg, theBlame = blameConstraints graph Constraint_Inconsistent }

makeManyExplanation :: SolverError -> [Constraint] -> Maybe (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeManyExplanation err cs pos msg graph =
  let blamed = foldl' union [] $ map (blameConstraints graph) cs
   in SolverError { theError = err, thePoint = pos, theMessage = msg, theBlame = blamed }

-- All the rest of this file is just converting back and forth
-- the OutsideIn representation and the Script representation
emptySolution :: [Constraint] -> [TyVar] -> OInState
emptySolution g tch = (g, [], tch)

-- Adapter for multiple OutsideIn solver
simplMany' :: [Axiom] -> [ScriptSolution]
           -> FreshM (Either SolverError OInState, Graph)
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
