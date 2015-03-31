{-# LANGUAGE TupleSections #-}
module Cobalt.U.Solver (
  solve
, simpl
, FinalSolution
, makeExplanation
, makeManyExplanation
, OIn.Solution(..)
) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (union, foldl')
import Text.Parsec.Pos (SourcePos)
import Unbound.LocallyNameless hiding (union)

import Cobalt.Core
import qualified Cobalt.OutsideIn as OIn
import Cobalt.U.Script

type OInState = ([Constraint],[Constraint],[TyVar])
-- First is a consistent solution
-- Second, the list of errors found
-- Third, the graph of constraints
type ScriptSolution = (OInState, [ErrorExplanation], Graph)
type FinalSolution  = (OIn.Solution, [ErrorExplanation], Graph)

solve :: [Axiom] -> [Constraint] -> [TyVar] -> TyScriptInfo -> TyScript
      -> FreshM FinalSolution
solve ax g tch info w = do
  (((simplG,rs,vars),err,graph), extraExists) <- simpl ax g tch info w
  let s@(OIn.Solution _simplG' rs' subst' _vars') = OIn.toSolution simplG rs vars
  solveImpl ax (g ++ rs') (map (\(i_, s_) -> (i_, substsScript subst' s_)) extraExists) (s,err,graph)

solveImpl :: [Axiom] -> [Constraint] -> [(TyScriptInfo, TyScript)]
          -> FinalSolution -> FreshM FinalSolution
solveImpl _ _ [] sol = return sol
solveImpl ax g ((info, Exists vars q c) : rest) (curSol, currErr, currGraph) = do
  (thisSol, thisErr, thisGraph) <- solve ax (g ++ q) vars info c
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
simpl :: [Axiom] -> [Constraint] -> [TyVar] -> TyScriptInfo -> TyScript
      -> FreshM (ScriptSolution, [(TyScriptInfo, TyScript)])
simpl _ g tch _ Empty =
  return ((emptySolution g tch, [], emptyGraph), [])
simpl _ g tch info me@(Exists { }) =
  return ((emptySolution g tch, [], emptyGraph), [(info, me)])
simpl ax g tch _ (Label i c) = simpl ax g tch i c
simpl ax g tch (pos,cm) (Singleton c) = do
  -- let comment = map Comment_Pos (maybeToList pos) ++ map Comment_String (maybeToList cm)
  solved <- simplMany' ax [((g,[c],tch), [], singletonCommented c [])]
  case solved of
    (Left err, graph) -> return ((emptySolution g tch, [makeExplanation err pos cm graph], emptyGraph), [])
    (Right s,  graph) -> return ((s, [], graph), [])
simpl ax g tch (pos,cm) (Join lst) = do
  simpls <- mapM (simpl ax g tch (pos,cm)) lst
  let (results, exs) = unzip simpls
      errs = map (\(_,e,_) -> e) results
  solved <- simplMany' ax results
  case solved of
    (Left err, graph) ->
       -- TODO: should be changed to use an heuristic
       let (fstSol, _, fstGraph) = head results
        in return ((fstSol, makeExplanation err pos cm graph : concat errs, fstGraph), concat exs)
    (Right s, graph) -> return ((s, concat errs, graph), concat exs)
simpl ax g tch (pos,cm) (AsymJoin s1 s2) = simpl ax g tch (pos,cm) (Join [s1,s2])
-- simpl ax g tch (pos,cm) (Sequence s1 s2)

makeExplanation :: SolverError -> Maybe (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeExplanation err pos msg graph =
  SolverError { theError = err
              , thePoint = pos
              , theMessage = msg
              , theBlame = blameConstraints graph Constraint_Inconsistent
              , theDominators = getDominators graph Constraint_Inconsistent }

makeManyExplanation :: SolverError -> [Constraint] -> Maybe (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeManyExplanation err cs pos msg graph =
  let blamed = foldl' union [] $ map (blameConstraints graph) cs
   in SolverError { theError = err, thePoint = pos, theMessage = msg, theBlame = blamed, theDominators = [] }

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
