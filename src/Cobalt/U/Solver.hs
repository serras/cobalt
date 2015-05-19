{-# LANGUAGE TupleSections #-}
module Cobalt.U.Solver (
  solve
, simpl
, FinalSolution
, makeExplanation
, makeManyExplanation
, OIn.Solution(..)
) where

import Control.Applicative ((<|>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (union, foldl')
import Data.Maybe (maybeToList)
import Text.Parsec.Pos (SourcePos)
import Unbound.LocallyNameless hiding (union)

import Cobalt.Core
import qualified Cobalt.OutsideIn as OIn
import Cobalt.U.Script

-- import Debug.Trace

type OInState = ([Constraint],[Constraint],[TyVar])
-- First is a consistent solution
-- Second, the list of errors found
-- Third, the graph of constraints
type ScriptSolution = (OInState, [ErrorExplanation], Graph)
type FinalSolution  = (OIn.Solution, [ErrorExplanation], Graph)

solve :: [Axiom] -> [Constraint] -> [TyVar]
      -> TyScript -> FreshM FinalSolution
solve ax c v s = do (sol, errs, g) <- solve_ ax c v Nothing s
                    return (sol, reverse errs, g)

solve_ :: [Axiom] -> [Constraint] -> [TyVar]
       -> Maybe TyScriptInfo -> TyScript
       -> FreshM FinalSolution
solve_ ax g tch info w = do
  (((simplG,rs,vars),err,graph), extraExists) <- simpl ax g tch info Nothing w
  let s@(OIn.Solution _simplG' rs' subst' _vars') = OIn.toSolution simplG rs vars
  solveImpl ax (g ++ rs') (map (\(i_, s_) -> (i_, substsScript subst' s_)) extraExists) (s,err,graph)

solveImpl :: [Axiom] -> [Constraint] -> [(Maybe TyScriptInfo, TyScript)]
          -> FinalSolution -> FreshM FinalSolution
solveImpl _ _ [] sol = return sol
solveImpl ax g ((info, Exists vars q c p) : rest) (curSol, currErr, currGraph) = do
  (thisSol, thisErr, thisGraph) <- solve_ ax (g ++ q) vars info c
  let newGraph = mappend thisGraph currGraph -- : map (\x -> singletonNode _ x "exists") (q ++ c)
  case (thisSol, thisErr) of
    (OIn.Solution _ [] _ _, []) -> solveImpl ax g rest (curSol, currErr, newGraph)
    _ -> let cList = toConstraintList' c
          in solveImpl ax g rest ( curSol
                                 , makeManyExplanation (SolverError_CouldNotDischarge cList)
                                                       cList p Nothing thisGraph : (currErr ++ thisErr)
                                 , newGraph)
solveImpl _ _ _ _ = error "This should never happen"

-- Solve one layer of constraints
-- and return the list of extra Exists.
simpl :: [Axiom] -> [Constraint] -> [TyVar]
      -> Maybe TyScriptInfo    -- label information
      -> Maybe ScriptSolution  -- previous solution (for sequencing)
      -> TyScript
      -> FreshM (ScriptSolution, [(Maybe TyScriptInfo, TyScript)])
simpl _ g tch _ _ Empty =
  return ((emptySolution g tch, [], emptyGraph), [])
simpl _ g tch info _ me@(Exists { }) =
  return ((emptySolution g tch, [], emptyGraph), [(info, me)])
simpl ax g tch _ prev (Label i c) = simpl ax g tch (Just i) prev c
simpl ax g tch cm prev (Singleton c pos expl) = do
  let comment = (Comment_Pos pos) : map Comment_String (maybeToList expl)
      prev' = maybeToList prev
  solved <- simplMany' ax (((g,[c],tch), [], singletonCommented c comment) : prev')
  case solved of
    (Left err, graph) -> return ( ( emptySolution g tch
                                  , [makeExplanation err pos cm graph]
                                  , emptyGraph )
                                , [] )
    (Right s,  graph) -> return ((s, [], graph), [])
simpl ax g tch cm prev (Join lst pos) = do
  simpls <- mapM (simpl ax g tch cm prev) lst
  let (results, exs) = unzip simpls
      errs = map (\(_,e,_) -> e) results
  solved <- simplMany' ax results
  case solved of
    (Left err, graph) ->
       -- TODO: should be changed to use an heuristic
       let (fstSol, _, fstGraph) = head results
        in return ( ( fstSol
                    , makeExplanation err pos cm graph : concat errs
                    , fstGraph )
                  , concat exs )
    (Right s, graph) -> return ((s, concat errs, graph), concat exs)
simpl ax g tch cm prev (AsymJoin s1 s2 pos) =
  simpl ax g tch cm prev (Join [s1,s2] pos)
simpl ax g tch cm prev (Sequence s1 s2 _pos) = do
  (result1@(_sol1,errs1,_), ex1) <- simpl ax g tch cm prev s1
  ((sol2,errs2,g2), ex2) <- {- trace ("using: " ++ show sol1) -} simpl ax g tch cm (Just result1) s2
  return ((sol2,errs2 ++ errs1,g2), ex1 ++ ex2)

makeExplanation :: NamedSolverError -> (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeExplanation (NamedSolverError (laterMsg, err)) pos msg graph =
  SolverError { theError = err
              , thePoint = Just pos
              , theMessage = msg <|> laterMsg
              , theBlame = blameConstraints graph Constraint_Inconsistent
              , theDominators = getDominators graph Constraint_Inconsistent }

makeManyExplanation :: SolverError -> [Constraint] -> (SourcePos, SourcePos) -> Maybe String -> Graph -> ErrorExplanation
makeManyExplanation err cs pos msg graph =
  let blamed = foldl' union [] $ map (blameConstraints graph) cs
   in SolverError { theError = err, thePoint = Just pos, theMessage = msg, theBlame = blamed, theDominators = [] }

-- All the rest of this file is just converting back and forth
-- the OutsideIn representation and the Script representation
emptySolution :: [Constraint] -> [TyVar] -> OInState
emptySolution g tch = (g, [], tch)

-- Adapter for multiple OutsideIn solver
simplMany' :: [Axiom] -> [ScriptSolution]
           -> FreshM (Either NamedSolverError OInState, Graph)
simplMany' ax lst =
  let given  = unions $ map (\((g,_,_),_,_) -> g) lst
      wanted = unions $ map (\((_,w,_),_,_) -> w) lst
      tch    = unions $ map (\((_,_,t),_,_) -> t) lst
      graphs = map (\(_,_,g) -> g) lst
   in runWriterT $
        runExceptT $
          flip runReaderT ax $
            flip evalStateT (tch, Nothing) $ do
              mapM_ tell graphs
              OIn.simpl given wanted

unions :: Eq a => [[a]] -> [a]
unions = foldr union []
