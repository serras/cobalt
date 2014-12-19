{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module Cobalt.Core.Graph (
  Graph
, vertices
, edges
, emptyGraph
, singletonDeleted
, singletonCommented
, singletonEdge
, singletonNodeWithTwoParents
, singletonNodeOrphan
, blameConstraints
, getDominators
) where

import qualified Data.Graph.Inductive as D
import Data.List
import Data.Maybe
import Data.Monoid

import Cobalt.Core.Errors
import Cobalt.Core.Types

{-# ANN module ("HLint: ignore Use map once"::String) #-}

data Graph = Graph { counter  :: Int
                   , vertices :: [(Constraint, (Int, Bool, [Comment]))]
                   , edges    :: [(Int, Int, String)] }
             deriving (Show, Eq)

emptyGraph :: Graph
emptyGraph = Graph 0 [] []

addVertexWithComment :: Constraint -> [Comment] -> Graph -> (Graph, Int)
addVertexWithComment c newComment g = case lookup c (vertices g) of
  Just (i,_,_) -> ( g { vertices = map (\e@(c',(i',d',cm')) -> if i == i' then (c',(i',d',cm' ++ newComment)) else e) (vertices g) }  -- Update comment
                  , i)  -- Already there
  Nothing      -> let newVertices = vertices g ++ [(c,(counter g, False, newComment))]
                   in ( g { counter  = counter g + 1, vertices = newVertices }
                      , counter g )

markVertexAsDeleted :: Constraint -> Graph -> Graph
markVertexAsDeleted cs g = g { vertices = map (\e@(c,(n,_,_)) -> if c == cs then (c,(n,True,[])) else e)
                                              (vertices g) }

singletonDeleted :: Constraint -> Graph
singletonDeleted c = Graph { counter  = 1
                           , vertices = [(c,(0,True,[]))]
                           , edges    = [] }

singletonCommented :: Constraint -> [Comment] -> Graph
singletonCommented c comment = Graph { counter  = 1
                                     , vertices = [(c,(0,False,comment))]
                                     , edges    = [] }

singletonEdge :: Constraint -> Constraint -> String -> Graph
singletonEdge c1 c2 s = Graph { counter  = 2
                              , vertices = [(c1,(0,False,[])),(c2,(1,False,[]))]
                              , edges    = [(0,1,s)] }

singletonNodeWithTwoParents :: Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeWithTwoParents c1 c2 child s =
  Graph { counter  = 3
        , vertices = [(c1,(0,False,[])),(c2,(1,False,[])),(child,(2,False,[]))]
        , edges    = [(0,2,s),(1,2,s)] }

singletonNodeOrphan :: Maybe Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeOrphan Nothing  = singletonEdge
singletonNodeOrphan (Just x) = singletonNodeWithTwoParents x

merge :: Graph -> Graph -> Graph
merge g1 (Graph _cnt2 vrt2 nod2) =
  let (Graph cnt1' vrt1' nod1', subst) =
        foldr (\(e2,(n2,b2,c2)) (currentG,currentSubst) ->
                  let (newG,newN) = addVertexWithComment e2 c2 currentG
                      newG' = if b2 then markVertexAsDeleted e2 newG else newG
                   in (newG',(n2,newN):currentSubst)) (g1,[]) vrt2
      newNodes = map (\(n1,n2,s) -> (fromJust (lookup n1 subst), fromJust (lookup n2 subst), s))
                     nod2
   in Graph { counter  = cnt1'
            , vertices = vrt1'
            , edges    = nod1' `union` newNodes }

instance Monoid Graph where
  mempty  = emptyGraph
  mappend = merge

blameConstraints :: Graph -> Constraint -> [(Constraint, [Comment])]
blameConstraints (Graph { .. }) problem
  | Just (_,(n,_,_)) <- find ((== problem) . fst) vertices = blame [n]
  | otherwise = []  -- No one to blame
  where blame lst = let newLst = nub $ sort $ lst `union` mapMaybe (\(o,d,_) -> if d `elem` lst then Just o else Nothing) edges
                     in if length newLst /= length lst
                           then blame newLst -- next step
                           else let lasts = filter (\n -> isNothing (find (\(_,d,_) -> d == n) edges)) newLst
                                 in map (\(c,(_,_,cm)) -> (c,cm)) $ mapMaybe (\n -> find (\(_,(m,_,_)) -> n == m) vertices) lasts

{-
getPathOfUniques :: Graph -> Constraint -> [Constraint]
getPathOfUniques (Graph _ vrtx edges) c
  | Just (_,(n,_,_)) <- find ((== c) . fst) vrtx =
      map (\m -> fst $ fromJust $ find (\(_,(u,_,_)) -> u == m) vrtx) $ getPathOfUniques' n
      where getPathOfUniques' current = case [next | (origin,next,_) <- edges, origin == current] of
                                          [one] -> case [past | (past,destination,_) <- edges, destination == one] of
                                                     [_] -> current : getPathOfUniques' one
                                                     _   -> [current]
                                          _     -> [current]
getPathOfUniques _ c = [c]
-}

getDominators :: Graph -> Constraint -> [Constraint]
getDominators g@(Graph _ vrtx edges) problem | Just (_,(n,_,_)) <- find ((== problem) . fst) vrtx =
  let blamed = map fst $ blameConstraints g problem
      extGraph :: D.UGr = D.mkUGraph (map (\(_,(i,_,_)) -> i) vrtx) (map (\(a,b,_) -> (a,b)) edges)
      initial :: [Int]
      initial = map (\(_,(m,_,_)) -> m) $ map fromJust $ map (\b -> find ((== b) . fst) vrtx) blamed
      getDomFor :: Int -> [Int]
      getDomFor m = snd $ fromJust $ find (\(to, _) -> to == n) $ D.dom extGraph m
      allDominators :: [[Int]]
      allDominators = map getDomFor initial
      jointDominators :: [Int]
      jointDominators = foldl' intersect (map (\(_,(i,_,_)) -> i) vrtx) allDominators
   in map (\b -> fst $ fromJust $ find (\(_,(i,_,_)) -> i == b) vrtx) (delete n jointDominators)
getDominators _ _ = []