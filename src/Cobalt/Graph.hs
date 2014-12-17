module Cobalt.Graph where

import Data.List
import Data.Maybe
import Data.Monoid

import Cobalt.Errors
import Cobalt.Types

data Graph = Graph { counter  :: Int
                   , vertices :: [(Constraint, (Int, Bool, [Comment]))]
                   , nodes    :: [(Int, Int, String)] }
             deriving (Show, Eq)

empty :: Graph
empty = Graph 0 [] []

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
                           , nodes    = [] }

singletonCommented :: Constraint -> [Comment] -> Graph
singletonCommented c comment = Graph { counter  = 1
                                     , vertices = [(c,(0,False,comment))]
                                     , nodes    = [] }

singletonNode :: Constraint -> Constraint -> String -> Graph
singletonNode c1 c2 s = Graph { counter  = 2
                              , vertices = [(c1,(0,False,[])),(c2,(1,False,[]))]
                              , nodes    = [(0,1,s)] }

singletonNodeWithTwoParents :: Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeWithTwoParents c1 c2 child s =
  Graph { counter  = 3
        , vertices = [(c1,(0,False,[])),(c2,(1,False,[])),(child,(2,False,[]))]
        , nodes    = [(0,2,s),(1,2,s)] }

singletonNodeOrphan :: Maybe Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeOrphan Nothing  = singletonNode
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
            , nodes    = nod1' `union` newNodes }

instance Monoid Graph where
  mempty  = empty
  mappend = merge

blameConstraints :: Graph -> Constraint -> [(Constraint, [Comment])]
blameConstraints (Graph _ vrtx edges) problem
  | Just (_,(n,_,_)) <- find ((== problem) . fst) vrtx = blame [n]
  | otherwise = []  -- No one to blame
  where blame lst = let newLst = nub $ sort $ lst `union` mapMaybe (\(o,d,_) -> if d `elem` lst then Just o else Nothing) edges
                     in if length newLst /= length lst
                           then blame newLst -- next step
                           else let lasts = filter (\n -> isNothing (find (\(_,d,_) -> d == n) edges)) newLst
                                 in map (\(c,(_,_,cm)) -> (c,cm)) $ mapMaybe (\n -> find (\(_,(m,_,_)) -> n == m) vrtx) lasts

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