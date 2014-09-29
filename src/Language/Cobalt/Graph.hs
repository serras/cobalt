module Language.Cobalt.Graph where

import Data.List (union)
import Data.Maybe (fromJust)
import Data.Monoid

import Language.Cobalt.Types

data Graph = Graph { counter  :: Int
                   , vertices :: [(Constraint,(Int,Bool))]
                   , nodes    :: [(Int,Int,String)] }
             deriving (Show, Eq)

empty :: Graph
empty = Graph 0 [] []

addVertex :: Constraint -> Graph -> (Graph, Int)
addVertex c g = case lookup c (vertices g) of
                  Just (i,_) -> (g, i)  -- Already there
                  Nothing    -> let newVertices = (vertices g) ++ [(c,(counter g,False))]
                                 in ( g { counter  = counter g + 1, vertices = newVertices }
                                    , counter g )

markVertexAsDeleted :: Constraint -> Graph -> Graph
markVertexAsDeleted cs g = g { vertices = map (\e@(c,(n,_)) -> if c == cs then (c,(n,True)) else e)
                                              (vertices g) }

singletonDeleted :: Constraint -> Graph
singletonDeleted c = Graph { counter  = 1
                           , vertices = [(c,(0,True))]
                           , nodes    = [] }

singletonNode :: Constraint -> Constraint -> String -> Graph
singletonNode c1 c2 s = Graph { counter  = 2
                              , vertices = [(c1,(0,False)),(c2,(1,False))]
                              , nodes    = [(0,1,s)] }

singletonNodeWithTwoParents :: Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeWithTwoParents c1 c2 child s =
  Graph { counter  = 3
        , vertices = [(c1,(0,False)),(c2,(1,False)),(child,(2,False))]
        , nodes    = [(0,2,s),(1,2,s)] }

singletonNodeOrphan :: Maybe Constraint -> Constraint -> Constraint -> String -> Graph
singletonNodeOrphan Nothing  = singletonNode
singletonNodeOrphan (Just x) = singletonNodeWithTwoParents x

merge :: Graph -> Graph -> Graph
merge g1 (Graph _cnt2 vrt2 nod2) =
  let (Graph cnt1' vrt1' nod1', subst) =
        foldr (\(e2,(n2,b2)) (currentG,currentSubst) ->
                  let (newG,newN) = addVertex e2 currentG
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
