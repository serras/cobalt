{-# LANGUAGE RecordWildCards #-}
module Cobalt.ErrorSimpl (
  simplifyErrorExplanation
-- , addLeadsTo
) where

import Control.Applicative
import Data.List (find)
import Data.Maybe (isNothing)
import Unbound.LocallyNameless

-- import Cobalt.Graph
import Cobalt.Errors
import Cobalt.Types

{-
addLeadsTo :: Graph -> ErrorExplanation -> ErrorExplanation
addLeadsTo g s@(SolverError { theBlame = b }) = s { theBlame = map (addLeadsTo' g) b }
addLeadsTo _ s = s

addLeadsTo' :: Graph -> AnnConstraint -> AnnConstraint
addLeadsTo' g (constraint, cm) = case filterLeads (getPathOfUniques g constraint) of
                                   [first] -> (first, cm)
                                   first : rest -> (first, cm ++ [Comment_LeadsTo rest])
                                   [] -> error "This should never happen"

filterLeads :: [Constraint] -> [Constraint]
filterLeads [] = []
filterLeads (Constraint_Equal _ _ : u@(Constraint_Unify _ _) : rest) = filterLeads (u : rest)
filterLeads (Constraint_Inst  _ _ : u@(Constraint_Unify _ _) : rest) = filterLeads (u : rest)
filterLeads (Constraint_Unify a1 b1 : u@(Constraint_Unify b2 a2) : rest) | a1 == a2, b1 == b2 = filterLeads (u : rest)
filterLeads (c : rest) = c : filterLeads rest
-}

-- | Runs all the different stages of simplification
simplifyErrorExplanation :: ErrorExplanation -> ErrorExplanation
simplifyErrorExplanation s@(SolverError { .. }) = s { theBlame = simplifyBlame theBlame }
simplifyErrorExplanation s = s

-- | Simplification by iterated substitution
simplifyBlame :: Blame -> Blame
simplifyBlame b = simplifyBlame' b []

simplifyBlame' :: Blame -> Blame -> Blame
simplifyBlame' []       acc = acc
simplifyBlame' (e:rest) acc = case doOneSimplifyBlame e (reverse acc ++ rest) of
  (Just (_, newRest), True)  -> simplifyBlame newRest
  (Just (me,newRest), False) -> simplifyBlame (me:newRest)
  (Nothing,           _)     -> simplifyBlame' rest (e:acc)

doOneSimplifyBlame :: AnnConstraint -> Blame -> (Maybe (AnnConstraint, Blame), Bool)  -- last Bool = should be deleted?
-- Simplify monotyped > and = to ~
doOneSimplifyBlame (Constraint_Equal v (PolyType_Mono [] m), info) b = (Just ((Constraint_Unify v m, info),b), False)
doOneSimplifyBlame (Constraint_Inst  v (PolyType_Mono [] m), info) b = (Just ((Constraint_Unify v m, info),b), False)
-- Insert ~ into other constraints
doOneSimplifyBlame cc@(Constraint_Unify (MonoType_Var v) m, info) b | noComments info = loop b
  where loop [] = (Nothing, True)
        loop ((c, info2) : rest)
          | v `elem` fv c = let mixed = (subst v m c, mixInfo info info2) in case loop rest of
                              (Just (_,rst), del) -> (Just (cc, mixed : rst),  del)
                              (Nothing,      del) -> (Just (cc, mixed : rest), del)
          | otherwise = let (rst, del) = loop rest
                            changeRst (_, info3) = (cc, (c,info2) : info3)
                         in (changeRst <$> rst, del)
doOneSimplifyBlame _ _ = (Nothing, False)

noComments :: [Comment] -> Bool
noComments = isNothing . find (\x -> case x of { Comment_String _ -> True; _ -> False })

mixInfo :: [Comment] -> [Comment] -> [Comment]
mixInfo [] bs = bs
mixInfo (Comment_Pos (e,i) : rest)    bs = mixInfo rest (mixPos bs)
  where mixPos [] = [Comment_Pos (e,i)]
        mixPos (Comment_Pos (e2,i2) : rst) = Comment_Pos (min e e2, max i i2) : rst
        mixPos (comment : rst) = comment : mixPos rst
mixInfo (c : rest) bs = c : mixInfo rest bs