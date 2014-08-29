{-# LANGUAGE CPP #-}
module Language.Cobalt.Solver.Step (
  SMonad
, SolutionStep(..)
, whileApplicable
, stepOverList
, stepOverProductList
, stepOverProductListDeleteBoth
, stepOverTwoLists
, myTrace
) where

import Control.Monad.Error
import Control.Monad.State
import Unbound.LocallyNameless
#define TRACE_SOLVER 0
#if TRACE_SOLVER
import Debug.Trace
#else
#endif

import Language.Cobalt.Syntax

type SMonad = StateT [TyVar] (ErrorT String FreshM)
data SolutionStep = NotApplicable | Applied [Constraint]

whileApplicable :: ([Constraint] -> SMonad ([Constraint], Bool))
                -> [Constraint] -> SMonad ([Constraint], Bool)
whileApplicable f c = innerApplicable' c False
  where innerApplicable' cs atAll = do
          r <- f cs
          case r of
            (_,   False) -> return (cs, atAll)
            (newC,True)  -> innerApplicable' newC True

stepOverList :: String -> ([Constraint] -> Constraint -> SMonad SolutionStep)
             -> [Constraint] -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverList s f extra lst = stepOverList' lst [] False
  where -- Finish cases: last two args are changed-in-this-loop, and changed-at-all
        -- stepOverList' [] accum True  _     = stepOverList' accum [] False True
        stepOverList' [] accum atAll = return (accum, atAll)
        -- Rest of cases
        stepOverList' (x:xs) accum atAll = do
          r <- {- myTrace (s ++ " " ++ show x) $ -} f (extra ++ xs ++ accum) x
          case r of
            NotApplicable -> stepOverList' xs (x:accum) atAll
            Applied newX  -> do -- vars <- get
                                myTrace (s ++ " " ++ show x ++ " ==> " ++ show newX {- ++ " tch:" ++ show vars -}) $
                                  stepOverList' xs (newX ++ accum) True

stepOverProductList :: String -> ([Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep)
                    -> [Constraint] -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverProductList s f given lst = stepOverProductList' lst []
  where stepOverProductList' []     accum = return (accum, False)
        stepOverProductList' (x:xs) accum = do
          r <- stepOverList (s ++ " " ++ show x) (\cs -> f given cs x) [] (xs ++ accum)
          case r of
            (_,     False) -> stepOverProductList' xs (x:accum)
            (newLst,True)  -> return (x:newLst, True)

stepOverProductListDeleteBoth :: String -> ([Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep)
                              -> [Constraint] -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverProductListDeleteBoth s f given lst = stepOverProductList' lst []
  where stepOverProductList' []     accum = return (accum, False)
        stepOverProductList' (x:xs) accum = do
          r <- stepOverList (s ++ " " ++ show x) (\cs -> f given cs x) [] (xs ++ accum)
          case r of
            (_,     False) -> stepOverProductList' xs (x:accum)
            (newLst,True)  -> return (newLst, True)

stepOverTwoLists :: String -> ([Constraint] -> [Constraint] -> Constraint -> Constraint -> SMonad SolutionStep)
                 -> [Constraint] -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverTwoLists s f given wanted = stepOverTwoLists' given [] wanted
  where stepOverTwoLists' []     _      w = return (w, False)
        stepOverTwoLists' (x:xs) accumG w = do
          r <- stepOverList (s ++ " " ++ show x) (\ws -> f (xs ++ accumG) ws x) [] wanted
          case r of
            (_,    False) -> stepOverTwoLists' xs (x:accumG) w
            (newW, True)  -> return (newW, True)

myTrace :: String -> a -> a
#if TRACE_SOLVER
myTrace = trace
#else
myTrace _ x = x
#endif
