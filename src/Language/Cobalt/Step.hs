{-# LANGUAGE CPP #-}
module Language.Cobalt.Step (
  SMonad
, StepResult(..)
, whileApplicable
, stepOverList
, stepOverProductList
) where

import Unbound.LocallyNameless
#define TRACE_SOLVER 0
#if TRACE_SOLVER
import Debug.Trace
#else
#endif

import Language.Cobalt.Syntax

type SMonad = FreshMT (Either String)
data StepResult = NotApplicable | Applied [Constraint]

whileApplicable :: ([Constraint] -> SMonad ([Constraint], Bool))
                -> [Constraint] -> SMonad ([Constraint], Bool)
whileApplicable f c = innerApplicable' c False
  where innerApplicable' cs atAll = do
          r <- f cs
          case r of
            (_,   False) -> return (cs, atAll)
            (newC,True)  -> innerApplicable' newC True

stepOverList :: String -> (Constraint -> SMonad StepResult)
             -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverList s f lst = stepOverList' lst [] False False
  where -- Finish cases: last two args are changed-in-this-loop, and changed-at-all
        stepOverList' [] accum True  _     = stepOverList' accum [] False True
        stepOverList' [] accum False atAll = return (accum, atAll)
        -- Rest of cases
        stepOverList' (x:xs) accum thisLoop atAll = do
          r <- f x
          case r of
            NotApplicable -> stepOverList' xs (x:accum) thisLoop atAll
            Applied newX  -> myTrace (s ++ " " ++ show x ++ " ==> " ++ show newX) $
                             stepOverList' xs (newX ++ accum) True True

stepOverProductList :: String -> (Constraint -> Constraint -> SMonad StepResult)
                    -> [Constraint] -> SMonad ([Constraint], Bool)
stepOverProductList s f lst = stepOverProductList' lst [] False
  where stepOverProductList' [] accum atAll = return (accum, atAll)
        stepOverProductList' (x:xs) accum atAll =
          do r <- stepOverList (s ++ " " ++ show x) (f x) (xs ++ accum)
             case r of
               (_,     False) -> stepOverProductList' xs (x:accum) atAll
               (newLst,True)  -> stepOverProductList' (x:newLst) [] True

myTrace :: String -> a -> a
#if TRACE_SOLVER
myTrace = trace
#else
myTrace _ x = x
#endif
