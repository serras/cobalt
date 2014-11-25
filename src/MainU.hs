module Main where

import Control.Lens hiding ((.=))
import System.Console.ANSI
import System.Environment
-- import Text.Parsec (parse)
import Text.Parsec.String
import Unbound.LocallyNameless

import Cobalt.Language.Parser (parseFile)
import Cobalt.Language.Syntax
import Cobalt.Script.Gather
import Cobalt.Script.Top

main :: IO ()
main = do
  todo:fname:_ <- getArgs
  p <- parseFromFile parseFile fname
  case p of
    Left ep -> do setSGR [SetColor Foreground Vivid Red]
                  putStr "Error while parsing: "
                  setSGR [Reset]
                  putStrLn (show ep)
    Right (env, defns) ->
      let env' =  env & dataE %~ (++ initialDataEnv)
       in case todo of
            "parse"  -> do putStrLn $ show env
                           putStrLn ""
                           mapM_ (putStrLn . show) defns
            "solve"  -> solveDefns env' defns
            "report" -> putStrLn "Not yet implemented"
            "gather" -> gatherDefns env' defns
            _ -> putStrLn "Unrecognized command"

gatherDefns :: Env -> [(RawDefn,Bool)] -> IO ()
gatherDefns env defns = do
  let gaths = gDefns env defns
  mapM_ showGathered (zip defns gaths)

solveDefns :: Env -> [(RawDefn,Bool)] -> IO ()
solveDefns env defns = do
  let sols = tcDefns env defns
  mapM_ showSolved (zip defns sols)

showGathered :: ((RawDefn,Bool), Either [String] Gathered) -> IO ()
showGathered (((n,_,_),_), Left errors) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "error"
  setSGR [Reset]
  mapM_ putStrLn errors
  putStrLn ""
showGathered (((n,_,_),_), Right (Gathered _ [w] _)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStrLn (name2String n)
  setSGR [Reset]
  putStrLn (show w)
  putStrLn ""
showGathered _ = do
  setSGR [SetColor Foreground Vivid Blue]
  putStrLn "ERROR: the grammar returned more than one result"
  setSGR [Reset]
  putStrLn ""

showSolved :: Show a => ((RawDefn,Bool), a) -> IO ()
showSolved (((n,_,_),_), sol) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [Reset]
  putStrLn (show sol)
  putStrLn ""
