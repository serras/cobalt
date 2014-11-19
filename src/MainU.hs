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
            "solve"  -> putStrLn "Not yet implemented"
            "report" -> putStrLn "Not yet implemented"
            "gather" -> gatherDefns env' defns
            _ -> putStrLn "Unrecognized command"

gatherDefns :: Env -> [(RawDefn,Bool)] -> IO ()
gatherDefns env defns = do
  let gaths = gDefns env defns
  mapM_ showGathered (zip defns gaths)

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
showGathered (((n,_,_),_), Right (Gathered _ w _)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStrLn (name2String n)
  setSGR [Reset]
  putStrLn (show w)
  putStrLn ""
