module Main where

import Control.Monad.Reader
import System.Console.ANSI
import System.Environment
import Text.Parsec.String
import Unbound.LocallyNameless

import Language.Cobalt.Infer
import Language.Cobalt.Parser (parseFile)
import Language.Cobalt.Syntax

main :: IO ()
main = do
  file:_ <- getArgs
  p <- parseFromFile parseFile file
  case p of
    Left ep -> do setSGR [SetColor Foreground Vivid Red]
                  putStr "Error while parsing: "
                  setSGR [Reset]
                  putStrLn (show ep)
    Right (env,defns) -> showAnns (tcDefns env defns)

tcDefns :: Env -> [Defn] -> [Either (TermVar,String) AnnDefn]
tcDefns _ []         = []
tcDefns e ((n,t):xs) = case tcDefn e (n,t) of
                         Left err -> Left (n,err) : tcDefns e xs
                         Right (n',p',t') -> (Right (n',p',t')) : (tcDefns ((n',t'):e) xs)

tcDefn :: Env -> Defn -> Either String AnnDefn
tcDefn e (n,t) = do Result _ a g w <- runReaderT (runFreshMT $ infer t) e
                    sl <- runFreshMT $ solve g w
                    let (smallC,sb) = toSubst sl
                        thisAnn = atAnn (substs sb) a
                        basicS = map (substs sb) g
                        finalT = closeType (basicS ++ smallC) (getAnn thisAnn)
                    return (n,thisAnn,finalT)

showAnns :: [Either (TermVar,String) AnnDefn] -> IO ()
showAnns [] = return ()
showAnns ((Left (n,e)):xs) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "error"
  setSGR [Reset]
  putStrLn e
  putStrLn ""
  showAnns xs
showAnns ((Right (n,t,p)):xs) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  putStrLn (show p)
  putStrLn (show t)
  showAnns xs
