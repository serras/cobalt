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
    Right (env,defns) -> case tcDefns env defns of
      Left et -> do setSGR [SetColor Foreground Vivid Red]
                    putStr "Error while type checking: "
                    setSGR [Reset]
                    putStrLn (show et)
      Right d -> showAnns d

tcDefns :: Env -> [Defn] -> Either String [AnnDefn]
tcDefns _ []         = return []
tcDefns e ((n,t):xs) =
  case runReaderT (runFreshMT $ infer t) e of
    Left err -> Left err
    Right (Result _ a g w) -> case runFreshMT $ solve g w of
      Left err -> Left err
      Right sl -> do
        let (smallC,sb) = toSubst sl
            thisAnn = atAnn (substs sb) a
            basicS = map (substs sb) g
            finalT = closeType (basicS ++ smallC) (getAnn thisAnn)
        restAnn <- tcDefns ((n,finalT):e) xs
        return $ (n,thisAnn,finalT) : restAnn

showAnns :: [AnnDefn] -> IO ()
showAnns []         = return ()
showAnns ((n,t,p):xs) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  putStrLn (show p)
  putStrLn (show t)
  showAnns xs
