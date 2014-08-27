{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Monad.Error
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
  todo:file:_ <- getArgs
  p <- parseFromFile parseFile file
  case p of
    Left ep -> do setSGR [SetColor Foreground Vivid Red]
                  putStr "Error while parsing: "
                  setSGR [Reset]
                  putStrLn (show ep)
    Right (env,defns) -> case todo of
                           "solve"  -> showAnns (doPerDefn' tcDefn tcNextEnv env defns) showTc
                           "gather" -> showAnns (doPerDefn' gDefn const env defns) showG
                           _ -> putStrLn "Unrecognized command"

doPerDefn' :: (Env -> Defn -> ErrorT String FreshM a)
           -> (Env -> a -> Env)
           -> Env -> [Defn] -> [Either (TermVar,String) a]
doPerDefn' f nx e d = runFreshM (doPerDefn f nx e d)

doPerDefn :: (Env -> Defn -> ErrorT String FreshM a)
          -> (Env -> a -> Env)
          -> Env -> [Defn] -> FreshM [Either (TermVar,String) a]
doPerDefn _ _ _ [] = return []
doPerDefn f nx e ((n,t,p):xs) = do r <- runErrorT (f e (n,t,p))
                                   case r of
                                     Left err -> do rest <- doPerDefn f nx e xs
                                                    return $ Left (n,err) : rest
                                     Right ok -> do rest <- doPerDefn f nx (nx e ok) xs
                                                    return $ Right ok : rest

tcDefn :: Env -> Defn -> ErrorT String FreshM (AnnDefn,[Constraint])
tcDefn e (n,t,Nothing) = do
  Gathered _ a g w <- runReaderT (gather t) e
  let tch = fv (getAnn a) `union` fv w
  Solution smallG rs sb tch' <- solve g w tch
  let thisAnn = atAnn (substs sb) a
      finalT = nf $ closeTypeWithException (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  tcCheckErrors rs finalT
  return ((n,thisAnn,finalT),rs)
tcDefn e (n,t,Just p) = do
  Gathered _ a g w <- runReaderT (gather t) e
  let extra = Constraint_Inst (getAnn a) p
      tch = fv (getAnn a) `union` fv w
  Solution smallG rs sb tch' <- solve g (extra:w) tch
  let thisAnn = atAnn (substs sb) a
      finalT = nf $ closeTypeWithException (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  tcCheckErrors rs finalT
  return ((n,thisAnn,finalT),rs)

tcCheckErrors :: [Constraint] -> PolyType -> ErrorT String FreshM ()
tcCheckErrors _rs t = do let fvT :: [TyVar] = fv t
                         when (not (null fvT)) $ throwError (show (fvT) ++ " are rigid type variables in " ++ show t)

tcNextEnv :: Env -> (AnnDefn,a) -> Env
tcNextEnv e ((n,_,t),_) = (n,t):e

showTc :: (AnnDefn,[Constraint]) -> IO ()
showTc ((n,t,p),cs) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  putStrLn (show p)
  setSGR [SetColor Foreground Vivid Green]
  putStr " res: "
  setSGR [Reset]
  putStrLn (show cs) 
  putStrLn (show t)

gDefn :: Env -> Defn -> ErrorT String FreshM (TermVar,Gathered)
gDefn e (n,t,_) = do r <- runReaderT (gather t) e
                     return (n,r)

showG :: (TermVar,Gathered) -> IO ()
showG (n,(Gathered t ann g w)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  putStrLn (show t)
  setSGR [SetColor Foreground Vivid Green]
  putStr "Solve "
  setSGR [Reset]
  putStr (show g)
  setSGR [SetColor Foreground Vivid Green]
  putStr " ||- "
  setSGR [Reset]
  putStrLn (show w)
  putStrLn (show ann)

showAnns :: [Either (TermVar,String) a] -> (a -> IO ()) -> IO ()
showAnns [] _ = return ()
showAnns ((Left (n,e)):xs) f = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "error"
  setSGR [Reset]
  putStrLn e
  putStrLn ""
  showAnns xs f
showAnns (Right ok:xs) f = do
  f ok
  showAnns xs f

