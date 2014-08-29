{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Monad.Error
import Control.Monad.Reader
import System.Console.ANSI
import System.Environment
import Text.Parsec.String
import Unbound.LocallyNameless

import Language.Cobalt.Gather
import Language.Cobalt.Parser (parseFile)
import Language.Cobalt.Solver
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
    Right (env,denv,defns) ->
      let denv' = denv ++ initialDataEnv
       in case todo of
            "parse"  -> do mapM_ (putStrLn . show) env
                           putStrLn ""
                           mapM_ (putStrLn . show) denv
                           putStrLn ""
                           mapM_ (putStrLn . show) defns
            "solve"  -> showAnns (doPerDefn' tcDefn tcNextEnv env denv' defns) (showTc True)
            "report" -> showAnns (doPerDefn' tcDefn tcNextEnv env denv' defns) (showTc False)
            "gather" -> showAnns (doPerDefn' gDefn const env denv' defns) showG
            _ -> putStrLn "Unrecognized command"

doPerDefn' :: (Env -> DataEnv -> Defn -> ErrorT String FreshM a)
           -> (Env -> a -> Env)
           -> Env -> DataEnv -> [(Defn,Bool)] -> [(Either (TermVar,String) a,Bool)]
doPerDefn' f nx e de d = runFreshM (doPerDefn f nx e de d)

doPerDefn :: (Env -> DataEnv -> Defn -> ErrorT String FreshM a)
          -> (Env -> a -> Env)
          -> Env -> DataEnv -> [(Defn,Bool)] -> FreshM [(Either (TermVar,String) a,Bool)]
doPerDefn _ _ _ _ [] = return []
doPerDefn f nx e de (((n,t,p),b):xs) = do r <- runErrorT (f e de (n,t,p))
                                          case r of
                                            Left err -> do rest <- doPerDefn f nx e de xs
                                                           return $ (Left (n,err),b) : rest
                                            Right ok -> do rest <- doPerDefn f nx (nx e ok) de xs
                                                           return $ (Right ok,b) : rest

tcDefn :: Env -> DataEnv -> Defn -> ErrorT String FreshM (AnnDefn,[Constraint])
tcDefn e de (n,t,Nothing) = do
  Gathered _ a g w <- runReaderT (gather t) (e,de)
  let tch = fv (getAnn a) `union` fv w
  Solution smallG rs sb tch' <- solve g w tch
  let thisAnn = atAnn (substs sb) a
      finalT = nf $ closeTypeWithException (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  tcCheckErrors rs finalT
  return ((n,thisAnn,finalT),rs)
tcDefn e de (n,t,Just p) = do
  Gathered _ a g w <- runReaderT (gather t) (e,de)
  (q1,t1,_) <- splitType p
  let extra = Constraint_Unify (getAnn a) t1
      tch = fv (getAnn a) `union` fv w
  Solution _smallG rs sb _tch' <- solve (g ++ q1) (extra:w) tch
  let thisAnn = atAnn (substs sb) a
      -- finalT = nf $ closeTypeWithException (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  if not (null rs) then throwError $ "Could not discharge: " ++ show rs
                   else return ((n,thisAnn,p),rs)

tcCheckErrors :: [Constraint] -> PolyType -> ErrorT String FreshM ()
tcCheckErrors rs t = do let fvT :: [TyVar] = fv t
                        when (not (null fvT)) $ throwError $ case fvT of
                          [x] -> show x ++ " is a rigid type variable in: " ++ show t
                          _   -> show fvT ++ " are rigid type variables in: " ++ show t
                        checkAmbiguity rs

checkAmbiguity :: [Constraint] -> ErrorT String FreshM ()
checkAmbiguity cs = do let vars = map getVar cs
                           dup  = findDuplicate vars
                       case dup of
                         Nothing -> return ()
                         Just v  -> let cs' = filter (\c -> getVar c == v) cs
                                     in throwError $ "Ambiguous variable " ++ show v ++ ": " ++ show cs'

getVar :: Constraint -> TyVar
getVar (Constraint_Inst  (MonoType_Var v) _) = v
getVar (Constraint_Equal (MonoType_Var v) _) = v
getVar _ = error "This should never happen"

findDuplicate :: Eq a => [a] -> Maybe a
findDuplicate []     = Nothing
findDuplicate (x:xs) = if x `elem` xs then Just x else findDuplicate xs

tcNextEnv :: Env -> (AnnDefn,a) -> Env
tcNextEnv e ((n,_,t),_) = (n,t):e

showTc :: Bool -> ((AnnDefn,[Constraint]),Bool) -> IO ()
showTc always (((n,t,p),cs),b) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  if b then setSGR [SetColor Foreground Vivid Green]
       else setSGR [SetColor Foreground Vivid Red]
  putStrLn (show p)
  setSGR [Reset]
  setSGR [SetColor Foreground Vivid Yellow]
  putStr " res: "
  setSGR [Reset]
  putStrLn (show cs)
  when (not b || always) $ do
    putStrLn (show t)

gDefn :: Env -> DataEnv -> Defn -> ErrorT String FreshM (TermVar,Gathered)
gDefn e de (n,t,Nothing) = do r <- runReaderT (gather t) (e,de)
                              return (n, r)
gDefn e de (n,t,Just p)  = do Gathered typ a g w <- runReaderT (gather t) (e,de)
                              (q1,t1,_) <- splitType p
                              let extra = Constraint_Unify (getAnn a) t1
                              return (n, Gathered typ a (g ++ q1) (extra:w))

showG :: ((TermVar,Gathered),Bool) -> IO ()
showG ((n,(Gathered t ann g w)),_) = do
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

showAnns :: [(Either (TermVar,String) a,Bool)] -> ((a,Bool) -> IO ()) -> IO ()
showAnns [] _ = return ()
showAnns ((Left (n,e),b):xs) f = do
  when b $ putStrLn ""
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  if b then setSGR [SetColor Foreground Vivid Red]
       else setSGR [SetColor Foreground Vivid Green]
  putStrLn "error"
  setSGR [Reset]
  putStr " "
  putStrLn e
  when b $ putStrLn ""
  showAnns xs f
showAnns ((Right ok,b):xs) f = do
  when (not b) $ putStrLn ""
  f (ok,b)
  showAnns xs f

