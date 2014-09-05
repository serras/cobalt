{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Control.Lens
import Control.Monad.Except
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
  todo:file:rest <- getArgs
  let higher = case rest of
                 []         -> UseHigherRanks
                 "higher":_ -> UseHigherRanks
                 _          -> NoHigherRanks
  p <- parseFromFile parseFile file
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
            "solve"  -> showAnns (doPerDefn' (tcDefn higher) tcNextEnv env' defns) (showTc True)
            "report" -> showAnns (doPerDefn' (tcDefn higher) tcNextEnv env' defns) (showTc False)
            "gather" -> showAnns (doPerDefn' (gDefn higher) const env' defns) showG
            _ -> putStrLn "Unrecognized command"

doPerDefn' :: (Env -> Defn -> ExceptT String FreshM a)
           -> (Env -> a -> Env)
           -> Env -> [(Defn,Bool)] -> [(Either (TermVar,String) a,Bool)]
doPerDefn' f nx e d = runFreshM (doPerDefn f nx e d)

doPerDefn :: (Env -> Defn -> ExceptT String FreshM a)
          -> (Env -> a -> Env)
          -> Env -> [(Defn,Bool)] -> FreshM [(Either (TermVar,String) a,Bool)]
doPerDefn _ _ _ [] = return []
doPerDefn f nx e (((n,t,p),b):xs) = do r <- runExceptT (f e (n,t,p))
                                       case r of
                                         Left err -> do rest <- doPerDefn f nx e xs
                                                        return $ (Left (n,err),b) : rest
                                         Right ok -> do rest <- doPerDefn f nx (nx e ok) xs
                                                        return $ (Right ok,b) : rest

tcDefn :: UseHigherRanks -> Env -> Defn -> ExceptT String FreshM (AnnDefn,[Constraint])
tcDefn h e (n,t,Nothing) = do
  Gathered _ a g w <- runReaderT (gather h t) e
  let tch = fv (getAnn a) `union` fv w
  Solution smallG rs sb tch' <- solve g w tch
  let thisAnn = atAnn (substs sb) a
      finalT = nf $ closeExn (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  tcCheckErrors rs finalT
  return ((n,thisAnn,finalT),rs)
tcDefn h e (n,t,Just p) = do
  Gathered _ a g w <- runReaderT (gather h t) e
  (q1,t1,_) <- split p
  let extra = Constraint_Unify (getAnn a) t1
      tch = fv (getAnn a) `union` fv w
  Solution _smallG rs sb _tch' <- solve (g ++ q1) (extra:w) tch
  let thisAnn = atAnn (substs sb) a
      -- finalT = nf $ closeTypeWithException (smallG ++ rs) (getAnn thisAnn) (not . (`elem` tch'))
  if not (null rs) then throwError $ "Could not discharge: " ++ show rs
                   else return ((n,thisAnn,p),rs)

tcCheckErrors :: [Constraint] -> PolyType -> ExceptT String FreshM ()
tcCheckErrors rs t = do let fvT :: [TyVar] = fv t
                        when (not (null fvT)) $ throwError $ case fvT of
                          [x] -> show x ++ " is a rigid type variable in: " ++ show t
                          _   -> show fvT ++ " are rigid type variables in: " ++ show t
                        checkAmbiguity rs

checkAmbiguity :: [Constraint] -> ExceptT String FreshM ()
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
tcNextEnv e ((n,_,t),_) = e & fnE %~ ((n,t):)

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

gDefn :: UseHigherRanks -> Env -> Defn -> ExceptT String FreshM (TermVar,Gathered)
gDefn h e (n,t,Nothing) = do r <- runReaderT (gather h t) e
                             return (n, r)
gDefn h e (n,t,Just p)  = do Gathered typ a g w <- runReaderT (gather h t) e
                             (q1,t1,_) <- split p
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

