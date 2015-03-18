{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Main where

import Control.Lens hiding ((.=))
import Control.Monad.Except
import Data.Aeson hiding (json)
import Data.List (intercalate)
import System.Console.ANSI
import System.Environment
import Text.Parsec (parse)
import Text.Parsec.String
import Unbound.LocallyNameless
import Web.Scotty

import Cobalt.Core
import Cobalt.Language
import Cobalt.OutsideIn
import Util.Show

main :: IO ()
main = do
  todo:_ <- getArgs
  case todo of
   "serve" -> mainServe
   _       -> mainCmd

mainCmd :: IO ()
mainCmd = do
  todo:fname:rest <- getArgs
  let higher = case rest of
                 []         -> UseHigherRanks
                 "higher":_ -> UseHigherRanks
                 _          -> NoHigherRanks
  p <- parseFromFile parseFile fname
  case p of
    Left ep -> do setSGR [SetColor Foreground Vivid Red]
                  putStr "Error while parsing: "
                  setSGR [Reset]
                  print ep
    Right (env, defns) ->
      let env' =  env & dataE %~ (++ initialDataEnv)
       in case todo of
            "parse"  -> do print env
                           putStrLn ""
                           mapM_ print defns
            "solve"  -> showAnns (tcDefns higher env' defns) (showTc True)
            "report" -> showAnns (tcDefns higher env' defns) (showTc False)
            "gather" -> showAnns (gDefns higher env' defns) showG
            _ -> putStrLn "Unrecognized command"

mainServe :: IO ()
mainServe = do
  _:port:_ <- getArgs
  scotty (read port) $ do
    get "/" $ do
      setHeader "Content-Type" "text/html; charset=utf-8"
      file "static/editor.html"
    post "/typecheck" $ do
      code <- param "code"
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) -> let env' = env & dataE %~ (++ initialDataEnv)
                                 vals = showJsonAnns (tcDefns UseHigherRanks env' defns)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    post "/gather" $ do
      code <- param "code"
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) -> let env' = env & dataE %~ (++ initialDataEnv)
                                 vals = showJsonConstraints (gDefns UseHigherRanks env' defns)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    get "/example/:file" $ do
      fname <- param "file"
      file $ "test/" ++ fname
    get "/:dir/:file" $ do
      dname <- param "dir"
      fname <- param "file"
      file $ "static/" ++ dname ++ "/" ++ fname
    get "/:file" $ do
      fname <- param "file"
      file $ "static/" ++ fname

showTc :: Bool -> ((TyDefn,[Constraint]),Graph,Bool) -> IO ()
showTc always (((n,t,p),cs),gr,b) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  if b then setSGR [SetColor Foreground Vivid Green]
       else setSGR [SetColor Foreground Vivid Red]
  print p
  setSGR [Reset]
  setSGR [SetColor Foreground Vivid Yellow]
  putStr " res: "
  setSGR [Reset]
  putStrLn (showConstraintList cs)
  when (not b || always) $ do
    putStr (show t)
    setSGR [SetColor Foreground Vivid Yellow]
    putStr "graph: "
    setSGR [Reset]
    print gr
    putStrLn ""

showG :: ((TyTermVar,Gathered,[TyVar]),Graph,Bool) -> IO ()
showG ((n,(Gathered t annot g w),_),_,_) = do
  let tch :: [TyVar] = fv (getAnn annot) `union` fv w
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  print t
  setSGR [SetColor Foreground Vivid Green]
  putStr "Solve "
  setSGR [Reset]
  putStr (showConstraintList g)
  setSGR [SetColor Foreground Vivid Green]
  putStr " ||- "
  setSGR [Reset]
  putStrLn (showConstraintList w)
  setSGR [SetColor Foreground Vivid Green]
  putStr "Touchables "
  setSGR [Reset]
  print tch
  print annot

showAnns :: Show err => [(Either (RawTermVar,err) a, Graph, Bool)] -> ((a,Graph,Bool) -> IO ()) -> IO ()
showAnns [] _ = return ()
showAnns ((Left (n,e),_,b):xs) f = do
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
  print e
  when b $ putStrLn ""
  showAnns xs f
showAnns ((Right ok,g,b):xs) f = do
  unless b $ putStrLn ""
  f (ok,g,b)
  showAnns xs f

showJsonAnns :: Show err => [(Either (RawTermVar,err) (TyDefn,[Constraint]), Graph, Bool)] -> [Value]
showJsonAnns [] = []
showJsonAnns ((Left (n,e),gr,b):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [showWithGreek e]
                    , "color" .= ("white" :: String)
                    , "backColor" .= if b then ("#F58471" :: String)  -- red
                                          else ("#F1B75B" :: String)  -- yellow
                    , "graph" .= showJsonGraph gr (map fst $ blameConstraints gr Constraint_Inconsistent) ]
   in this : showJsonAnns xs
showJsonAnns ((Right ((n,t,p),_cs),gr,b):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [showWithGreek p]
                    , "color" .= ("white" :: String)
                    , "backColor" .= if b then ("#85C99E" :: String)  -- green
                                          else ("#F58471" :: String)  -- red
                    , "nodes" .= runFreshM (showAnnTermJson t)
                    , "graph" .= showJsonGraph gr [] ]
   in this : showJsonAnns xs

showAnnTermJson :: Fresh m => TyTerm -> m [Value]
showAnnTermJson (Term_IntLiteral n t) =
  return [ object [ "text"  .= show n
                  , "tags"  .= [showWithGreek t] ] ]
showAnnTermJson (Term_StrLiteral n t) =
  return [ object [ "text"  .= show n
                  , "tags"  .= [showWithGreek t] ] ]
showAnnTermJson (Term_Var v t) =
  return [ object [ "text"  .= show v
                  , "tags"  .= [showWithGreek t] ] ]
showAnnTermJson (Term_Abs b _ t) = do
  (x,e) <- unbind b
  inner <- showAnnTermJson e
  return [ object [ "text"  .= ("λ " ++ show x ++ " →")
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= inner ] ]
showAnnTermJson (Term_AbsAnn b _ p t) = do
  (x,e) <- unbind b
  inner <- showAnnTermJson e
  return [ object [ "text"  .= ("λ (" ++ show x ++ " :: " ++ showWithGreek p ++ ") →")
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= inner ] ]
showAnnTermJson (Term_App a b t) = do
  e1 <- showAnnTermJson a
  e2 <- showAnnTermJson b
  return [ object [ "text"  .= ("@" :: String)
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= (e1 ++ e2) ] ]
showAnnTermJson (Term_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTermJson e1
  s2 <- showAnnTermJson e2
  return [ object [ "text"  .= ("let " ++ show x ++ " =")
                  , "nodes" .= s1 ]
         , object [ "text"  .= ("in" :: String)
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= s2 ] ]
showAnnTermJson (Term_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTermJson e1
  s2 <- showAnnTermJson e2
  return [ object [ "text"  .= ("let " ++ show x ++ " :: " ++ showWithGreek p ++ " =")
                  , "nodes" .= s1 ]
         , object [ "text"  .= ("in" :: String)
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= s2 ] ]
showAnnTermJson (Term_Match e c bs t) = do
  e'  <- showAnnTermJson e
  bs' <- mapM (\(d,b,_) -> do (xs,es) <- unbind b
                              es' <- showAnnTermJson es
                              return $ object [ "text"  .= ("| " ++ intercalate " " (map show (d:xs)) ++ " →")
                                              , "nodes" .= es']) bs
  return [ object [ "text"  .= ("match" :: String)
                  , "nodes" .= e' ]
         , object [ "text"  .= ("with '" ++ c)
                  , "tags"  .= [showWithGreek t]
                  , "nodes" .= bs' ] ]

showJsonConstraints :: [(Either (RawTermVar,String) (TyTermVar,Gathered,[TyVar]), Graph, Bool)] -> [Value]
showJsonConstraints [] = []
showJsonConstraints ((Left (n,e),_,_):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [withGreek e]
                    , "color" .= ("white" :: String)
                    , "backColor" .= ("#F58471" :: String) ] -- red
   in this : showJsonConstraints xs
showJsonConstraints ((Right (n, Gathered t a g w, _),_,_):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [showWithGreek t]
                    , "color" .= ("white" :: String)
                    , "backColor" .= ("#95D6E9" :: String) -- blue
                    , "nodes" .= [ object [ "text"  .= ("annotated ast" :: String)
                                          , "nodes" .= runFreshM (showAnnTermJson a) ]
                                 , object [ "text"  .= ("given" :: String)
                                          , "nodes" .= runFreshM (showJsonConstraintList g) ]
                                 , object [ "text"  .= ("wanted" :: String)
                                          , "nodes" .= runFreshM (showJsonConstraintList w) ] ] ]
   in this : showJsonConstraints xs

showJsonConstraintList :: [Constraint] -> FreshM [Value]
showJsonConstraintList = mapM showJsonConstraint

showJsonConstraint :: Constraint -> FreshM Value
showJsonConstraint (Constraint_Unify t1 t2) =
  return $ object [ "text" .= (showWithGreek t1 ++ " ~ " ++ showWithGreek t2 :: String) ]
showJsonConstraint (Constraint_Inst t1 t2) =
  return $ object [ "text" .= (showWithGreek t1 ++ " > " ++ showWithGreek t2 :: String) ]
showJsonConstraint (Constraint_Equal t1 t2) =
  return $ object [ "text" .= (showWithGreek t1 ++ " = " ++ showWithGreek t2 :: String) ]
showJsonConstraint (Constraint_Class c ts) =
  return $ object [ "text" .= ("$" ++ c ++ " " ++ intercalate " " (map (doParens . showWithGreek) ts) :: String) ]
showJsonConstraint (Constraint_Exists b) = do
  (v, (g,w)) <- unbind b
  oG <- showJsonConstraintList g
  oW <- showJsonConstraintList w
  return $ object [ "text"  .= ("∃" ++ showWithGreek v :: String)
                  , "nodes" .= [ object [ "text"  .= ("assume" :: String)
                                        , "nodes" .= oG ]
                               , object [ "text"  .= ("implies" :: String)
                                        , "nodes" .= oW ] ] ]
showJsonConstraint (Constraint_Inconsistent) =
  return $ object [ "text" .= ("⊥" :: String) ]

showJsonGraph :: Graph -> [Constraint] -> Value
showJsonGraph g blamed =
  object [ "nodes" .= map (\(x,(_,b,_)) -> object [ "text" .= showWithGreek x
                                                  , "deleted" .= b
                                                  , "blamed"  .= (x `elem` blamed) ])
                          (vertices g)
         , "links" .= map (\(src,tgt,tag) -> object [ "source" .= src
                                                    , "target" .= tgt
                                                    , "value"  .= tag])
                          (edges g) ]
