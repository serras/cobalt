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
import Unbound.LocallyNameless hiding (close)
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
                 []          -> UseAnyType
                 "systemf":_ -> UseSystemFTypes
                 _           -> UseAnyType
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
      (systemf :: String) <- param "systemf"
      let sf = if systemf == "only" then UseSystemFTypes else UseAnyType
      (printsystemf :: String) <- param "printsystemf"
      let psf = if printsystemf == "yes" then True else False
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) -> let env' = env & dataE %~ (++ initialDataEnv)
                                 vals = showJsonAnns psf (tcDefns sf env' defns)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    post "/gather" $ do
      code <- param "code"
      (systemf :: String) <- param "systemf"
      let sf = if systemf == "only" then UseSystemFTypes else UseAnyType
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) -> let env' = env & dataE %~ (++ initialDataEnv)
                                 vals = showJsonConstraints (gDefns sf env' defns)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    get "/example/:folder/:file" $ do
      dirname <- param "folder"
      fname   <- param "file"
      file $ "test/" ++ dirname ++ "/" ++ fname
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

showJsonAnns :: Show err => Bool -> [(Either (RawTermVar,err) (TyDefn,[Constraint]), Graph, Bool)] -> [Value]
showJsonAnns _ [] = []
showJsonAnns systemf ((Left (n,e),gr,b):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [showWithGreek e]
                    , "color" .= ("white" :: String)
                    , "backColor" .= if b then ("#F58471" :: String)  -- red
                                          else ("#F1B75B" :: String)  -- yellow
                    , "graph" .= showJsonGraph gr (map fst $ blameConstraints gr Constraint_Inconsistent) ]
   in this : showJsonAnns systemf xs
showJsonAnns systemf ((Right ((n,t,p),cs),gr,b):xs) =
  let this = object [ "text" .= name2String n
                    , "tags" .= [if systemf then withGreek (showPolyTypeAsSystemF p) else showWithGreek p]
                    , "color" .= ("white" :: String)
                    , "backColor" .= if b then ("#85C99E" :: String)  -- green
                                          else ("#F58471" :: String)  -- red
                    , "nodes" .= runFreshM (showAnnTermJson systemf t cs)
                    , "graph" .= showJsonGraph gr [] ]
   in this : showJsonAnns systemf xs

showAnnTermJson :: Fresh m => Bool -> TyTerm -> [Constraint] -> m [Value]
showAnnTermJson systemf (Term_IntLiteral n t) cs =
  return [ object [ "text"  .= show n
                  , "tags"  .= [closeAndShowWithGreek systemf cs t] ] ]
showAnnTermJson systemf (Term_StrLiteral n t) cs =
  return [ object [ "text"  .= show n
                  , "tags"  .= [closeAndShowWithGreek systemf cs t] ] ]
showAnnTermJson systemf (Term_Var v t) cs =
  return [ object [ "text"  .= show v
                  , "tags"  .= [closeAndShowWithGreek systemf cs t] ] ]
showAnnTermJson systemf (Term_Abs b _ t) cs = do
  (x,e) <- unbind b
  inner <- showAnnTermJson systemf e cs
  return [ object [ "text"  .= ("λ " ++ show x ++ " →")
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= inner ] ]
showAnnTermJson systemf (Term_AbsAnn b _ p t) cs = do
  (x,e) <- unbind b
  inner <- showAnnTermJson systemf e cs
  return [ object [ "text"  .= ("λ (" ++ show x ++ " :: " ++ showWithGreek p ++ ") →")
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= inner ] ]
showAnnTermJson systemf (Term_App a b t) cs = do
  e1 <- showAnnTermJson systemf a cs
  e2 <- showAnnTermJson systemf b cs
  return [ object [ "text"  .= ("@" :: String)
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= (e1 ++ e2) ] ]
showAnnTermJson systemf (Term_Let b t) cs = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTermJson systemf e1 cs
  s2 <- showAnnTermJson systemf e2 cs
  return [ object [ "text"  .= ("let " ++ show x ++ " =")
                  , "nodes" .= s1 ]
         , object [ "text"  .= ("in" :: String)
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= s2 ] ]
showAnnTermJson systemf (Term_LetAnn b p t) cs = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTermJson systemf e1 cs
  s2 <- showAnnTermJson systemf e2 cs
  return [ object [ "text"  .= ("let " ++ show x ++ " :: " ++ showWithGreek p ++ " =")
                  , "nodes" .= s1 ]
         , object [ "text"  .= ("in" :: String)
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= s2 ] ]
showAnnTermJson systemf (Term_Match e c bs t) cs = do
  e'  <- showAnnTermJson systemf e cs
  bs' <- mapM (\(d,b,_) -> do (xs,es) <- unbind b
                              es' <- showAnnTermJson systemf es cs
                              return $ object [ "text"  .= ("| " ++ intercalate " " (map show (d:xs)) ++ " →")
                                              , "nodes" .= es']) bs
  return [ object [ "text"  .= ("match" :: String)
                  , "nodes" .= e' ]
         , object [ "text"  .= ("with '" ++ c)
                  , "tags"  .= [closeAndShowWithGreek systemf cs t]
                  , "nodes" .= bs' ] ]

closeAndShowWithGreek :: Bool -> [Constraint] -> MonoType -> String
closeAndShowWithGreek True  cs m = withGreek $ showPolyTypeAsSystemF $ fst (close cs m)
closeAndShowWithGreek False cs m = showWithGreek $ fst (close cs m)

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
                                          , "nodes" .= runFreshM (showAnnTermJson False a []) ]
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
showJsonConstraint Constraint_Inconsistent =
  return $ object [ "text" .= ("⊥" :: String) ]
showJsonConstraint (Constraint_FType v) =
  return $ object [ "text" .= ("ftype[" ++ show v ++ "]" :: String) ]
showJsonConstraint (Constraint_Later s l) = do
  oL <- showJsonConstraintList l
  return $ object [ "text"  .= ("later \"" ++ s ++ "\"" :: String)
                  , "nodes" .= oL ]
showJsonConstraint (Constraint_Cond c t e) = do
  cT <- showJsonConstraintList c
  tT <- showJsonConstraintList t
  eT <- showJsonConstraintList e
  return $ object [ "text"  .= ("cond" :: String)
                  , "nodes" .= [ object [ "text"  .= ("condition" :: String)
                                        , "nodes" .= cT ]
                               , object [ "text"  .= ("then" :: String)
                                        , "nodes" .= tT ]
                               , object [ "text"  .= ("else" :: String)
                                        , "nodes" .= eT ] ] ]

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
