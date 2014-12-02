{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
module Main where

import Control.Lens hiding ((.=))
import Data.Aeson hiding (json, Error)
import Data.List (intercalate)
import Data.Foldable (toList)
import System.Console.ANSI
import System.Environment
import Text.Parsec (parse)
import Text.Parsec.String
import Unbound.LocallyNameless hiding (toList)
import Web.Scotty

import Cobalt.Language.Parser (parseFile)
import Cobalt.Language.Syntax
import Cobalt.Script.Gather
import Cobalt.Script.Script
import Cobalt.Script.Solver
import Cobalt.Script.Syntax
import Cobalt.Script.Top
import Cobalt.Types
import Cobalt.Util (showWithGreek, doParens)

main :: IO ()
main = do
  todo:_ <- getArgs
  case todo of
   "serve" -> mainServe
   _       -> mainCmd

mainCmd :: IO ()
mainCmd = do
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
            "gather" -> gatherDefns env' defns
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
                                 tcs  = tcDefns  env' defns
                                 vals = map jsonTypechecked (zip defns tcs)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    post "/gather" $ do
      code <- param "code"
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) -> let env' = env & dataE %~ (++ initialDataEnv)
                                 gath = gDefns env' defns
                                 vals = map jsonScript (zip defns gath)
                              in json $ object [ "status" .= ("ok" :: String)
                                               , "values" .= vals ]
    get "/example/:file" $ do
      fname <- param "file"
      file $ "test/" ++ fname
    get "/:file" $ do
      fname <- param "file"
      file $ "static/" ++ fname

-- COMMAND LINE PART

gatherDefns :: Env -> [(RawDefn,Bool)] -> IO ()
gatherDefns env defns = do
  let gaths = gDefns env defns
  mapM_ showGathered (zip defns gaths)

solveDefns :: Env -> [(RawDefn,Bool)] -> IO ()
solveDefns env defns = do
  let sols = tcDefns env defns
  mapM_ showSolved (zip defns sols)

showGathered :: ((RawDefn,Bool), (Gathered, AnnUTerm TyVar)) -> IO ()
showGathered (((n,_,_),_), (Error errors, _)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "error"
  setSGR [Reset]
  mapM_ putStrLn errors
  putStrLn ""
showGathered (((n,_,_),_), (GatherTerm _ [w] _, _)) = do
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

-- JSON PART
jsonScript :: ((RawDefn,Bool), (Gathered, AnnUTerm TyVar)) -> Value
jsonScript (((n,_,_),_), (Error e, _)) = 
  object [ "text" .= name2String n
         -- , "tags" .= [withGreek e]
         , "nodes" .= map justText e
         , "color" .= ("white" :: String)
         , "backColor" .= ("#F58471" :: String) ] -- red
jsonScript (((n,_,_),_), (GatherTerm g w _, term)) =
  object [ "text" .= name2String n
         -- , "tags" .= [showWithGreek t]
         , "color" .= ("white" :: String)
         , "backColor" .= ("#95D6E9" :: String) -- blue
         , "nodes" .= [ object [ "text"  .= ("annotated ast" :: String)
                               , "nodes" .= showAnnTermJson term ]
                      , object [ "text"  .= ("given" :: String)
                               , "nodes" .= map (justText . textJsonConstraint) g ]
                      , object [ "text"  .= ("wanted" :: String)
                               , "nodes" .= map showJsonScript w ] ] ]

jsonTypechecked :: ((RawDefn,Bool), (ScriptSolution, [(TyVar, MonoType)], AnnUTerm MonoType)) -> Value
jsonTypechecked (((n,_,_),ok), (((_,rs,_), errs, _graph), _, term)) =
  let errNodes = if null errs
                    then []
                    else [ object [ "text"  .= ("errors" :: String)
                                  , "nodes" .= map justText errs ] ]
      resNodes = if null rs
                    then []
                    else [ object [ "text"  .= ("residual" :: String)
                                  , "nodes" .= map (justText . textJsonConstraint) rs ] ]
      color = if null errs
                 then if ok then "#85C99E" else "#F58471"
                 else if ok then "#F58471" else "#F1B75B"
   in object [ "text" .= name2String n
             -- , "tags" .= [showWithGreek t]
             , "color" .= ("white" :: String)
             , "backColor" .= (color :: String)
             , "nodes" .= (errNodes ++ showAnnTermJson term ++ resNodes) ]

showJsonScript :: TyScript -> Value
showJsonScript Empty =
  object [ "text" .= ("∅" :: String) ]
showJsonScript (Singleton c (_,t)) =
  object [ "text" .= textJsonConstraint c
         , "tags" .= toList t ]
showJsonScript (Merge lst (_,t)) =
  object [ "text"  .= ("merge" :: String)
         , "tags"  .= toList t
         , "nodes" .= map showJsonScript lst ]
showJsonScript (Asym e1 e2 (_,t)) =
  object [ "text"  .= ("asym" :: String)
         , "tags"  .= toList t
         , "nodes" .= map showJsonScript [e1, e2] ]
showJsonScript (Exists v q w) =
  object [ "text"  .= ("∃" ++ showWithGreek v :: String)
         , "nodes" .= [ object [ "text"  .= ("assume" :: String)
                               , "nodes" .= map (justText . textJsonConstraint) q ]
                      , object [ "text"  .= ("implies" :: String)
                               , "nodes" .= [ showJsonScript w ] ] ] ]

justText :: String -> Value
justText s = object [ "text" .= s ]

textJsonConstraint :: Constraint -> String
textJsonConstraint (Constraint_Unify t1 t2) = showWithGreek t1 ++ " ~ " ++ showWithGreek t2
textJsonConstraint (Constraint_Inst  t1 t2) = showWithGreek t1 ++ " > " ++ showWithGreek t2
textJsonConstraint (Constraint_Equal t1 t2) = showWithGreek t1 ++ " = " ++ showWithGreek t2
textJsonConstraint (Constraint_Class c  ts) = "$" ++ c ++ " " ++ intercalate " " (map (doParens . showWithGreek) ts)
textJsonConstraint (Constraint_Exists _)    = error "This should never happen"
textJsonConstraint Constraint_Inconsistent  = "⊥"


showAnnTermJson :: Show t => AnnUTerm t -> [Value]
showAnnTermJson (UTerm_IntLiteral n (_,t)) =
  [ object [ "text"  .= show n
           , "tags"  .= [showWithGreek t] ] ]
showAnnTermJson (UTerm_Var v (_,t)) =
  [ object [ "text"  .= show v
           , "tags"  .= [showWithGreek t] ] ]
showAnnTermJson (UTerm_Abs x _ e (_,t)) =
  [ object [ "text"  .= ("λ " ++ show x ++ " →")
           , "tags"  .= [showWithGreek t]
           , "nodes" .= showAnnTermJson e ] ]
showAnnTermJson (UTerm_AbsAnn x _ e p (_,t)) =
  [ object [ "text"  .= ("λ (" ++ show x ++ " :: " ++ showWithGreek p ++ ") →")
           , "tags"  .= [showWithGreek t]
           , "nodes" .= showAnnTermJson e ] ]
showAnnTermJson (UTerm_App a b (_,t)) =
  [ object [ "text"  .= ("@" :: String)
           , "tags"  .= [showWithGreek t]
           , "nodes" .= (showAnnTermJson a ++ showAnnTermJson b) ] ]
showAnnTermJson (UTerm_Let x e1 e2 (_,t)) =
  [ object [ "text"  .= ("let " ++ show x ++ " =")
           , "nodes" .= showAnnTermJson e1 ]
  , object [ "text"  .= ("in" :: String)
           , "tags"  .= [showWithGreek t]
           , "nodes" .= showAnnTermJson e2 ] ]
showAnnTermJson (UTerm_LetAnn x e1 e2 p (_,t)) =
  [ object [ "text"  .= ("let " ++ show x ++ " :: " ++ showWithGreek p ++ " =")
           , "nodes" .= showAnnTermJson e1 ]
  , object [ "text"  .= ("in" :: String)
           , "tags"  .= [showWithGreek t]
           , "nodes" .= showAnnTermJson e2 ] ]
showAnnTermJson (UTerm_Match e c bs (_,t)) =
  let bs' = map (\(UCaseAlternative d xs _ es _) ->
                    object [ "text"  .= ("| " ++ intercalate " " (map show (d:xs)) ++ " →")
                           , "nodes" .= showAnnTermJson es]) bs
   in [ object [ "text"  .= ("match" :: String)
               , "nodes" .= showAnnTermJson e ]
      , object [ "text"  .= ("with '" ++ c)
               , "tags"  .= [showWithGreek t]
               , "nodes" .= bs' ] ]
showAnnTermJson _ = error "This should never happen"
