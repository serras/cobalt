{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Main where

import Control.Lens hiding ((.=), Empty)
import Data.Aeson hiding (json, Error)
import Data.HashMap.Strict (insert)
import Data.List (intercalate)
import Data.Foldable (toList)
import System.Console.ANSI
import System.Environment
import Text.Parsec (parse)
import Text.Parsec.String
import Unbound.LocallyNameless hiding (toList, close)
import Web.Scotty

import Cobalt.Core
import Cobalt.Language
import Cobalt.U
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
  p <- parseFromFile parseFile fname
  let scheme  = if "flat" `elem` rest then TreeScheme else FlatScheme
      systemf = if "systemf" `elem` rest then UseOnlySystemFTypes else UseAnyType
  case p of
    Left ep -> do setSGR [SetColor Foreground Vivid Red]
                  putStr "Error while parsing: "
                  setSGR [Reset]
                  print ep
    Right (env, defns) ->
      let env' =  env & dataE %~ (++ initialDataEnv)
       in case todo of
            "parse"   -> do print env
                            putStrLn ""
                            mapM_ print defns
            "solve"   -> solveDefns  scheme systemf env' defns
            "gather"  -> gatherDefns scheme systemf env' defns
            _ -> putStrLn "Unrecognized command"

mainServe :: IO ()
mainServe = do
  _:port:_ <- getArgs
  scotty (read port) $ do
    get "/" $ do
      setHeader "Content-Type" "text/html; charset=utf-8"
      file "static/editor.html"
    post "/typecheck" $ do
      -- Get parameters
      (scheme :: String) <- param "scheme"
      let gs = if scheme == "flat" then FlatScheme else TreeScheme
      (systemf :: String) <- param "systemf"
      let sf = if systemf == "only" then UseOnlySystemFTypes else UseAnyType
      (printsystemf :: String) <- param "printsystemf"
      let psf = if printsystemf == "yes" then True else False
      -- Parse and typecheck
      code <- param "code"
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) ->
         let env' = env & dataE %~ (++ initialDataEnv)
          in case checkEnv env' of
              Left rulesErr -> json $ object [ "status"  .= ("error" :: String)
                                             , "message" .= intercalate "\n\n" rulesErr ]
              Right _ -> let tcs  = tcDefns gs sf env' defns
                             vals = zipWith (jsonTypechecked code psf) defns tcs
                          in json $ object [ "status" .= ("ok" :: String)
                                           , "values" .= vals ]
    post "/gather" $ do
      -- Get parameters
      (scheme :: String) <- param "scheme"
      let gs = if scheme == "flat" then FlatScheme else TreeScheme
      (systemf :: String) <- param "systemf"
      let sf = if systemf == "only" then UseOnlySystemFTypes else UseAnyType
      -- Parse code and gather constraints
      code <- param "code"
      case parse parseFile "code" code of
       Left ep -> json $ object [ "status"  .= ("error" :: String)
                                , "message" .= show ep ]
       Right (env, defns) ->
         let env' = env & dataE %~ (++ initialDataEnv)
          in case checkEnv env' of
              Left rulesErr -> json $ object [ "status"  .= ("error" :: String)
                                             , "message" .= intercalate "\n\n" rulesErr ]
              Right _ -> let gath = gDefns gs sf env' defns
                             vals = zipWith jsonScript defns gath
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

-- COMMAND LINE PART

gatherDefns :: GatheringScheme -> SystemFScheme -> Env -> [(RawDefn,Bool)] -> IO ()
gatherDefns gs fs env defns = do
  let gaths = gDefns gs fs env defns
  mapM_ showGathered (zip defns gaths)

solveDefns :: GatheringScheme -> SystemFScheme -> Env -> [(RawDefn,Bool)] -> IO ()
solveDefns gs fs env defns = do
  let sols = tcDefns gs fs env defns
  mapM_ showSolved (zip defns sols)

showGathered :: ( (RawDefn,Bool)
                , ( Either Errors ([Constraint], [a], GatherTermInfo)
                  , AnnUTerm TyVar, [TyVar], [Constraint] ) )
             -> IO ()
showGathered (((n,_,_),_), (Left errors, _, _, _)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [SetColor Foreground Vivid Red]
  putStrLn "error"
  setSGR [Reset]
  mapM_ putStrLn errors
  putStrLn ""
showGathered (((n,_,_),_), (Right (_, _, GatherTermInfo w _ _), _, _, _)) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStrLn (name2String n)
  setSGR [Reset]
  print w
  putStrLn ""

showSolved :: Show a => ((RawDefn,Bool), a) -> IO ()
showSolved (((n,_,_),_), sol) = do
  setSGR [SetColor Foreground Vivid Blue]
  putStr (name2String n)
  setSGR [Reset]
  putStr " ==> "
  setSGR [Reset]
  print sol
  putStrLn ""

-- JSON PART
jsonScript :: (RawDefn,Bool)
           -> ( Either Errors ([Constraint], [a], GatherTermInfo)
              , AnnUTerm TyVar, [TyVar], [Constraint] )
           -> Value
jsonScript ((n,_,_),_) (Left e, _, _, _) =
  object [ "text" .= name2String n
         -- , "tags" .= [withGreek e]
         , "nodes" .= map justText e
         , "color" .= ("white" :: String)
         , "backColor" .= ("#F58471" :: String) ] -- red
jsonScript ((n,_,_),_) (Right (g, _, GatherTermInfo w _ _), term, _, extra) =
  object [ "text" .= name2String n
         -- , "tags" .= [showWithGreek t]
         , "color" .= ("white" :: String)
         , "backColor" .= ("#95D6E9" :: String) -- blue
         , "nodes" .= [ object [ "text"  .= ("annotated ast" :: String)
                               , "nodes" .= showAnnTermJson False [] term ]
                      , object [ "text"  .= ("given" :: String)
                               , "nodes" .= map (justText . textJsonConstraint) g ]
                      , object [ "text"  .= ("wanted" :: String)
                               , "nodes" .= [ showJsonScript w ] ]
                      , object [ "text"  .= ("extra" :: String)
                               , "nodes" .= map (justText . textJsonConstraint) extra ] ] ]

jsonTypechecked :: String -> Bool -> (RawDefn,Bool) -> (FinalSolution, AnnUTerm MonoType, Maybe PolyType) -> Value
jsonTypechecked sourceCode printSystemF ((n,_,_),ok) ((Solution _ rs _ _, errs, graph), term, p) =
  let errNodes = if null errs
                    then []
                    else [ object [ "text"  .= ("errors" :: String)
                                  , "nodes" .= map ( justText . toHtmlString . withGreek
                                                   . showErrorExplanation sourceCode
                                                   . simplifyErrorExplanation ) errs ] ]
      resNodes = if null rs
                    then []
                    else [ object [ "text"  .= ("residual" :: String)
                                  , "nodes" .= map (justText . textJsonConstraint) rs ] ]
      color = if null errs
                 then if ok then "#85C99E" else "#F58471"
                 else if ok then "#F58471" else "#F1B75B"
   in object [ "text" .= name2String n
             , "tags" .= case p of
                           Just t -> [showAsJsonTag printSystemF rs t]
                           Nothing -> []
             , "color" .= ("white" :: String)
             , "backColor" .= (color :: String)
             , "nodes" .= (errNodes ++ showAnnTermJson printSystemF rs term ++ resNodes)
             , "graph" .= showJsonGraph graph ]

showJsonScript :: TyScript -> Value
showJsonScript Empty =
  object [ "text" .= ("∅" :: String) ]
showJsonScript (Label i s) =
  let Object inner = showJsonScript s
   in Object (insert "tags" (toJSON [i]) inner)
showJsonScript (Singleton (Constraint_Later s l) p i) =  -- Special case for later
  object [ "text"  .= ("later" :: String)
         , "tags"  .= toList s
         , "nodes" .= map (showJsonScript . (\n -> Singleton n p i)) l ]
showJsonScript (Singleton (Constraint_Cond c t e) p i) =  -- Special case for cond
  object [ "text"  .= ("cond" :: String)
         , "tags"  .= toList i
         , "nodes" .= [ object [ "text"  .= ("condition" :: String)
                               , "nodes" .= map (showJsonScript . (\n -> Singleton n p i)) c ]
                      , object [ "text"  .= ("then" :: String)
                               , "nodes" .= map (showJsonScript . (\n -> Singleton n p i)) t ]
                      , object [ "text"  .= ("else" :: String)
                               , "nodes" .= map (showJsonScript . (\n -> Singleton n p i)) e ] ] ]
showJsonScript (Singleton c _ i) =
  object [ "text" .= textJsonConstraint c
         , "tags" .= toList i ]
showJsonScript (Join lst _) =
  object [ "text"  .= ("merge" :: String)
         , "nodes" .= map showJsonScript lst ]
showJsonScript (AsymJoin e1 e2 _) =
  object [ "text"  .= ("asymjoin" :: String)
         , "nodes" .= map showJsonScript [e1, e2] ]
showJsonScript (Sequence e1 e2 _) =
  object [ "text"  .= ("sequence" :: String)
         , "nodes" .= map showJsonScript [e1, e2] ]
showJsonScript (Exists v q w _) =
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
textJsonConstraint (Constraint_FType v)     = "ftype[" ++ show v ++ "]"
textJsonConstraint (Constraint_Later s l)   = "later \"" ++ s ++ "\" [" ++ intercalate ", " (map textJsonConstraint l) ++ "]"
textJsonConstraint (Constraint_Cond c t e)  = "cond [" ++ intercalate ", " (map textJsonConstraint c)
                                              ++ "] [" ++ intercalate ", " (map textJsonConstraint t)
                                              ++ "] [" ++ intercalate ", " (map textJsonConstraint e) ++ "]"

showAnnTermJson :: ShowAsJsonTag t => Bool -> [Constraint] -> AnnUTerm t -> [Value]
showAnnTermJson psf rs (UTerm_IntLiteral n (_,t)) =
  [ object [ "text"  .= show n
           , "tags"  .= [showAsJsonTag psf rs t] ] ]
showAnnTermJson psf rs (UTerm_StrLiteral n (_,t)) =
  [ object [ "text"  .= show n
           , "tags"  .= [showAsJsonTag psf rs t] ] ]
showAnnTermJson psf rs (UTerm_Var v (_,t)) =
  [ object [ "text"  .= show v
           , "tags"  .= [showAsJsonTag psf rs t] ] ]
showAnnTermJson psf rs (UTerm_Abs x _ e (_,t)) =
  [ object [ "text"  .= ("λ " ++ show x ++ " →")
           , "tags"  .= [showAsJsonTag psf rs t]
           , "nodes" .= showAnnTermJson psf rs e ] ]
showAnnTermJson psf rs (UTerm_AbsAnn x _ e (p,_) (_,t)) =
  [ object [ "text"  .= ("λ (" ++ show x ++ " :: " ++ showWithGreek p ++ ") →")
           , "tags"  .= [showAsJsonTag psf rs t]
           , "nodes" .= showAnnTermJson psf rs e ] ]
showAnnTermJson psf rs (UTerm_App a b (_,t)) =
  [ object [ "text"  .= ("@" :: String)
           , "tags"  .= [showAsJsonTag psf rs t]
           , "nodes" .= (showAnnTermJson psf rs a ++ showAnnTermJson psf rs b) ] ]
showAnnTermJson psf rs (UTerm_Let x e1 e2 (_,t)) =
  [ object [ "text"  .= ("let " ++ show x ++ " =")
           , "nodes" .= showAnnTermJson psf rs e1 ]
  , object [ "text"  .= ("in" :: String)
           , "tags"  .= [showAsJsonTag psf rs t]
           , "nodes" .= showAnnTermJson psf rs e2 ] ]
showAnnTermJson psf rs (UTerm_LetAnn x e1 e2 (p,_) (_,t)) =
  [ object [ "text"  .= ("let " ++ show x ++ " :: " ++ showWithGreek p ++ " =")
           , "nodes" .= showAnnTermJson psf rs e1 ]
  , object [ "text"  .= ("in" :: String)
           , "tags"  .= [showAsJsonTag psf rs t]
           , "nodes" .= showAnnTermJson psf rs e2 ] ]
showAnnTermJson psf rs (UTerm_Match e c _k bs (_,t)) =
  let bs' = map (\(UCaseAlternative d xs _casep es _) ->
                    object [ "text"  .= ("| " ++ intercalate " " (map show (d:xs)) ++ " →")
                           -- , "tags"  .= case casep of
                           --                Nothing -> ["?" :: String]
                           --                Just (_,(cpq,cpw,cpv)) -> [showWithGreek cpv ++ " "
                           --                                           ++ showWithGreek cpq ++ " "
                           --                                           ++ showWithGreek cpw]
                           , "nodes" .= showAnnTermJson psf rs es]) bs
   in [ object [ "text"  .= ("match" :: String)
               -- , "tags"  .= case k of
               --                Nothing -> ["?" :: String]
               --                Just ty -> [showWithGreek ty]
               , "nodes" .= showAnnTermJson psf rs e]
      , object [ "text"  .= ("with '" ++ c)
               , "tags"  .= [showAsJsonTag psf rs t]
               , "nodes" .= bs' ] ]
showAnnTermJson _ _ _ = error "This should never happen"

class ShowAsJsonTag x where
  showAsJsonTag :: Bool -> [Constraint] -> x -> String

instance ShowAsJsonTag TyVar where
  showAsJsonTag _ _ = showWithGreek

instance ShowAsJsonTag MonoType where
  showAsJsonTag True  cs m = withGreek $ showPolyTypeAsSystemF $ fst (close cs m)
  showAsJsonTag False cs m = showWithGreek $ fst (close cs m)

instance ShowAsJsonTag PolyType where
  showAsJsonTag True  _ = withGreek . showPolyTypeAsSystemF
  showAsJsonTag False _ = showWithGreek

showJsonGraph :: Graph -> Value
showJsonGraph g =
  object [ "nodes" .= map (\(x,(_,b,cm)) -> object [ "text" .= let comment = if null cm then "" else " " ++ show cm
                                                                in (showWithGreek x ++ comment :: String)
                                                   , "deleted" .= b ])
                          (vertices g)
         , "links" .= map (\(src,tgt,tag) -> object [ "source" .= src
                                                    , "target" .= tgt
                                                    , "value"  .= tag])
                          (edges g) ]
