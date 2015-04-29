{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Cobalt.Language.Syntax (
  -- * Terms
  RawTermVar
, RawTerm
, TyTermVar
, TyTerm
  -- ** Generic annotated terms
, TermVar
, Term(..)
, atAnn
, getAnn
  -- * Rules
, Rule(..)
, RuleStrictness(..)
, RuleBody
, RuleRegexVar
, RuleRegex(..)
, RuleCheck
, RuleScript
, RuleScriptInstr(..)
, RuleScriptOrdering(..)
, RuleScriptMessage(..)
  -- * Whole program structure
  -- ** Environment
, FnEnv
, DataEnv
, initialDataEnv
, AxiomEnv
, RuleEnv
, Env(Env)
, fnE
, dataE
, axiomE
, ruleE
  -- ** Definitions
, RawDefn
, TyDefn
) where

import Control.Lens hiding ((.=), from, to)
import Data.List (intercalate, union)
import Data.Monoid
import Text.Parsec.Pos
import Unbound.LocallyNameless hiding (close, union)

import Cobalt.Core
{-# ANN module ("HLint: ignore Use camelCase"::String) #-}

type RawTermVar = TermVar (SourcePos, SourcePos)
type RawTerm    = Term (SourcePos, SourcePos)
type TyTermVar  = TermVar MonoType
type TyTerm     = Term MonoType

type TermVar t = Name (Term t)
data Term t = Term_IntLiteral Integer t
            | Term_Var    (TermVar t) t
            | Term_Abs    (Bind (TermVar t) (Term t)) t t
            | Term_AbsAnn (Bind (TermVar t) (Term t)) t PolyType t
            | Term_App    (Term t) (Term t) t
            | Term_Let    (Bind (TermVar t, Embed (Term t)) (Term t)) t
            | Term_LetAnn (Bind (TermVar t, Embed (Term t)) (Term t)) PolyType t
            | Term_Match  (Term t) String [(TermVar t, Bind [TermVar t] (Term t), t)] t
            | Term_StrLiteral String t

atAnn :: (Alpha a, Alpha b) => (a -> b) -> Term a -> Term b
atAnn f = runFreshM . atAnn' f

atAnn' :: (Fresh m, Alpha a, Alpha b) => (a -> b) -> Term a -> m (Term b)
atAnn' f (Term_IntLiteral n t) = return $ Term_IntLiteral n (f t)
atAnn' f (Term_Var v t) = return $ Term_Var (translate v) (f t)
atAnn' f (Term_Abs b bt t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ Term_Abs (bind (translate x) inner) (f bt) (f t)
atAnn' f (Term_AbsAnn b bt p t) = do
  (x,e) <- unbind b
  inner <- atAnn' f e
  return $ Term_AbsAnn (bind (translate x) inner) (f bt) p (f t)
atAnn' f (Term_App a b t) = do
  e1 <- atAnn' f a
  e2 <- atAnn' f b
  return $ Term_App e1 e2 (f t)
atAnn' f (Term_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ Term_Let (bind (translate x, embed s1) s2) (f t)
atAnn' f (Term_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- atAnn' f e1
  s2 <- atAnn' f e2
  return $ Term_LetAnn (bind (translate x, embed s1) s2) p (f t)
atAnn' f (Term_Match e c bs t) = do
  e' <- atAnn' f e
  b' <- mapM (\(d,b,ann) -> do (xs,expr) <- unbind b
                               expr' <- atAnn' f expr
                               return (translate d, bind (map translate xs) expr', f ann)) bs
  return $ Term_Match e' c b' (f t)
atAnn' f (Term_StrLiteral n t) = return $ Term_StrLiteral n (f t)

getAnn :: Term t -> t
getAnn (Term_IntLiteral _ t) = t
getAnn (Term_Var _ t)        = t
getAnn (Term_Abs _ _ t)      = t
getAnn (Term_AbsAnn _ _ _ t) = t
getAnn (Term_App _ _ t)      = t
getAnn (Term_Let _ t)        = t
getAnn (Term_LetAnn _ _ t)   = t
getAnn (Term_Match _ _ _ t)  = t
getAnn (Term_StrLiteral _ t) = t

data Rule = Rule RuleStrictness String RuleBody deriving Show
type RuleBody = Bind (TyVar,[TyVar]) (RuleRegex, RuleCheck, RuleScript)
data RuleStrictness = RuleStrictness_NonStrict | RuleStrictness_Strict | RuleStrictness_Unsafe deriving Show

type RuleRegexVar = Name RuleRegex
data RuleRegex = RuleRegex_Square  RuleRegexVar
               | RuleRegex_Iter    (Bind RuleRegexVar RuleRegex)
               | RuleRegex_Any
               | RuleRegex_Choice  RuleRegex RuleRegex
               | RuleRegex_App     RuleRegex RuleRegex
               | RuleRegex_Var     RawTermVar
               | RuleRegex_Int     Integer
               | RuleRegex_Str     String
               | RuleRegex_Capture TyVar (Maybe RuleRegex)
               deriving Show

type RuleCheck = [Constraint]

type RuleScript = Bind [TyVar] [(RuleScriptInstr, Maybe RuleScriptMessage)]
data RuleScriptInstr = RuleScriptInstr_Empty
                     | RuleScriptInstr_Ref TyVar
                     | RuleScriptInstr_Constraint Constraint (Maybe RuleScriptMessage)
                     | RuleScriptInstr_Ordered  RuleScript
                     | RuleScriptInstr_Sequence RuleScript
                     | RuleScriptInstr_Join     RuleScript
                     | RuleScriptInstr_Match    TyVar [RuleBody]
                     | RuleScriptInstr_ForEach  [(TyVar, RuleScriptOrdering)] (Bind TyVar RuleScript)
                     | RuleScriptInstr_Rec      (Maybe MonoType) TyVar (Bind TyVar RuleScript)
                     | RuleScriptInstr_Call     (Maybe MonoType) TyVar
                     | RuleScriptInstr_Return   MonoType
                     deriving Show

data RuleScriptOrdering = RuleScriptOrdering_OutToIn
                        | RuleScriptOrdering_InToOut
                        deriving Show

data RuleScriptMessage = RuleScriptMessage_Literal    String
                       -- | RuleScriptMessage_Type       TyVar
                       -- | RuleScriptMessage_Expression TyVar
                       -- | RuleScriptMessage_VConcat    TyVar (Bind TyVar RuleScriptMessage) RuleScriptMessage
                       -- | RuleScriptMessage_HConcat    TyVar (Bind TyVar RuleScriptMessage)
                       -- | RuleScriptMessage_Vertical   RuleScriptMessage RuleScriptMessage
                       -- | RuleScriptMessage_Horizontal RuleScriptMessage RuleScriptMessage
                       deriving Show

type FnEnv    = [(RawTermVar, PolyType)]
type DataEnv  = [(String, [TyVar])]
type AxiomEnv = [Axiom]
type RuleEnv  = [Rule]
data Env      = Env { _fnE    :: FnEnv
                    , _dataE  :: DataEnv
                    , _axiomE :: AxiomEnv
                    , _ruleE  :: RuleEnv }

$(makeLenses ''Env)

instance Monoid Env where
  mempty = Env [] [] [] []
  (Env f1 d1 a1 r1) `mappend` (Env f2 d2 a2 r2) =
    Env (f1 `union` f2) (d1 `union` d2) (a1 ++ a2) (r1 ++ r2)

type RawDefn = (RawTermVar, RawTerm, Maybe PolyType)
type TyDefn  = (TyTermVar,  TyTerm,  PolyType)

initialDataEnv :: DataEnv
initialDataEnv = [("Int",     [])
                 ,("Char",    [])
                 ,("List",    [string2Name "a"])
                 ,("Tuple2",  [string2Name "a", string2Name "b"])]

-- Hand-written `RepLib` instance for `unbound`
instance Rep t => Rep (Term t) where
  rep = Data (DT "Term" ((rep :: R t) :+: MNil))
             [ Con rIntLiteral ((rep :: R Integer) :+: (rep :: R t) :+: MNil)
             , Con rTermVar    ((rep :: R (TermVar t)) :+: (rep :: R t) :+: MNil)
             , Con rTermAbs    ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R t)
                                :+: (rep :: R t) :+: MNil)
             , Con rTermAbsAnn ((rep :: R (Bind (TermVar t) (Term t))) :+: (rep :: R t)
                                :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermApp    ((rep :: R (Term t)) :+: (rep :: R (Term t)) :+: (rep :: R t) :+: MNil)
             , Con rTermLet    ((rep :: R (Bind (TermVar t, Embed (Term t)) (Term t)))
                                :+: (rep :: R t) :+: MNil)
             , Con rTermLetAnn ((rep :: R (Bind (TermVar t, Embed (Term t)) (Term t)))
                                :+: (rep :: R PolyType) :+: (rep :: R t) :+: MNil)
             , Con rTermMatch  ((rep :: R (Term t)) :+: (rep :: R String)
                                :+: (rep :: R [(TermVar t, Bind [TermVar t] (Term t), t)])
                                :+: (rep :: R t) :+: MNil)
             , Con rStrLiteral ((rep :: R String) :+: (rep :: R t) :+: MNil)
             ]

instance ( Rep t, Sat (ctx t), Sat (ctx (Term t)), Sat (ctx (TermVar t))
         , Sat (ctx Integer), Sat (ctx String), Sat (ctx PolyType)
         , Sat (ctx (Bind (TermVar t) (Term t))), Sat (ctx (Bind (TermVar t, Embed (Term t)) (Term t)))
         , Sat (ctx [(TermVar t, Bind [TermVar t] (Term t), t)])) => Rep1 ctx (Term t) where
  rep1 = rAnnTerm1 dict dict dict dict dict dict dict dict dict

rAnnTerm1 :: forall t ctx. Rep t
          => ctx t -> ctx (Term t) -> ctx (TermVar t)
          -> ctx Integer -> ctx String -> ctx PolyType
          -> ctx (Bind (TermVar t) (Term t)) -> ctx (Bind (TermVar t, Embed (Term t)) (Term t))
          -> ctx [(TermVar t, Bind [TermVar t] (Term t), t)] -> R1 ctx (Term t)
rAnnTerm1 ct ctt ctv ci cs cp cb1 cb2 cbl =
  Data1 (DT "Term" ((rep :: R t) :+: MNil))
        [ Con rIntLiteral (ci  :+: ct :+: MNil)
        , Con rTermVar    (ctv :+: ct :+: MNil)
        , Con rTermAbs    (cb1 :+: ct :+: ct :+: MNil)
        , Con rTermAbsAnn (cb1 :+: ct :+: cp :+: ct :+: MNil)
        , Con rTermApp    (ctt :+: ctt :+: ct :+: MNil)
        , Con rTermLet    (cb2 :+: ct :+: MNil)
        , Con rTermLetAnn (cb2 :+: cp :+: ct :+: MNil)
        , Con rTermMatch  (ctt :+: cs :+: cbl :+: ct :+: MNil)
        , Con rStrLiteral (cs  :+: ct :+: MNil)
        ]

rIntLiteral :: Emb (Integer :*: t :*: Nil) (Term t)
rIntLiteral = Emb { to = \(n :*: t :*: Nil) -> Term_IntLiteral n t
                  , from = \x -> case x of
                                   Term_IntLiteral n t -> Just (n :*: t :*: Nil)
                                   _                   -> Nothing
                  , labels = Nothing
                  , name = "Term_IntLiteral"
                  , fixity = Nonfix
                  }

rTermVar :: Emb (TermVar t :*: t :*: Nil) (Term t)
rTermVar = Emb { to = \(v :*: t :*: Nil) -> Term_Var v t
               , from = \x -> case x of
                                Term_Var v t -> Just (v :*: t :*: Nil)
                                _            -> Nothing
               , labels = Nothing
               , name = "Term_Var"
               , fixity = Nonfix
               }

rTermAbs :: Emb (Bind (TermVar t) (Term t) :*: t :*: t :*: Nil) (Term t)
rTermAbs = Emb { to = \(b :*: bt :*: t :*: Nil) -> Term_Abs b bt t
               , from = \x -> case x of
                               Term_Abs b bt t -> Just (b :*: bt :*: t :*: Nil)
                               _               -> Nothing
               , labels = Nothing
               , name = "Term_Abs"
               , fixity = Nonfix
               }

rTermAbsAnn :: Emb (Bind (TermVar t) (Term t) :*: t :*: PolyType :*: t :*: Nil) (Term t)
rTermAbsAnn = Emb { to = \(b :*: bt :*: p :*: t :*: Nil) -> Term_AbsAnn b bt p t
                  , from = \x -> case x of
                                  Term_AbsAnn b bt p t -> Just (b :*: bt :*: p :*: t :*: Nil)
                                  _                    -> Nothing
                  , labels = Nothing
                  , name = "Term_AbsAnn"
                  , fixity = Nonfix
                  }

rTermApp :: Emb (Term t :*: Term t :*: t :*: Nil) (Term t)
rTermApp = Emb { to = \(t1 :*: t2 :*: t :*: Nil) -> Term_App t1 t2 t
               , from = \x -> case x of
                               Term_App t1 t2 t -> Just (t1 :*: t2 :*: t :*: Nil)
                               _                -> Nothing
               , labels = Nothing
               , name = "Term_App"
               , fixity = Nonfix
               }

rTermLet :: Emb (Bind (TermVar t, Embed (Term t)) (Term t) :*: t :*: Nil) (Term t)
rTermLet = Emb { to = \(b :*: t :*: Nil) -> Term_Let b t
               , from = \x -> case x of
                               Term_Let b t -> Just (b :*: t :*: Nil)
                               _            -> Nothing
               , labels = Nothing
               , name = "Term_Let"
               , fixity = Nonfix
               }

rTermLetAnn :: Emb (Bind (TermVar t, Embed (Term t)) (Term t) :*: PolyType :*: t :*: Nil) (Term t)
rTermLetAnn = Emb { to = \(b :*: p :*: t :*: Nil) -> Term_LetAnn b p t
                  , from = \x -> case x of
                                  Term_LetAnn b p t -> Just (b :*: p :*: t :*: Nil)
                                  _                 -> Nothing
                  , labels = Nothing
                  , name = "Term_LetAnn"
                  , fixity = Nonfix
                  }

rTermMatch :: Emb (Term t :*: String :*: [(TermVar t, Bind [TermVar t] (Term t), t)] :*: t :*: Nil) (Term t)
rTermMatch = Emb { to = \(e :*: c :*: alts :*: t :*: Nil) -> Term_Match e c alts t
                 , from = \x -> case x of
                                 Term_Match e c alts t -> Just (e :*: c :*: alts :*: t :*: Nil)
                                 _                     -> Nothing
                 , labels = Nothing
                 , name = "Term_Match"
                 , fixity = Nonfix
                 }

rStrLiteral :: Emb (String :*: t :*: Nil) (Term t)
rStrLiteral = Emb { to = \(n :*: t :*: Nil) -> Term_StrLiteral n t
                  , from = \x -> case x of
                                   Term_StrLiteral n t -> Just (n :*: t :*: Nil)
                                   _                   -> Nothing
                  , labels = Nothing
                  , name = "Term_StrLiteral"
                  , fixity = Nonfix
                  }

instance Alpha t => Alpha (Term t)
instance (Alpha t, Subst (Term t) t, Subst t Constraint, Subst t MonoType, Subst t PolyType) => Subst (Term t) (Term t) where
  isvar (Term_Var v _) = Just (SubstName v)
  isvar _              = Nothing
instance (Alpha t, Subst t t, Subst t PolyType) => Subst t (Term t)

instance (Subst t PolyType, Subst t Constraint, Subst t MonoType) => Subst (Term t) PolyType
instance (Subst t MonoType) => Subst (Term t) MonoType
instance (Subst t Constraint, Subst t PolyType, Subst t MonoType) => Subst (Term t) Constraint

instance Rep SourcePos where
  rep = Data (DT "SourcePos" MNil)
             [ Con rSourcePos ((rep :: R String) :+: (rep :: R Int) :+: (rep :: R Int) :+: MNil) ]

instance (Sat (ctx String), Sat (ctx Int)) => Rep1 ctx SourcePos where
  rep1 = Data1 (DT "SourcePos" MNil)
               [ Con rSourcePos (dict  :+: dict :+: dict :+: MNil) ]

rSourcePos :: Emb (String :*: Int :*: Int :*: Nil) SourcePos
rSourcePos = Emb { to = \(fn :*: i :*: f :*: Nil) -> newPos fn i f
                 , from = \x -> Just (sourceName x :*: sourceLine x :*: sourceColumn x :*: Nil)
                 , labels = Nothing
                 , name = "SourcePos"
                 , fixity = Nonfix
                 }

instance Alpha SourcePos

$(derive [''RuleRegex, ''RuleScriptInstr, ''RuleScriptOrdering, ''RuleScriptMessage])
instance Alpha RuleRegex
instance Alpha RuleScriptInstr
instance Alpha RuleScriptOrdering
instance Alpha RuleScriptMessage

instance Subst MonoType RuleRegex
instance Subst MonoType RuleScriptInstr
instance Subst MonoType RuleScriptOrdering
instance Subst MonoType RuleScriptMessage

-- Show instances

instance (Alpha t, Show t) => Show (Term t) where
  show = showAnnTerm id

showAnnTerm :: (Alpha a, Show b) => (a -> b) -> Term a -> String
showAnnTerm f = unlines . runFreshM . showAnnTerm' f

showAnnTerm' :: (Fresh m, Alpha a, Show b) => (a -> b) -> Term a -> m [String]
showAnnTerm' f (Term_IntLiteral n t) = return [show n ++ " ==> " ++ show (f t)]
showAnnTerm' f (Term_Var v t) = return [show v ++ " ==> " ++ show (f t)]
showAnnTerm' f (Term_Abs b _ t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\" ++ show x ++ " -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (Term_AbsAnn b _ p t) = do
  (x,e) <- unbind b
  inner <- showAnnTerm' f e
  let line1 = "\\(" ++ show x ++ " :: " ++ show p ++ ") -> ==> " ++ show (f t)
  return $ line1 : map ("  " ++) inner
showAnnTerm' f (Term_App a b t) = do
  e1 <- showAnnTerm' f a
  e2 <- showAnnTerm' f b
  let line1 = "@ ==> " ++ show (f t)
  return $ line1 : map ("  " ++) (e1 ++ e2)
showAnnTerm' f (Term_Let b t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)
showAnnTerm' f (Term_LetAnn b p t) = do
  ((x, unembed -> e1),e2) <- unbind b
  s1 <- showAnnTerm' f e1
  s2 <- showAnnTerm' f e2
  let line1 = "let " ++ show x ++ " :: " ++ show p ++ " = "
      line2 = "in ==> " ++ show t
  return $ (line1 : map ("  " ++) s1) ++ (line2 : map ("  " ++) s2)
showAnnTerm' f (Term_Match e c bs t) = do
  e'  <- showAnnTerm' f e
  bs' <- mapM (\(d,b,a) -> do (xs,es) <- unbind b
                              es' <- showAnnTerm' f es
                              let line1 = "| " ++ intercalate " " (map show (d:xs))
                                               ++ " ->" ++ " ==> " ++ show (f a)
                              return $ line1 : map ("    " ++) es') bs
  let firstPart  = "match " : map ("  " ++) e'
      line2      = "with " ++ c ++ " ==> " ++ show (f t)
      secondPart = line2 : concat bs'
  return $ firstPart ++ secondPart
showAnnTerm' f (Term_StrLiteral n t) = return ["\"" ++ show n ++ "\" ==> " ++ show (f t)]

deriving instance Show Env
