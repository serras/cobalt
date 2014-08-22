module Language.Cobalt.Parser (
  parseTerm
, parsePolyType
, parseClosedPolyType
, parseMonoType
, parseSig
, parseDefn
, parseFile
) where

import Control.Applicative hiding (many)
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Unbound.LocallyNameless

import Language.Cobalt.Syntax

parseTerm :: Parsec String s Term
parseTerm = parseAtom `chainl1` (pure Term_App)

parseAtom :: Parsec String s Term
parseAtom = -- Parenthesized expression
            parens parseTerm
        <|> -- Type annotated abstraction
            try (createTermAbsAnn <$  reservedOp "\\"
                                  <*> parens ((,) <$> identifier
                                                  <*  reservedOp "::"
                                                  <*> parseClosedPolyType)
                                  <*  reservedOp "->"
                                  <*> parseTerm)
        <|> -- Abstraction
            createTermAbs <$  reservedOp "\\"
                          <*> identifier
                          <*  reservedOp "->"
                          <*> parseTerm
        <|> -- Type annotated let
            try (createTermLetAbs <$  reserved "let"
                                  <*> identifier
                                  <*  reservedOp "::"
                                  <*> parseClosedPolyType
                                  <*  reservedOp "="
                                  <*> parseTerm
                                  <*  reserved "in"
                                  <*> parseTerm)
        <|> -- Let
            createTermLet <$  reserved "let"
                          <*> identifier
                          <*  reservedOp "="
                          <*> parseTerm
                          <*  reserved "in"
                          <*> parseTerm
        <|> -- Literal
            Term_IntLiteral <$> integer
        <|> -- Variable
            Term_Var . string2Name <$> identifier

createTermAbsAnn :: (String, PolyType) -> Term -> Term
createTermAbsAnn (x,t) e = Term_AbsAnn (bind (string2Name x) e) t

createTermAbs :: String -> Term -> Term
createTermAbs x e = Term_Abs (bind (string2Name x) e)

createTermLetAbs :: String -> PolyType -> Term -> Term -> Term
createTermLetAbs x t e1 e2 = Term_LetAnn (bind (string2Name x, embed e1) e2) t

createTermLet :: String -> Term -> Term -> Term
createTermLet x e1 e2 = Term_Let (bind (string2Name x, embed e1) e2)

parsePolyType :: Parsec String s PolyType
parsePolyType = try (createPolyType PolyType_Inst
                     <$> braces ((,) <$> identifier
                                     <*  reservedOp ">"
                                     <*> parsePolyType)
                     <*> parsePolyType)
            <|> try (createPolyType PolyType_Equal
                     <$> braces ((,) <$> identifier
                                     <*  reservedOp "="
                                     <*> parsePolyType)
                     <*> parsePolyType)
            <|> try (createPolyType PolyType_Inst
                     <$> braces ((,) <$> identifier
                                     <*> pure PolyType_Bottom)
                     <*> parsePolyType)
            <|> PolyType_Bottom <$ reservedOp "_|_"
            <|> PolyType_Mono <$> parseMonoType

parseClosedPolyType :: Parsec String s PolyType
parseClosedPolyType = do t <- parsePolyType
                         if null $ fvAny t
                            then return t
                            else fail "Closed type expected"

createPolyType :: ((Bind (TyVar, Embed PolyType) PolyType) -> PolyType)
               -> (String,PolyType) -> PolyType -> PolyType
createPolyType f (x,s) r = f (bind (string2Name x, embed s) r)

parseMonoType :: Parsec String s MonoType
parseMonoType = foldr1 MonoType_Arrow <$> parseMonoAtom `sepBy1` reservedOp "->"

parseMonoAtom :: Parsec String s MonoType
parseMonoAtom = const intTy <$> reserved "Integer"
            <|> listTy <$> brackets parseMonoType
            <|> try (uncurry tupleTy <$>
                       parens ((,) <$> parseMonoType
                                   <*  comma
                                   <*> parseMonoType))
            <|> MonoType_Con <$> parseDataName
                             <*> many (    (\x -> MonoType_Con x []) <$> parseDataName
                                       <|> MonoType_Var . string2Name <$> identifier
                                       <|> parens parseMonoType)
            <|> MonoType_Var . string2Name <$> identifier

parseDataName :: Parsec String s String
parseDataName = id <$ char '\'' <*> identifier

parseSig :: Parsec String s (TermVar,PolyType)
parseSig = (,) <$  reserved "import"
               <*> (string2Name <$> identifier)
               <*  reservedOp "::"
               <*> parsePolyType
               <*  reservedOp ";;"

parseDefn :: Parsec String s Defn
parseDefn = (,) <$> (string2Name <$> identifier)
                <*  reservedOp "="
                <*> parseTerm
                <*  reservedOp ";;"

parseFile :: Parsec String s (Env,[Defn])
parseFile = (,) <$> many parseSig
                <*> many parseDefn

-- Lexer for Haskell-like language

lexer :: T.TokenParser t
lexer = T.makeTokenParser haskellDef

parens :: Parsec String s a -> Parsec String s a
parens = T.parens lexer

braces :: Parsec String s a -> Parsec String s a
braces = T.braces lexer

brackets :: Parsec String s a -> Parsec String s a
brackets = T.brackets lexer

comma :: Parsec String s String
comma = T.comma lexer

identifier :: Parsec String s String
identifier = T.identifier lexer

reserved :: String -> Parsec String s ()
reserved = T.reservedOp lexer

reservedOp :: String -> Parsec String s ()
reservedOp = T.reservedOp lexer

integer :: Parsec String s Integer
integer = T.integer lexer
