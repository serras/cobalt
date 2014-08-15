module Language.HigherRank.Parser (
  parseTerm
, parsePolyType
, parseRhoType
, parseMonoType
) where

import Control.Applicative
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Unbound.LocallyNameless

import Language.HigherRank.Syntax

parseTerm :: Parsec String s Term
parseTerm = parseAtom `chainl1` (pure Term_App)

parseAtom :: Parsec String s Term
parseAtom = -- Type annotation
            try (uncurry Term_Ann <$> parens ((,) <$> parseTerm
                                                  <*  reservedOp "::"
                                                  <*> parsePolyType))
        <|> -- Parenthesized expression
            parens parseTerm
        <|> -- Type annotated abstraction
            try (createTermAnnAbs <$> braces ((,) <$> identifier
                                                    <*  reservedOp "::"
                                                    <*> parsePolyType)
                                  <*> parseTerm)
        <|> -- Abstraction
            createTermAbs <$> braces identifier <*> parseTerm
        <|> -- Literal
            Term_IntLiteral <$> integer
        <|> -- Variable
            Term_Var . string2Name <$> identifier

createTermAbs :: String -> Term -> Term
createTermAbs x e = Term_Abs (bind (string2Name x) e)

createTermAnnAbs :: (String, PolyType) -> Term -> Term
createTermAnnAbs (x,t) e = Term_AnnAbs (bind (string2Name x) e) t

parsePolyType :: Parsec String s PolyType
parsePolyType = createPolyType <$> braces (commaSep identifier)
                               <*> parseRhoType
            <|> parens parsePolyType

createPolyType :: [String] -> RhoType -> PolyType
createPolyType vars rho = PolyType_Quant (bind (map string2Name vars) rho)

parseRhoType :: Parsec String s RhoType
parseRhoType = RhoType_Arrow <$> parsePolyType
                             <*  reservedOp "->"
                             <*> parseRhoType
           <|> RhoType_Mono <$> parseMonoType
           <|> parens parseRhoType

parseMonoType :: Parsec String s MonoType
parseMonoType = foldr1 MonoType_Arrow <$> parseMonoAtom `sepBy1` reservedOp "->"

parseMonoAtom :: Parsec String s MonoType
parseMonoAtom = const MonoType_Int <$> reserved "Integer"
            <|> MonoType_List <$> brackets parseMonoType
            <|> try (uncurry MonoType_Tuple <$>
                       parens ((,) <$> parseMonoType
                                   <*  comma
                                   <*> parseMonoType))
            <|> parens parseMonoType
            <|> MonoType_Var . string2Name <$> identifier

-- Lexer for Haskell-like language

lexer :: T.TokenParser t
lexer = T.makeTokenParser haskellStyle

parens :: Parsec String s a -> Parsec String s a
parens = T.parens lexer

braces :: Parsec String s a -> Parsec String s a
braces = T.braces lexer

brackets :: Parsec String s a -> Parsec String s a
brackets = T.brackets lexer

comma :: Parsec String s String
comma = T.comma lexer

commaSep :: Parsec String s a -> Parsec String s [a]
commaSep = T.commaSep lexer

identifier :: Parsec String s String
identifier = T.identifier lexer

reserved :: String -> Parsec String s ()
reserved = T.reservedOp lexer

reservedOp :: String -> Parsec String s ()
reservedOp = T.reservedOp lexer

integer :: Parsec String s Integer
integer = T.integer lexer
