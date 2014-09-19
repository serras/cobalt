{-# LANGUAGE TupleSections #-}

module Language.Cobalt.Parser (
  parseTerm
, parsePolyType
, parseClosedPolyType
, parseMonoType
, parseSig
, parseData
, parseAxiom
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
        <|> -- Case
            Term_Match <$  reserved "match"
                       <*> parseTerm
                       <*  reserved "with"
                       <*> parseDataName
                       <*> many parseCaseAlternative
        <|> -- Literal
            Term_IntLiteral <$> integer
        <|> -- Variable
            Term_Var . string2Name <$> identifier

parseCaseAlternative :: Parsec String s (TermVar, Bind [TermVar] Term)
parseCaseAlternative = createCaseAlternative <$  reservedOp "|"
                                             <*> identifier
                                             <*> many identifier
                                             <*  reservedOp "->"
                                             <*> parseTerm

createTermAbsAnn :: (String, PolyType) -> Term -> Term
createTermAbsAnn (x,t) e = Term_AbsAnn (bind (string2Name x) e) t

createTermAbs :: String -> Term -> Term
createTermAbs x e = Term_Abs (bind (string2Name x) e)

createTermLetAbs :: String -> PolyType -> Term -> Term -> Term
createTermLetAbs x t e1 e2 = Term_LetAnn (bind (string2Name x, embed e1) e2) t

createTermLet :: String -> Term -> Term -> Term
createTermLet x e1 e2 = Term_Let (bind (string2Name x, embed e1) e2)

createCaseAlternative :: String -> [String] -> Term -> (TermVar, Bind [TermVar] Term)
createCaseAlternative con args e = (string2Name con, bind (map string2Name args) e)

parsePolyType :: Parsec String s PolyType
parsePolyType = nf <$> parsePolyType'

parsePolyType' :: Parsec String s PolyType
parsePolyType' = createPolyTypeBind <$> braces identifier
                                    <*> parsePolyType'
             <|> try (PolyType_Mono <$> parseConstraint `sepBy1` comma
                                    <*  reservedOp "=>"
                                    <*> parseMonoType)
             <|> PolyType_Bottom <$ reservedOp "_|_"
             <|> PolyType_Mono [] <$> parseMonoType

parseClosedPolyType :: Parsec String s PolyType
parseClosedPolyType = do t <- parsePolyType
                         if null $ fvAny t
                            then return t
                            else fail "Closed type expected"

createPolyTypeBind :: String -> PolyType -> PolyType
createPolyTypeBind x p = PolyType_Bind $ bind (string2Name x) p

parseConstraint :: Parsec String s Constraint
parseConstraint = try (Constraint_Inst  <$> (var . string2Name <$> identifier)
                                        <*  reservedOp ">"
                                        <*> parsePolyType)
              <|> try (Constraint_Equal <$> (var . string2Name <$> identifier)
                                        <*  reservedOp "="
                                        <*> parsePolyType)
              <|> Constraint_Unify <$> parseMonoType
                                   <*  reservedOp "~"
                                   <*> parseMonoType

parseMonoType :: Parsec String s MonoType
parseMonoType = foldr1 MonoType_Arrow <$> parseMonoAtom `sepBy1` reservedOp "->"

parseMonoAtom :: Parsec String s MonoType
parseMonoAtom = MonoType_List <$> brackets parseMonoType
            <|> try (uncurry MonoType_Tuple <$>
                       parens ((,) <$> parseMonoType
                                   <*  comma
                                   <*> parseMonoType))
            <|> parens parseMonoType
            <|> MonoType_Con <$> parseDataName
                             <*> many (    (\x -> MonoType_Con x []) <$> parseDataName
                                       <|> (\x -> MonoType_Fam x []) <$> parseFamName
                                       <|> MonoType_Var . string2Name <$> identifier
                                       <|> parens parseMonoType)
            <|> MonoType_Fam <$> parseFamName
                             <*> many (    (\x -> MonoType_Con x []) <$> parseDataName
                                       <|> (\x -> MonoType_Fam x []) <$> parseFamName
                                       <|> MonoType_Var . string2Name <$> identifier
                                       <|> parens parseMonoType)
            <|> MonoType_Var . string2Name <$> identifier

parseDataName :: Parsec String s String
parseDataName = id <$ char '\'' <*> identifier

parseFamName :: Parsec String s String
parseFamName = id <$ char '^' <*> identifier

parseSig :: Parsec String s (TermVar,PolyType)
parseSig = (,) <$  reserved "import"
               <*> (string2Name <$> identifier)
               <*  reservedOp "::"
               <*> parsePolyType
               <*  reservedOp ";"

parseData :: Parsec String s (String,[TyVar])
parseData = (,) <$  reserved "data"
                <*> parseDataName
                <*> many (string2Name <$> identifier)
                <*  reservedOp ";"

parseAxiom :: Parsec String s Axiom
parseAxiom = createAxiomUnify <$  reserved "axiom"
                              <*> many (braces identifier)
                              <*> parseMonoType
                              <*  reservedOp "~"
                              <*> parseMonoType
                              <*  reservedOp ";"

createAxiomUnify :: [String] -> MonoType -> MonoType -> Axiom
createAxiomUnify vs r l = Axiom_Unify (bind (map string2Name vs) (r,l))

parseDefn :: Parsec String s (Defn,Bool)
parseDefn = try ((\x y z w -> ((x,z,Just y),w))
                     <$> (string2Name <$> identifier)
                     <*  reservedOp "::"
                     <*> parsePolyType
                     <*  reservedOp "="
                     <*> parseTerm
                     <*> parseExpected
                     <*  reservedOp ";")
        <|> (\x z w -> ((x,z,Nothing),w))
                     <$> (string2Name <$> identifier)
                     <*  reservedOp "="
                     <*> parseTerm
                     <*> parseExpected
                     <*  reservedOp ";"

parseExpected :: Parsec String s Bool
parseExpected = try (id <$ reservedOp "=>" <*> (    const True  <$> reservedOp "ok"
                                                <|> const False <$> reservedOp "fail"))
            <|> pure True

parseFile :: Parsec String s (Env,[(Defn,Bool)])
parseFile = (\x y w z -> (Env y x w, z))
                   <$> many parseData
                   <*> many parseSig
                   <*> many parseAxiom
                   <*> many parseDefn

-- Lexer for Haskell-like language

lexer :: T.TokenParser t
lexer = T.makeTokenParser $ haskellDef { T.reservedNames = "with" : T.reservedNames haskellDef }

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
