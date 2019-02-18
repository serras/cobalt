{-# LANGUAGE TupleSections #-}

module Cobalt.Language.Parser (
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
import Data.List ((\\), nub)
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Unbound.LocallyNameless

import Cobalt.Language.Syntax
import Cobalt.Core

parseTerm :: Parsec String s RawTerm
parseTerm = parseAtom `chainl1` pure joinTerms
            where joinTerms x y = let (xInn,xFin) = getAnn x
                                      (yInn,yFin) = getAnn y
                                   in Term_App x y (min xInn yInn, max xFin yFin)

parseAtom :: Parsec String s RawTerm
parseAtom = -- Parenthesized expression
            (\pin tm pe -> atAnn (const (pin,pe)) tm) <$> getPosition
                                                      <*> parens parseTerm
                                                      <*> getPosition
        <|> -- Type annotated abstraction
            try (createTermAbsAnn <$> getPosition
                                  <*  reservedOp "\\"
                                  <*> parens ((,,,) <$> getPosition
                                                    <*> identifier
                                                    <*  reservedOp "::"
                                                    <*> parseClosedPolyType
                                                    <*> getPosition)
                                  <*  reservedOp "->"
                                  <*> parseTerm
                                  <*> getPosition)
        <|> -- Abstraction
            createTermAbs <$> getPosition
                          <*  reservedOp "\\"
                          <*> getPosition
                          <*> identifier
                          <*> getPosition
                          <*  reservedOp "->"
                          <*> parseTerm
                          <*> getPosition
        <|> -- Type annotated let
            try (createTermLetAbs <$> getPosition
                                  <*  reserved "let"
                                  <*> identifier
                                  <*  reservedOp "::"
                                  <*> parseClosedPolyType
                                  <*  reservedOp "="
                                  <*> parseTerm
                                  <*  reserved "in"
                                  <*> parseTerm
                                  <*> getPosition)
        <|> -- Let
            createTermLet <$> getPosition
                          <*  reserved "let"
                          <*> identifier
                          <*  reservedOp "="
                          <*> parseTerm
                          <*  reserved "in"
                          <*> parseTerm
                          <*> getPosition
        <|> -- Case
            createTermMatch <$> getPosition
                            <*  reserved "match"
                            <*> parseTerm
                            <*  reserved "with"
                            <*> parseDataName
                            <*> many parseCaseAlternative
                            <*> getPosition
        <|> -- Do notation
            (do reserved "do"
                actions <- parseDoAction `sepBy1` comma
                pos     <- getPosition
                createTermDo actions pos)
        <|> -- Integer literal
            (\i n f -> Term_IntLiteral n (i,f)) <$> getPosition
                                                <*> integer
                                                <*> getPosition
        <|> -- String literal
            (\i n f -> Term_StrLiteral n (i,f)) <$> getPosition
                                                <*> stringLiteral
                                                <*> getPosition
        <|> -- Variable
            (\i v f -> Term_Var (string2Name v) (i,f)) <$> getPosition
                                                       <*> identifier
                                                       <*> getPosition

parseCaseAlternative :: Parsec String s (RawTermVar, Bind [RawTermVar] RawTerm, (SourcePos,SourcePos))
parseCaseAlternative = createCaseAlternative <$> getPosition
                                             <*  reservedOp "|"
                                             <*> identifier
                                             <*> many identifier
                                             <*  reservedOp "->"
                                             <*> parseTerm
                                             <*> getPosition

createTermAbsAnn :: SourcePos -> (SourcePos,String, PolyType,SourcePos) -> RawTerm -> SourcePos -> RawTerm
createTermAbsAnn i (vi,x,t,vf) e f = Term_AbsAnn (bind (string2Name x) e) (vi,vf) t (i,f)

createTermAbs :: SourcePos -> SourcePos -> String -> SourcePos -> RawTerm -> SourcePos -> RawTerm
createTermAbs i vi x vf e f = Term_Abs (bind (string2Name x) e) (vi,vf) (i,f)

createTermLetAbs :: SourcePos -> String -> PolyType -> RawTerm -> RawTerm -> SourcePos -> RawTerm
createTermLetAbs i x t e1 e2 f = Term_LetAnn (bind (string2Name x, embed e1) e2) t (i,f)

createTermLet :: SourcePos -> String -> RawTerm -> RawTerm -> SourcePos -> RawTerm
createTermLet i x e1 e2 f = Term_Let (bind (string2Name x, embed e1) e2) (i,f)

createTermMatch :: SourcePos -> RawTerm -> String
                -> [(RawTermVar, Bind [RawTermVar] RawTerm, (SourcePos, SourcePos))]
                -> SourcePos -> RawTerm
createTermMatch i e t c f = Term_Match e t c (i,f)

createCaseAlternative :: SourcePos -> String -> [String] -> RawTerm -> SourcePos
                      -> (RawTermVar, Bind [RawTermVar] RawTerm, (SourcePos, SourcePos))
createCaseAlternative i con args e f = (string2Name con, bind (map string2Name args) e, (i,f))

createTermDo :: [DoAction] -> SourcePos -> Parsec String s RawTerm
createTermDo []                             _     = fail "empty do blocks not allowed"
createTermDo [DoAction_Term _ t _]          _     = return t
createTermDo [_]                            _     = fail "do blocks must end with a term"
createTermDo ((DoAction_Term s t e)     : as) doEnd = do
  rest <- createTermDo as doEnd
  return $ Term_App
             (Term_App (Term_Var (string2Name "then_") (s,e)) t (s,e))
             rest (s,doEnd)
createTermDo ((DoAction_Assign s v t e) : as) doEnd = do
  rest <- createTermDo as doEnd
  return $ Term_App
             (Term_App (Term_Var (string2Name "bind_") (s,e)) t (s,e))
             (Term_Abs (bind v rest) (e,e) (e,doEnd))
             (s,doEnd)
createTermDo ((DoAction_Let s v t _)    : as) doEnd = do
  rest <- createTermDo as doEnd
  return $ Term_Let (bind (v, embed t) rest) (s,doEnd)

data DoAction = DoAction_Term   SourcePos RawTerm            SourcePos
              | DoAction_Assign SourcePos RawTermVar RawTerm SourcePos
              | DoAction_Let    SourcePos RawTermVar RawTerm SourcePos

parseDoAction :: Parsec String s DoAction
parseDoAction = try (DoAction_Assign <$> getPosition
                                     <*> (string2Name <$> identifier)
                                     <*  reservedOp "<-"
                                     <*> parseTerm
                                     <*> getPosition)
            <|> try (DoAction_Let    <$> getPosition
                                     <*  reserved "let"
                                     <*> (string2Name <$> identifier)
                                     <*  reservedOp "="
                                     <*> parseTerm
                                     <*> getPosition)
            <|> try (DoAction_Term   <$> getPosition
                                     <*> parseTerm
                                     <*> getPosition)

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
                         if null (fvAny t :: [AnyName])
                            then return t
                            else fail "Closed type expected"

createPolyTypeBind :: String -> PolyType -> PolyType
createPolyTypeBind x p = PolyType_Bind $ bind (string2Name x) p

parseConstraint :: Parsec String s Constraint
parseConstraint = Constraint_Inconsistent <$ reservedOp "_|_"
              <|> Constraint_Later <$  reserved "later"
                                   <*> stringLiteral
                                   <*> brackets (commaSep1 parseConstraint)
              <|> (\m -> Constraint_Later m [Constraint_Inconsistent])
                                   <$  reserved "repair"
                                   <*> stringLiteral
              <|> Constraint_Cond  <$  reserved "cond"
                                   <*> brackets (commaSep1 parseConstraint)
                                   <*> brackets (commaSep1 parseConstraint)
                                   <*> brackets (commaSep1 parseConstraint)
              <|> try (Constraint_Inst  <$> (var . string2Name <$> parseVarName)
                                        <*  reservedOp ">"
                                        <*> parsePolyType)
              <|> try (Constraint_Equal <$> (var . string2Name <$> parseVarName)
                                        <*  reservedOp "="
                                        <*> parsePolyType)
              <|> Constraint_Class <$> parseClsName
                                   <*> many parseMonoType
              <|> Constraint_Unify <$> parseMonoType
                                   <*  reservedOp "~"
                                   <*> parseMonoType

parseMonoType :: Parsec String s MonoType
parseMonoType = foldr1 (:-->:) <$> parseMonoAtom `sepBy1` reservedOp "->"

parseMonoAtom :: Parsec String s MonoType
parseMonoAtom = MonoType_List <$> brackets parseMonoType
            <|> try (uncurry MonoType_Tuple <$>
                       parens ((,) <$> parseMonoType
                                   <*  comma
                                   <*> parseMonoType))
            <|> parens parseMonoType
            <|> (conApply <$> parseDataName)
                             <*> many (    (\x -> MonoType_Con x) <$> parseDataName
                                       <|> (\x -> MonoType_Fam x []) <$> parseFamName
                                       <|> MonoType_List <$> brackets parseMonoType
                                       <|> MonoType_Var . string2Name <$> parseVarName
                                       <|> parens parseMonoType)
            <|> MonoType_Fam <$> parseFamName
                             <*> many (    (\x -> MonoType_Con x) <$> parseDataName
                                       <|> (\x -> MonoType_Fam x []) <$> parseFamName
                                       <|> MonoType_List <$> brackets parseMonoType
                                       <|> MonoType_Var . string2Name <$> parseVarName
                                       <|> parens parseMonoType)
            <|> MonoType_Var . string2Name <$> parseVarName

parseDataName :: Parsec String s String
parseDataName = id <$ char '\'' <*> identifier

parseFamName :: Parsec String s String
parseFamName = id <$ char '^' <*> identifier

parseClsName :: Parsec String s String
parseClsName = id <$ char '$' <*> identifier

parseVarName :: Parsec String s String
parseVarName =     (:) <$> char '#' <*> identifier
               <|> identifier

parseSig :: Parsec String s (RawTermVar, PolyType)
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

parseAxiom :: Parsec String s [Axiom]
parseAxiom = id <$ reserved "axiom"
                <*> (    (\x -> [x]) . Axiom_Injective
                                         <$  reserved "injective"
                                         <*> parseFamName
                     <|> (\x -> [x]) . Axiom_Defer
                                         <$  reserved "defer"
                                         <*> parseFamName
                     <|> try (do reserved "synonym"
                                 idents <- many (braces identifier)
                                 m1 <- parseMonoType
                                 reservedOp "~"
                                 m2 <- parseMonoType
                                 createAxiomSynonym idents m1 m2)
                     <|> try (createAxiomUnify <$> many (braces identifier)
                                               <*> parseMonoType
                                               <*  reservedOp "~"
                                               <*> parseMonoType)
                     <|> try (createAxiomClass <$> many (braces identifier)
                                               <*> parseConstraint `sepBy1` comma
                                               <*  reservedOp "=>"
                                               <*> parseClsName
                                               <*> many parseMonoType)
                     <|> flip createAxiomClass [] <$> many (braces identifier)
                                                  <*> parseClsName
                                                  <*> many parseMonoType )
                <* reservedOp ";"

createAxiomSynonym :: [String] -> MonoType -> MonoType -> Parsec String s [Axiom]
createAxiomSynonym vs r@(MonoType_Fam f _) l = return $
  Axiom_Injective f : Axiom_Defer f : createAxiomUnify vs r l
createAxiomSynonym _ _ _ = fail "Incorrect type synonym specification"

createAxiomUnify :: [String] -> MonoType -> MonoType -> [Axiom]
createAxiomUnify vs r l = [Axiom_Unify (bind (map string2Name vs) (r,l))]

createAxiomClass :: [String] -> [Constraint] -> String -> [MonoType] -> [Axiom]
createAxiomClass vs ctx c m = [Axiom_Class (bind (map string2Name vs) (ctx,c,m))]

parseDefn :: Parsec String s (RawDefn,Bool)
parseDefn = buildDefn
                <$> getPosition
                <*> many1 identifier
                <*> (    try (Just <$  reservedOp "::"
                                   <*> parsePolyType)
                     <|> pure Nothing)
                <*  reservedOp "="
                <*> parseTerm
                <*> parseExpected
                <*  reservedOp ";"
                <*> getPosition

buildDefn :: SourcePos -> [String] -> Maybe PolyType -> RawTerm -> Bool -> SourcePos -> (RawDefn,Bool)
buildDefn _ [] _ _ _ _ = error "This should never happen"
buildDefn i (n:args) ty tr ex f = let finalTerm = foldr (\x y -> createTermAbs i i x f y f) tr args
                                  in ((string2Name n,finalTerm,ty),ex)

parseExpected :: Parsec String s Bool
parseExpected = try (id <$ reservedOp "=>" <*> (    const True  <$> reservedOp "ok"
                                                <|> const False <$> reservedOp "fail"))
            <|> pure True

parseRule :: Parsec String s Rule
parseRule = do reserved "rule"
               st <-  id <$  reserved "strict"
                         <*> pure RuleStrictness_Strict
                  <|> id <$  reserved "unsafe"
                         <*> pure RuleStrictness_Unsafe
                  <|> pure RuleStrictness_NonStrict
               nm <- identifier
               (rx,ch,sc) <- parseRuleBody
               reservedOp ";"
               createRule st nm rx ch sc

createRule :: RuleStrictness -> String -> RuleRegex -> [Constraint] -> RuleScript -> Parsec String s Rule
createRule st nm rx ch sc = do
  let rxVars  = nub (fv rx)
      thisVar = s2n "#this"
      chVars  = nub (fv ch) \\ (thisVar : rxVars)
      scVars  = nub (fv sc) \\ (thisVar : rxVars)
  case (chVars, scVars) of
    (_:_, _:_) -> fail ("Neither check nor script blocks may have unbound variables" ++ show (chVars `union` scVars))
    (_:_, [])  -> fail ("`check` blocks may not have unbound variables: " ++ show chVars)
    ([] , _:_) -> fail ("`script` blocks may not have unbound variables (use `fresh`): " ++ show scVars)
    ([] , [])  -> return $ Rule st nm (bind (thisVar,rxVars) (rx, ch, sc))

parseRuleBody :: Parsec String s (RuleRegex, [Constraint], RuleScript)
parseRuleBody = (,,) <$  reserved "case"
                     <*> parseRuleRegex
                     <*> (    id <$ reserved "when" <*> commaSep1 parseConstraint
                          <|> pure [])
                     <*> braces parseRuleScript

parseRuleCapture :: Parsec String s TyVar
parseRuleCapture = s2n . ('#' :) <$ char '#' <*> identifier

parseRuleRegex :: Parsec String s RuleRegex
parseRuleRegex = parseRuleRegexApp `chainl1` (RuleRegex_Choice <$ reservedOp "|")

parseRuleRegexApp :: Parsec String s RuleRegex
parseRuleRegexApp = parseRuleRegexAtom `chainl1` (pure RuleRegex_App)

parseRuleRegexAtom :: Parsec String s RuleRegex
parseRuleRegexAtom = -- Parenthesized expression
                     parens parseRuleRegex
                 <|> (\rx v -> RuleRegex_Iter $ bind (string2Name v) rx)
                                   <$> brackets parseRuleRegex
                                   <*  reservedOp "*"
                                   <*> identifier
                 <|> RuleRegex_Any <$ reserved "any"
                 <|> RuleRegex_Square <$ char '&' <*> (s2n <$> identifier)
                 <|> try (RuleRegex_Capture <$> parseRuleCapture <* char '@'
                                            <*> (Just <$> parens parseRuleRegex) )
                 <|> RuleRegex_Capture <$> parseRuleCapture <*> pure Nothing
                 <|> RuleRegex_Int <$> integer
                 <|> RuleRegex_Str <$> stringLiteral
                 <|> RuleRegex_Var <$> (s2n <$> identifier)

parseRuleScript :: Parsec String s RuleScript
parseRuleScript = bind <$> (    id <$ reserved "fresh" <*> many1 parseRuleCapture <* comma
                            <|> pure [])
                       <*> commaSep1 parseRuleInstrMsg

parseRuleInstrMsg :: Parsec String s (RuleScriptInstr, Maybe RuleScriptMessage)
parseRuleInstrMsg = (\msg -> (RuleScriptInstr_Constraint Constraint_Inconsistent Nothing, Just msg))
                        <$  reserved "repair"
                        <*> braces parseRuleMessage
                <|> (,) <$> parseRuleInstr
                        <*> optionMaybe (id <$  reserved "error"
                                            <*> braces parseRuleMessage)

parseRuleInstr :: Parsec String s RuleScriptInstr
parseRuleInstr = RuleScriptInstr_Empty    <$  reserved "empty"
             <|> RuleScriptInstr_Ref      <$  reserved "constraints"
                                          <*> parseRuleCapture
             <|> RuleScriptInstr_Ordered  <$  reserved "ordered"
                                          <*> braces parseRuleScript
             <|> RuleScriptInstr_Sequence <$  reserved "sequence"
                                          <*> braces parseRuleScript
             <|> RuleScriptInstr_Join     <$  reserved "join"
                                          <*> braces parseRuleScript
             <|> (\inner outer script -> RuleScriptInstr_ForEach outer (bind inner script))
                                          <$  reserved "foreach"
                                          <*> parseRuleCapture
                                          <*  reservedOp "<-"
                                          <*> parseRuleCaptureOrdering `sepBy1` (reservedOp "++")
                                          <*> braces parseRuleScript
             <|> try ((\x inner outer script -> RuleScriptInstr_Rec (Just x) outer (bind inner script))
                                          <$> parseMonoType
                                          <*  reservedOp "~"
                                          <*  reserved "rec"
                                          <*> parseRuleCapture
                                          <*  reservedOp "<-"
                                          <*> parseRuleCapture
                                          <*> braces parseRuleScript)
             <|> (\inner outer script -> RuleScriptInstr_Rec Nothing outer (bind inner script))
                                          <$  reserved "rec"
                                          <*> parseRuleCapture
                                          <*  reservedOp "<-"
                                          <*> parseRuleCapture
                                          <*> braces parseRuleScript
             <|> try ((\x -> RuleScriptInstr_Call (Just x))
                                          <$> parseMonoType
                                          <*  reservedOp "~"
                                          <*  reserved "call"
                                          <*> parseRuleCapture)
             <|> RuleScriptInstr_Call Nothing <$ reserved "call"
                                          <*> parseRuleCapture
             <|> RuleScriptInstr_Return   <$  reserved "returning"
                                          <*> parseMonoType
             <|> RuleScriptInstr_Match    <$  reserved "match"
                                          <*> parseRuleCapture
                                          <*> braces (
                                               commaSep1 (
                                                 -- HACK: use a name which no one would use
                                                 (\(rx,ch,sc) -> bind (s2n "#qwertyuiop", fv rx) (rx,ch,sc))
                                                   <$> parseRuleBody ) )
             <|> RuleScriptInstr_Constraint <$> parseConstraint
                                            <*> optionMaybe (id <$  reserved "explain"
                                                                <*> braces parseRuleMessage)

parseRuleCaptureOrdering :: Parsec String s (TyVar,RuleScriptOrdering)
parseRuleCaptureOrdering = (flip (,)) <$> (    RuleScriptOrdering_InToOut <$ reserved "inout"
                                           <|> RuleScriptOrdering_OutToIn <$ reserved "outin")
                                      <*> parseRuleCapture

parseRuleMessage :: Parsec String s RuleScriptMessage
parseRuleMessage = parseRuleMessageAtom
{-
parseRuleMessage :: Parsec String s RuleScriptMessage
parseRuleMessage = parseRuleMessageAtom `chainl1` (   RuleScriptMessage_Vertical   <$ reservedOp "<|>"
                                                  <|> RuleScriptMessage_Horizontal <$ reservedOp "<->")
-}

parseRuleMessageAtom :: Parsec String s RuleScriptMessage
parseRuleMessageAtom = parens parseRuleMessage
                   <|> RuleScriptMessage_Literal    <$> stringLiteral
                   {-
                   <|> RuleScriptMessage_Type       <$  reserved "type" <*> parseRuleCapture
                   <|> RuleScriptMessage_Expression <$  reserved "expr" <*> parseRuleCapture
                   <|> (\x xs s sep -> RuleScriptMessage_VConcat xs (bind x s) sep)
                                                    <$  reserved "vcat"
                                                    <*> parseRuleCapture
                                                    <*  reservedOp "<-"
                                                    <*> parseRuleCapture
                                                    <*> parseRuleMessage
                                                    <*> parseRuleMessage
                   <|> (\x xs s -> RuleScriptMessage_HConcat xs (bind x s))
                                                    <$  reserved "hcat"
                                                    <*> parseRuleCapture
                                                    <*  reservedOp "<-"
                                                    <*> parseRuleCapture
                                                    <*> parseRuleMessage -}

data DeclType = AData   (String, [TyVar])
              | AnAxiom [Axiom]
              | ASig    (RawTermVar, PolyType)
              | ADefn   (RawDefn, Bool)
              | ARule   Rule

parseDecl :: Parsec String s DeclType
parseDecl = AData   <$> parseData
        <|> AnAxiom <$> parseAxiom
        <|> ASig    <$> parseSig
        <|> ADefn   <$> parseDefn
        <|> ARule   <$> parseRule

buildProgram :: [DeclType] -> (Env, [(RawDefn,Bool)])
buildProgram = foldr (\decl (Env s d a r, df) -> case decl of
                        AData i   -> (Env s (i:d) a r, df)
                        AnAxiom i -> (Env s d (i ++ a) r, df)
                        ASig i    -> (Env (i:s) d a r, df)
                        ADefn i   -> (Env s d a r, i:df)
                        ARule i   -> (Env s d a (i:r),df))
                     (Env [] [] [] [], [])

parseFile :: Parsec String s (Env,[(RawDefn,Bool)])
parseFile = buildProgram <$> many parseDecl

-- Lexer for Haskell-like language

lexer :: T.TokenParser t
lexer = T.makeTokenParser $ haskellDef { T.reservedNames = "rule" : "strict" : "unsafe"            -- Rule
                                                           : "match" : "when" : "any"              -- Rule
                                                           : "type" : "expr" : "vcat" : "hcat"     -- Error msgs
                                                           : "fresh" : "constraints" : "repair"    -- Type tree
                                                           : "join" : "ordered" : "sequence"       -- Type tree
                                                           : "foreach" : "error" : "explain"       -- Type tree
                                                           : "rec" : "case" : "continue"           -- Type tree
                                                           : "call" : "returning"                  -- Type tree
                                                           : "inout" : "outin"                     -- Type tree ordering
                                                           : "injective" : "defer" : "synonym"     -- Axioms
                                                           : "do" : "with" : "later" : "cond"      -- Syntax
                                                           : T.reservedNames haskellDef }

parens :: Parsec String s a -> Parsec String s a
parens = T.parens lexer

braces :: Parsec String s a -> Parsec String s a
braces = T.braces lexer

brackets :: Parsec String s a -> Parsec String s a
brackets = T.brackets lexer

comma :: Parsec String s String
comma = T.comma lexer

-- commaSep :: Parsec String s a -> Parsec String s [a]
-- commaSep = T.commaSep lexer

commaSep1 :: Parsec String s a -> Parsec String s [a]
commaSep1 = T.commaSep1 lexer

identifier :: Parsec String s String
identifier = T.identifier lexer

reserved :: String -> Parsec String s ()
reserved = T.reservedOp lexer

reservedOp :: String -> Parsec String s ()
reservedOp = T.reservedOp lexer

integer :: Parsec String s Integer
integer = T.integer lexer

stringLiteral :: Parsec String s String
stringLiteral = T.stringLiteral lexer
