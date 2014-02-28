{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp, FlexibleContexts #-}
module Language.Parser
       (parseModule) where
import Language.Syntax
import Language.Monad (emit)
import Language.Program (progTerm)

import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
--import Text.PrettyPrint(text)
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent

import Control.Applicative hiding ((<|>),many, optional)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import Control.Exception(Exception)

import qualified Data.IntMap as IM
import Data.Typeable
import Data.Char
import Data.List

parseModule :: String -> String -> Either P.ParseError Module
parseModule srcName cnts = runIndent srcName $
                           runParserT gModule initialParserState srcName cnts

type Parser a = IndentParser String ParserState a

-- User state, so that we can update the operator parsing table.

data ParserState =
  ParserState {
    progParser :: IndentParser String ParserState Prog,
    formulaParser :: IndentParser String ParserState PreTerm,
    progOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Prog],
    formulaOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) PreTerm]}

initialParserState :: ParserState
initialParserState = ParserState {
  progParser = buildExpressionParser [] progA, --progPre,
  formulaParser = buildExpressionParser initialFormulaOpTable atom,
  progOpTable =  IM.fromAscList (zip [0 ..] [[]]),
  formulaOpTable =  IM.fromAscList (zip [0 ..] initialFormulaOpTable)}

initialFormulaOpTable :: [[Operator String u (State SourcePos) PreTerm]]
initialFormulaOpTable = [[], [], [], [binOp AssocRight "->" Imply]]

ftypeOpTable :: [[Operator String u (State SourcePos) FType]]
ftypeOpTable = [[binOp AssocRight "->" Arrow]]

binOp :: Assoc -> String -> (a -> a -> a) -> Operator String u (State SourcePos) a
binOp assoc op f = Infix (reservedOp op >> return f) assoc

postOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
postOp op f = Postfix (reservedOp op >> return f)

preOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
preOp op f = Prefix (reservedOp op >> return f)

toOp op "infix" app var = binOp AssocNone op (binApp op app var)
toOp op "infixr" app var = binOp AssocRight op (binApp op app var)
toOp op "infixl" app var = binOp AssocLeft op (binApp op app var)
toOp op "pre" app var = preOp op (preApp op app var)
toOp op "post" app var = postOp op (postApp op app var) 
toOp _ fx app var = error (fx ++ " is not a valid operator fixity.")

postApp op app var x = app (var op) x

preApp op app var x = app (var op) x

binApp op app var x y = app (app (var op) x) y

deriving instance Typeable P.ParseError
instance Exception P.ParseError where

-- parse module
gModule :: Parser Module
gModule = do
  whiteSpace
  reserved "module"
  modName <- identifier
  reserved "where"
  bs <- many1 gDecl
  eof
  return $ Module modName bs

gDecl :: Parser Decl
gDecl = gDataDecl <|> try proofDecl <|> try progDecl
        <|> setDecl <|> formOperatorDecl <|>
        progOperatorDecl <|> try tacticDecl

  
formOperatorDecl :: Parser Decl
formOperatorDecl = do
  reserved "formula"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl","pre","post"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r SApp PVar] $ formulaOpTable st
      form' = buildExpressionParser (map snd (IM.toAscList table')) atom
  putState $ ParserState
    (progParser st) form' (progOpTable st) table'
  return (FormOperatorDecl op level r)

progOperatorDecl :: Parser Decl
progOperatorDecl = do
  reserved "prog"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl","pre","post"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r Applica Name] $ progOpTable st
      prog' = buildExpressionParser (map snd (IM.toAscList table')) progA
  putState $ ParserState
    prog' (formulaParser st) table' (formulaOpTable st) 
  return (ProgOperatorDecl op level r)

gDataDecl :: Parser Decl
gDataDecl = do
  reserved "data"
  n <- setVar
  pos <- getPosition
  ps <- params
  reserved "where"
  cs <- block cons 
  return $ DataDecl pos (Data n ps cs)
  where cons = do
          c <- termVar
          reservedOp "::"
          t <- ftype
          return (c,t)
        params = option [] $ many1 (try setVar <|> termVar)

termVar :: Parser String
termVar = do
  n <- identifier
  when (null n || isUpper (head n)) $
    unexpected "Term names must begin with an lowercase letter."
  return n

setVar :: Parser String
setVar = do
  n <- identifier
  when (null n || isLower (head n)) $
    unexpected "Set names must begin with an uppercase letter."
  return n

-- parser for FType--
ftype :: Parser FType
ftype = buildExpressionParser ftypeOpTable base

base :: Parser FType
base = try dep <|> try compound <|> parens ftype

depHead = do
  n <- termVar
  reservedOp "::"
  t2 <- ftype
  return (n, t2)

dep = do
  (n, t2) <- parens depHead
  reservedOp "->"
  t1 <- ftype
  return $ Pi n t2 t1
  
compound = do
  n <- setVar
  as <- option [] $ compoundArgs
  if null as then return $ FVar n
    else return $ FCons n as

compoundArgs = 
  many $ indented >>
  ((try (setVar >>= \ n -> return $ ArgType $ FVar n))
  <|> (try (prog >>= \ n -> return $ ArgProg n))
  <|> (try (parens ftype >>= \ n -> return $ ArgType n)))

-- tactic decl ---

tacticDecl :: Parser Decl
tacticDecl = do
  reserved "tactic"
  n <- termVar
  as <- many (try termVar <|> try setVar)
  reservedOp "="
  p <-  try (do{p <- proof;
                notFollowedBy $ reservedOp "=";
                return $ Left p})
        <|>
        (do{ 
            ps <- block $ ( assumption <|> proofDef);
            return $ Right ps})
  return $ TacDecl n as p

-----  Parser for Program ------

progDecl :: Parser Decl
progDecl = do
  n <- try termVar <|> parens operator
  as <- many termVar
  reservedOp "="
  p <- prog
  if (null as) then return $ ProgDecl n p
    else return $ ProgDecl n (Abs as p)

progA :: Parser Prog  
progA = wrapProgPos $ absProg <|> caseTerm <|> appProg <|> parens prog

prog :: Parser Prog
prog = getState >>= \ st -> progParser st

termVarProg :: Parser Prog
termVarProg = termVar >>= \n-> return $ Name n
  
appProg = do
  sp <- termVarProg <|> parens prog
  as <- many $ indented >> (try (parens prog) <|> try termVarProg)
  if null as then return sp
    else return $ foldl' (\ z x -> Applica z x) sp as
         
caseTerm = do
  reserved "case"
  n <- prog
  reserved "of"
  bs <- block branch
  return $ Match n bs
  where
    branch = do
      v <- termVar
      l <- many termVar
      reservedOp "->"
      pr <- prog
      return $ (v, l, pr)

absProg = do
  reservedOp "\\"
  as <- many1 termVar
  reservedOp "."
  p <- prog
  return $ Abs as p

--------------set decl-------------

setDecl :: Parser Decl
setDecl = do
  n <- try setVar <|> parens operator
  as <- many $ try termVar <|> setVar
  reservedOp "="
  s <- try formula <|> set
  if (null as) then return $ SetDecl n s
    else return $ SetDecl n (foldr (\ x z -> Iota x z) s as)

progPre :: Parser PreTerm
progPre = wrapProgPos prog >>= \ p -> return $ progTerm p

termVarPre :: Parser PreTerm
termVarPre = termVar >>= \ n -> return $ PVar n 

setVarPre :: Parser PreTerm
setVarPre = setVar >>= \ n -> return $ PVar n 
  
set :: Parser PreTerm
set = wrapFPos $ iotaClause <|> appClause <|> parens set

iotaClause = do
  reserved "iota"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- formula
  return $ (foldr (\ x z -> Iota x z) f xs)

appClause = do
  n <- setVarPre <|> parens set
  as <- many $ indented >>
         (try setVarPre  <|> try termVarPre <|>
          try (parens progPre) <|> parens set)
  if null as then return n
    else return $ foldl' (\ z x -> helper z x) n as
  where helper z (x@(App _ _)) = TApp z x
        helper z (x@(Lambda _ _)) = TApp z x
        helper z (x@(PVar a)) = if isLower $ head a then TApp z x
                            else SApp z x
        helper z (Pos _ t) = helper z t
        helper z x = SApp z x
        
formula :: Parser PreTerm
formula = getState >>= \st -> wrapFPos $ formulaParser st

atom :: Parser PreTerm
atom = wrapFPos $ try forallClause <|> try inClause <|>
       try appClause <|> parens formula 

forallClause = do
  reserved "forall"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- formula
  return $ (foldr (\ x z -> Forall x z) f xs)

inClause = do
  p <- progPre
  reservedOp "::"
  s <- set
  return $ In p s

------- Parser for Proofs ---------

proofDecl :: Parser Decl
proofDecl = do
  reserved "theorem"
--  emit $ text "processing theorem"
  n <- identifier
  m <- optionMaybe $ brackets identifier
  reservedOp "."
  f <- formula
  reserved "proof"
  ps <- block $ assumption <|> proofDef 
  reserved "qed"
  return $ ProofDecl n m ps f

assumption :: Parser (VName, Proof, Maybe PreTerm)
assumption = do
 a <- brackets termVar
 reservedOp ":"
 f <- formula
 return (a, Assume a, Just f)

proofDef :: Parser (VName, Proof, Maybe PreTerm)
proofDef = do
  b <- termVar
  reservedOp "="
  p <- proof
  f <- option Nothing $
       (do{reservedOp ":";
           g <- formula;
           return $ Just g})
  return (b, p, f)

termVarProof :: Parser Proof
termVarProof = termVar >>= \n-> return $ PrVar n

proof :: Parser Proof
proof = wrapPPos $ cmp <|> mp <|> inst <|>
                  ug <|> beta <|> discharge 
                  <|>invcmp <|> invbeta
                  <|> absProof <|> try appProof <|> (parens proof)
-- invcmp and invbeta are abrieviation
appPreTerm :: Parser (Either PreTerm Proof)
appPreTerm = do
  t <- try (reservedOp "$" >> formula)
       <|> try(reservedOp "$" >> set) <|> try (reservedOp "$" >> progPre)
       
  return $ Left t

appPr :: Parser (Either PreTerm Proof)
appPr = do
  p <- try (parens proof) <|> try termVarProof
  return $ Right p
  
appProof = do
  sp <- try termVarProof <|> parens proof
  as <- many $ indented >> (try appPreTerm <|> try appPr)
  return $ foldl' (\ z x -> helper z x) sp as
    where helper z (Left a) = PFApp z a
          helper z (Right a) = PApp z a

absProof = do
  reserved "\\"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- proof
  return $ (foldr (\ x z -> PLam x z) f xs)

invcmp = do
  reserved "invcmp"
  p <- proof
  f <- try (lookAhead $ reservedOp ":" >> formula) <|> (reserved "from" >> formula)
  return $ InvCmp p f

invbeta = do
  reserved "invbeta"
  p <- proof
  f <- try (lookAhead $ reservedOp ":" >> formula) <|> ( reserved "from" >> formula)
  return $ InvBeta p f

cmp = do
  reserved "cmp"
  p <- proof
  return $ Cmp p

mp = do
  reserved "mp"
  p1 <- proof
  reserved "by"
  p2 <- proof
  return $ MP p1 p2

discharge = do
  reserved "discharge"
  n <- termVar
  f <- option Nothing $
       (do{ reservedOp ":";
            a <- formula;
            return $ Just a})
  reservedOp "."
  p <- proof
  return $ Discharge n f p
  
inst = do
  reserved "inst"
  p <- proof
  reserved "by"
  t <- try progPre <|> try set <|> formula
  return $ Inst p t

ug = do
  reserved "ug"
  m <- try setVar <|> termVar
  reservedOp "."
  p <- proof
  return $ UG m p

beta = do
  reserved "beta"
  p <- proof
  return $ Beta p
  
-----------------------Positions -------
  
wrapFPos :: Parser PreTerm -> Parser PreTerm
wrapFPos p = pos <$> getPosition <*> p
  where pos x (Pos y e) | x==y = (Pos y e)
        pos x y = Pos x y

wrapPPos :: Parser Proof -> Parser Proof
wrapPPos p = pos <$> getPosition <*> p
  where pos x (PPos y e) | x==y = (PPos y e)
        pos x y = PPos x y

wrapProgPos :: Parser Prog -> Parser Prog
wrapProgPos p = pos <$> getPosition <*> p
  where pos x (ProgPos y e) | x==y = (ProgPos y e)
        pos x y = ProgPos x y


-------------------------------

-- Tokenizer definition

gottlobStyle :: (Stream s m Char, Monad m) => Token.GenLanguageDef s u m
gottlobStyle = Token.LanguageDef
                { Token.commentStart   = "{-"
                , Token.commentEnd     = "-}"
                , Token.commentLine    = "--"
                , Token.nestedComments = True
                , Token.identStart     = letter
                , Token.identLetter    = alphaNum <|> oneOf "_'"
                , Token.opStart        = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.opLetter       = oneOf ":!#$%&*+.,/<=>?@\\^|-"
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "forall", "iota", 
                    "cmp","invcmp", "inst", "mp", "discharge", "ug", "beta", "invbeta",
                    "by", "from",
                    "case", "of",
                    "data", 
                    "theorem", "proof", "qed",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic"
                  ]
               , Token.reservedOpNames =
                    ["\\", "->", "|", ".","=", "::", ":", "$", "$$"]
                }

tokenizer :: Token.GenTokenParser String u (State SourcePos)
tokenizer = Token.makeTokenParser gottlobStyle

identifier :: ParsecT String u (State SourcePos) String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u (State SourcePos) ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u (State SourcePos) ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u (State SourcePos) ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u (State SourcePos) String
operator = Token.operator tokenizer

colon :: ParsecT String u (State SourcePos) String
colon = Token.colon tokenizer

integer :: ParsecT String u (State SourcePos) Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
brackets = Token.brackets tokenizer

parens :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
parens  = Token.parens tokenizer

braces :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) a
braces = Token.braces tokenizer

dot :: ParsecT String u (State SourcePos) String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u (State SourcePos) a -> ParsecT String u (State SourcePos) [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u (State SourcePos) String
comma = Token.comma tokenizer

