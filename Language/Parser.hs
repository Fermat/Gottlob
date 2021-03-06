{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp, FlexibleContexts #-}
module Language.Parser
       (parseModule) where
import Language.Syntax

import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
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
    proofParser :: IndentParser String ParserState Prog,
    formulaParser :: IndentParser String ParserState Prog,
    progOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Prog],
    proofOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Prog],
    formulaOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Prog]}

initialParserState :: ParserState
initialParserState = ParserState {
  progParser = buildExpressionParser [] progA, 
  proofParser = buildExpressionParser [] proofA, 
  formulaParser = buildExpressionParser initialFormulaOpTable atom,
  progOpTable =  IM.fromAscList (zip [0 ..] [[]]),
  proofOpTable =  IM.fromAscList (zip [0 ..] [[]]),
  formulaOpTable =  IM.fromAscList (zip [0 ..] initialFormulaOpTable)}

initialFormulaOpTable :: [[Operator String u (State SourcePos) Prog]]
initialFormulaOpTable = [[], [], [], [], [], [binOp AssocRight "->" TImply]]

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
  bs <- many gDecl
  eof
  return $ Module modName bs

gDecl :: Parser Decl
gDecl = gDataDecl <|> try proofDecl -- <|> try progDecl
        <|> try setDecl <|> try formOperatorDecl <|> try patternDecl <|>
        progOperatorDecl <|> try tacticDecl <|> proofOperatorDecl
  
formOperatorDecl :: Parser Decl
formOperatorDecl = do
  reserved "formula"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl","pre","post"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r TSApp Name] $ formulaOpTable st
      form' = buildExpressionParser (map snd (IM.toAscList table')) atom
  putState $ ParserState
    (progParser st) (proofParser st) form' (progOpTable st) (proofOpTable st) table'
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
    prog' (proofParser st) (formulaParser st) table' (proofOpTable st) (formulaOpTable st) 
  return (ProgOperatorDecl op level r)

proofOperatorDecl :: Parser Decl
proofOperatorDecl = do
  reserved "proof"
  r <- choice [reserved i >> return i | i <- ["infix","infixr","infixl","pre","post"]]
  level <- fromInteger <$> integer
  op <- operator
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r Applica Name] $ proofOpTable st
      proof' = buildExpressionParser (map snd (IM.toAscList table')) proofA
  putState $ ParserState
    (progParser st) proof' (formulaParser st) (progOpTable st) table' (formulaOpTable st) 
  return (ProofOperatorDecl op level r)

gDataDecl :: Parser Decl
gDataDecl = do
  reserved "data"
  n <- setVar
  pos <- getPosition
  ps <- params
  reserved "where"
  cs <- block cons
  b <- option False $ reserved "deriving" >> reserved "Ind" >> return True
  return $ DataDecl pos (Data n ps cs) b
  where cons = do
          c <- try termVar <|> parens operator
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


-----  Parser for Program ------

patternDecl :: Parser Decl
patternDecl = do 
  n <- try termVar <|> parens operator
  as <- many $ (try (parens prog) <|> try termVarProg)
  reservedOp "="
  p <- prog
  return $ PatternDecl n as p

progDecl :: Parser Decl
progDecl = do
  n <- try termVar <|> parens operator
  as <- many termVar
  reservedOp "="
  p <- prog
  if (null as) then return $ ProgDecl n p
    else return $ ProgDecl n (Abs as p)

progA :: Parser Prog  
progA = wrapPos $ absProg <|> ifprog <|> caseTerm <|> appProg <|> letbind <|> parens prog

prog :: Parser Prog
prog = getState >>= \ st -> progParser st

termVarProg :: Parser Prog
termVarProg = termVar >>= \n-> return $ Name n

setVarProg :: Parser Prog
setVarProg = setVar >>= \n-> return $ Name n

opToProg :: Parser Prog
opToProg = operator >>= \n-> return $ Name n

appProg = do
  sp <- try termVarProg <|> try (parens prog) <|> parens opToProg
  as <- many $ indented >> (try (parens prog) <|> try termVarProg)
  if null as then return sp
    else return $ foldl' (\ z x -> Applica z x) sp as

ifprog = do
  reserved "if"
  cond <- prog
  reserved "then"
  t <- prog
  reserved "else"
  e <- prog
  return $ If cond t e
  
letbind = do
  reserved "let"
  bs <- block branch
  reserved "in"
  p <- prog
  return $ Let bs p
  where branch = do 
          v <- termVar
          reservedOp "="
          p <- prog
          return $ (v, p)
          
caseTerm = do
  reserved "case"
  n <- prog
  reserved "of"
  bs <- block branch
  return $ Match n bs
  where
    branch = do
      v <- try termVar <|> parens operator
      l <- many $ try termVarProg <|> parens appProg
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
    else return $ SetDecl n (foldr (\ x z -> TIota x z) s as)

set :: Parser Prog
set = wrapPos $ iotaClause <|> try appClause <|> parens set

iotaClause = do
  reserved "iota"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- formula
  return $ (foldr (\ x z -> TIota x z) f xs)

appClause = do
  n <- setVarProg <|> parens set
  as <- many $ indented >>
         (try setVarProg  <|> try termVarProg <|>
          try (parens prog) <|> parens set)
  return $ foldl' (\ z x -> helper z x) n as
  where helper z (x@(Applica _ _)) = TSTApp z x
        helper z (x@(Abs _ _)) = TSTApp z x
        helper z (x@(Name a)) = if isLower $ head a then TSTApp z x
                            else TSApp z x
        helper z (ProgPos _ t) = helper z t
        helper z x = TSApp z x
        
formula :: Parser Prog
formula = getState >>= \st -> wrapPos $ formulaParser st

atom :: Parser Prog
atom = wrapPos $ try forallClause <|> try inClause <|>
       try appClause <|> parens formula 

forallClause = do
  reserved "forall"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- formula
  return $ (foldr (\ x z -> TForall x z) f xs)

inClause = do
  p <- prog
  reservedOp "::"
  s <- set
  return $ TIn p s

-- tactic decl ---

tacticDecl :: Parser Decl
tacticDecl = do
  reserved "tactic"
--  unexpected "heiii"
  n <- termVar <|> parens operator
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

assumption :: Parser (VName, Either Assumption Prog, Maybe Prog)
assumption = do
 a <- brackets termVar
 reservedOp ":"
 f <- formula
 return (a, Left $ Assume a, Just f)

proofDef :: Parser (VName, Either Assumption Prog, Maybe Prog)
proofDef = do
  b <- termVar
  reservedOp "="
  p <- proof
  f <- option Nothing $
       (do{reservedOp ":";
           g <- formula;
           return $ Just g})
  return (b, Right p, f)


proof :: Parser Prog
proof = getState >>= \ st -> proofParser st

proofA :: Parser Prog
proofA =  cmp <|> mp <|> inst <|>
         ug <|> beta <|> discharge <|> ifproof
         <|>invcmp <|> invsimp <|> simp <|> invbeta <|> match <|> pletbind
         <|> absProof <|> appProof <|> (parens proof)
-- invcmp and invbeta are abrieviation
appPreTerm :: Parser (Either Prog Prog)
appPreTerm = do
  t <-  try setVarProg <|> try (parens formula) <|> parens set 
--  unexpected "hei"
       -- <|> try (reservedOp "$" >> progPre)
  return $ Left t

appPr :: Parser (Either Prog Prog)
appPr = do
  p <- try (parens proof) <|> try termVarProg <|> parens prog
--  unexpected "well"
  return $ Right p
  
appProof = do
  sp <- try termVarProg <|> try (parens proof) <|> parens opToProg
--  unexpected "here"
  as <- many $ indented >> (try appPr <|> try appPreTerm)
  return $ foldl' (\ z x -> helper z x) sp as
    where helper z (Left a) = AppPre z a
          helper z (Right a) = Applica z a

absProof = do
  reserved "\\"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- proof
  return $ Abs xs f

ifproof = do
  reserved "if"
  cond <- proof
  reserved "then"
  t <- proof
  reserved "else"
  e <- proof
  return $ If cond t e

pletbind = do
  reserved "let"
  bs <- block branch
  reserved "in"
  p <- proof
  return $ Let bs p
  where branch = do 
          v <- termVar
          reservedOp "="
          p <- try proof <|> try prog <|> try formula <|> set
          return $ (v, p)

match = do
  reserved "case"
  n <- prog
  reserved "of"
  bs <- block branch
  return $ Match n bs
  where
    branch = do
      v <- try termVar <|> parens operator
      l <- many $ try termVarProg <|> parens prog
      reservedOp "->"
      pr <- proof
      return $ (v, l, pr)

invcmp = do
  reserved "invcmp"
  p <- proof
  f <- try (lookAhead $ reservedOp ":" >> formula) <|> (reserved "from" >> formula)
  return $ TInvCmp p f

invsimp = do
  reserved "invSimp"
  p <- proof
  f <- try (lookAhead $ reservedOp ":" >> formula) <|> (reserved "from" >> formula)
  return $ TInvSimp p f

invbeta = do
  reserved "invbeta"
  p <- proof
  f <- try (lookAhead $ reservedOp ":" >> formula) <|> ( reserved "from" >> formula)
  return $ TInvBeta p f

cmp = do
  reserved "cmp"
  p <- proof
  return $ TCmp p

simp = do
  reserved "simpCmp"
  p <- proof
  return $ TSimpCmp p

mp = do
  reserved "mp"
  p1 <- proof
  reserved "by"
  p2 <- proof
  return $ TMP p1 p2

discharge = do
  reserved "discharge"
  n <- termVar
  f <- option Nothing $
       (do{ reservedOp ":";
            a <- formula;
            return $ Just a})
  reservedOp "."
  p <- proof
  return $ TDischarge n f p
  
inst = do
  reserved "inst"
  p <- proof
  reserved "by"
  t <- try prog <|> try set <|> formula
  return $ TInst p t

ug = do
  reserved "ug"
  m <- try setVar <|> termVar
  reservedOp "."
  p <- proof
  return $ TUG m p

beta = do
  reserved "beta"
  p <- proof
  return $ TBeta p
  
-----------------------Positions -------
  
wrapPos :: Parser Prog -> Parser Prog
wrapPos p = pos <$> getPosition <*> p
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
                , Token.opLetter       = (oneOf ":!#$%&*+.,/<=>?@\\^|-") <|> alphaNum
                , Token.caseSensitive  = True
                , Token.reservedNames =
                  [
                    "forall", "iota", 
                    "cmp","invcmp", "inst", "mp", "discharge", "ug", "beta", "invbeta",
                    "by", "from", "in", "let", "simpCmp", "invSimp",
                    "case", "of",
                    "data", "if", "then", "else",
                    "theorem", "proof", "qed",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "tactic", "deriving", "Ind"
                  ]
               , Token.reservedOpNames =
                    ["\\", "->", "|", ".","=", "::", ":"]
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

