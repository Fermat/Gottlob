{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp, FlexibleContexts #-}
module Language.Parser where
import Language.Syntax
import Language.Program
import Text.Parsec hiding (ParseError,Empty, State)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import Text.Parsec.Indent
import Control.Applicative hiding ((<|>),many)
import Control.Monad.State.Lazy
import "mtl" Control.Monad.Identity
import qualified Data.IntMap as IM
import Control.Exception(Exception)
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
    specialParser :: IndentParser String ParserState PreTerm,
    progParser :: IndentParser String ParserState Prog,
    formulaParser :: IndentParser String ParserState PreTerm,
    specialOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) PreTerm],
    progOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) Prog],
    formulaOpTable :: IM.IntMap [Operator String ParserState (State SourcePos) PreTerm]
    }

initialParserState :: ParserState
initialParserState = ParserState {
  specialParser = parserZero,
  progParser = buildExpressionParser [] progA, --progPre,
  formulaParser = buildExpressionParser initialFormulaOpTable atom,
  specialOpTable =  IM.fromAscList (zip [0 ..] [[]]),
  progOpTable =  IM.fromAscList (zip [0 ..] [[]]),
  formulaOpTable =  IM.fromAscList (zip [0 ..] initialFormulaOpTable)
  }

initialFormulaOpTable :: [[Operator String u (State SourcePos) PreTerm]]
initialFormulaOpTable =
  [[], [], []
    ,[binOp AssocRight "->" Imply]]
  
-- etypeOpTable :: [[Operator String u (State SourcePos) EType]]
-- etypeOpTable =
--   [[binOp AssocRight "->" To]]

ftypeOpTable :: [[Operator String u (State SourcePos) FType]]
ftypeOpTable =
  [[binOp AssocRight "->" Arrow]]

binOp
  :: Assoc -> String -> (a -> a -> a) -> Operator String u (State SourcePos) a
binOp assoc op f = Infix (reservedOp op >> return f) assoc

postOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
postOp op f = Postfix (reservedOp op >> return f)

preOp :: String -> (a -> a) -> Operator String u (State SourcePos) a
preOp op f = Prefix (reservedOp op >> return f)

deriving instance Typeable P.ParseError
instance Exception P.ParseError where

gModule :: Parser Module
gModule = do
  whiteSpace
  reserved "module"
  modName <- identifier
  reserved "where"
  bs <- many1 gDecl
--  os <- many 
  eof
  return $ Module modName bs

gDecl :: Parser Decl
gDecl =  gDataDecl <|> proofDecl <|> try progDecl
        <|> setDecl <|> formOperatorDecl <|> progOperatorDecl <|>
        specialOperatorDecl



formOperatorDecl :: Parser Decl
formOperatorDecl = do
  reserved "formula"
  r <- choice [reserved i >> return i
               | i <- ["infix","infixr","infixl","pre","post"]
               ]
  level <- fromInteger <$> integer
  op <- operator
  -- update the table
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r] $ formulaOpTable st
      form' = buildExpressionParser (map snd (IM.toAscList table')) atom
  putState $ ParserState (specialParser st) (progParser st) form' (specialOpTable st) (progOpTable st) table'
  return (FormOperatorDecl op level r)
  where toOp op "infix" =
          binOp AssocNone op (binApp op)
        toOp op "infixr" =
          binOp AssocRight op (binApp op)
        toOp op "infixl" =
          binOp AssocLeft op (binApp op)
        toOp op "pre" =
          preOp op (SApp (PVar op))
        toOp op "post" =
          postOp op (SApp (PVar op))
        -- Unreachable, since we guard with 'choice' above...
        toOp _ fx = error (fx ++ " is not a valid operator fixity.")
        binApp op x y = SApp (SApp (PVar op) x) y

progOperatorDecl :: Parser Decl
progOperatorDecl = do
  reserved "prog"
  r <- choice [reserved i >> return i
               | i <- ["infix","infixr","infixl","pre","post"]
               ]
  level <- fromInteger <$> integer
  op <- operator
  -- update the table
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r] $ progOpTable st
      prog' = buildExpressionParser (map snd (IM.toAscList table')) progA
  putState $ ParserState (specialParser st) prog' (formulaParser st) (specialOpTable st) table' (formulaOpTable st) 
  return (ProgOperatorDecl op level r)
  where toOp op "infix" =
          binOp AssocNone op (binApp op)
        toOp op "infixr" =
          binOp AssocRight op (binApp op)
        toOp op "infixl" =
          binOp AssocLeft op (binApp op)
        toOp op "pre" =
          preOp op (Applica (Name op))
        toOp op "post" =
          postOp op (Applica (Name op))
        -- Unreachable, since we guard with 'choice' above...
        toOp _ fx = error (fx ++ " is not a valid operator fixity.")
        binApp op x y = Applica (Applica (Name op) x) y

specialOperatorDecl :: Parser Decl
specialOperatorDecl = do
  reserved "special"
  r <- choice [reserved i >> return i
               | i <- ["infix","infixr","infixl","pre","post"]
               ]
  level <- fromInteger <$> integer
  op <- operator
  -- update the table
  st <- getState
  let table' = IM.insertWith (++) level [toOp op r] $ specialOpTable st
      special' = buildExpressionParser (map snd (IM.toAscList table')) progPre
  putState $ ParserState special' (progParser st) (formulaParser st) table' (progOpTable st) (formulaOpTable st) 
  return (SpecialOperatorDecl op level r)
  where toOp op "infix" =
          binOp AssocNone op (binApp op)
        toOp op "infixr" =
          binOp AssocRight op (binApp op)
        toOp op "infixl" =
          binOp AssocLeft op (binApp op)
        toOp op "pre" =
          preOp op (TApp (PVar op))
        toOp op "post" =
          postOp op (TApp (PVar op))
        -- Unreachable, since we guard with 'choice' above...
        toOp _ fx = error (fx ++ " is not a valid operator fixity.")
        binApp op x y = TApp (TApp (PVar op) x) y

gDataDecl :: Parser Decl
gDataDecl = do
  reserved "data"
  n <- setVar
  ps <- params
  reserved "where"
  cs <- block cons 
  return $ DataDecl (Data n ps cs)
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
    unexpected "Term names must begin with an lowercase letter"
  return n

setVar :: Parser String
setVar = do
  n <- identifier
  when (null n || isLower (head n)) $
    unexpected "Set names must begin with an uppercase letter"
  return n

-- parser for FType--
ftype :: Parser FType
ftype = buildExpressionParser ftypeOpTable base

base :: Parser FType
base = compound <|> try dep <|> parens ftype

dep = do
  (x,t) <- parens $ do{
    n <- termVar;
    reservedOp "::";
    t2 <- ftype ;
    return (n,t2)
    }
  reservedOp "->"
  t1 <- ftype
  return $ Pi x t t1
  
compound = do
  n <- setVar
  as <- option [] $ compoundArgs
  if null as then
    return $ FVar n 
    else 
    return $ FCons n as

compoundArgs = 
  many $ indented >>
  (try (do{ n <- setVar;
       return $ ArgType $ FVar n})
  <|>
  (try (do{ n <- prog;
       return $ ArgProg n}))
  <|> (try (do{ n <- parens ftype;
            return $ ArgType n})))

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
progA = absProg <|> caseTerm <|> appProg <|> parens prog

prog :: Parser Prog
prog = do
  st <- getState
  progParser st

termVarProg :: Parser Prog
termVarProg = do
  n <- termVar
  return $ Name n
  
appProg = do
  sp <- termVarProg <|> parens prog
  as <- many $ indented >>
        (parens prog <|>
         (do{x <- termVar;
             return $ Name x}))
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
    else return $
         SetDecl n (foldr (\ x z -> Iota  x z) s as)

progPre :: Parser PreTerm
progPre = do
  p <- prog
  return $ progTerm p

setVarPre :: Parser PreTerm
setVarPre = do
  n <- setVar
  return $ PVar n 
  
set :: Parser PreTerm
set = iotaClause <|> appClause <|> parens set

iotaClause = do
  reserved "iota"
  xs <- many1 $ try termVar <|> setVar
  reservedOp "."
  f <- formula
  return $ (foldr (\ x z -> Iota  x z) f xs)

appClause = do 
  n <- setVarPre <|> parens set
  as <- many $ indented >>
         (try setVarPre  <|> try progPre <|>
          parens set)
  if null as then return n
    else return $ foldl' (\ z x -> helper z x) n as
  where helper z x = if isTerm x then TApp z x
                     else SApp z x

formula :: Parser PreTerm
formula = do
  st <- getState
  formulaParser st


atom :: Parser PreTerm
atom = forallClause <|> try inClause
       <|> try appClause <|> parens formula <|>
       try special

special = do
  st <- getState
  (parens $ specialParser st) <|> specialParser st
  
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
  n <- identifier
  reservedOp "."
  f <- formula
  reserved "proof"
  ps <- block $ assumption <|> proofDef 
  reserved "qed"
  return $ ProofDecl n ps f

assumption :: Parser (VName, Proof, PreTerm)
assumption = do
 a <- brackets termVar
 reservedOp ":"
 f <- formula
 return (a, Assume a, f)

proofDef :: Parser (VName, Proof, PreTerm)
proofDef = do
  b <- termVar
  reservedOp "="
  p <- proof
  reservedOp ":"
  f <- formula
  return (b, p, f)

proof :: Parser Proof
proof = var <|> cmp <|> mp <|> inst <|>
        ug <|> beta <|> discharge <|> parens proof
        <|>invcmp <|> invbeta
-- invcmp and invbeta are abrieviation
invcmp = do
  reserved "invcmp"
  p <- proof
  f <- lookAhead $ reservedOp ":" >> formula
  return $ InvCmp p f

invbeta = do
  reserved "invbeta"
  p <- proof
  f <- lookAhead $ reservedOp ":" >> formula
  return $ InvBeta p f

var = do
  v <- termVar
  return $ PrVar v
  
cmp = do
  reserved "cmp"
  p <- proof
  return $ Cmp p


mp = do
  reserved "mp"
  p1 <- proof
  p2 <- proof
  return $ MP p1 p2

discharge = do
  reserved "discharge"
  n <- termVar
  p <- proof
  return $ Discharge n p
  
inst = do
  reserved "inst"
  p <- proof
  t <- try progPre <|> try set <|> formula
  return $ Inst p t

ug = do
  reserved "ug"
  m <- try setVar <|> termVar
  p <- proof
  return $ UG m p

beta = do
  reserved "beta"
  p <- proof
  return $ Beta p


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
                    "case", "of",
                    "data", 
                    "theorem", "proof", "qed",
                    "show",
                    "where", "module",
                    "infix", "infixl", "infixr", "pre", "post",
                    "formula", "prog", "set",
                    "special"
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

