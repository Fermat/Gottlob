{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, PackageImports,ParallelListComp #-}
module Language.Parser where
import Language.Syntax
import Text.Parsec hiding (ParseError,Empty)
import qualified Text.Parsec as P
import Text.Parsec.Language
import Text.Parsec.Expr(Operator(..),Assoc(..),buildExpressionParser)
import qualified Text.Parsec.Token as Token
import "mtl" Control.Monad.Identity
import qualified Data.IntMap as IM
import Control.Exception(Exception)
import Data.Typeable
-- parseModule :: String -> String -> Either P.ParseError Module
-- parseModule srcName cnts = runParser gModule initialParserState srcName cnts

-- User state, so that we can update the operator parsing table.
data ExprParserState =
  ExprParserState {
    exprParser :: Parsec String ExprParserState Meta,
    exprOpTable :: IM.IntMap [Operator String ExprParserState Identity Meta]
    }


deriving instance Typeable P.ParseError
instance Exception P.ParseError where

type Parser a = ParsecT String ExprParserState Identity a

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
gDecl = gDataDecl 

gDataDecl  :: Parser Decl
gDataDecl = do
  reserved "data"
  n <- consName
  ps <- params
  reservedOp "="
  cs <- sepBy cons (reservedOp "|")  <?> "Constructor declaration"
  return $ DataDecl (Data n ps cs)
  where cons = do
          c <- constructor
          reservedOp "::"
          t <- ftype
          return (c,t)
        params = option Empty $ do
          ps <- many1 defaultVar
          return ps

defaultVar :: ParsecT String u Identity (VName,EType)
defaultVar = do
  n <- identifier
  if isLower (head n) then return $ (n, Ind)
    else return $ (n, To Ind Form)
         
consName :: ParsecT String u Identity String
consName = do
  n <- identifier
  when (null n || isLower (head n)) $
       unexpected "Data names must begin with an uppercase letter"
  return n

constructor :: Parser String
constructor = do
  n <- identifier
  when (null n || isUpper (head n)) $
    unexpected "Term names must begin with an lowercase letter"

expr :: Parser FType
expr = do
  st <- getState
  wrapPos $ exprParser st



-- Tokenizer definition
gottlobStyle :: GenLanguageDef String u Identity
gottlobStyle = haskellStyle {
           Token.reservedNames = [
            "forall",
            "cmp","invcmp", "inst", "mp", "discharge", "ug", 
            "case", "of",
            "data", 
            "theorem", "proof",
            "show"
           ],
           Token.reservedOpNames = ["\\", "->", "|", ".","=", "::", ":"]
           }


tokenizer :: Token.GenTokenParser String u Identity
tokenizer = Token.makeTokenParser gottlobStyle

identifier :: ParsecT String u Identity String
identifier = Token.identifier tokenizer

whiteSpace :: ParsecT String u Identity ()
whiteSpace = Token.whiteSpace tokenizer

reserved :: String -> ParsecT String u Identity ()
reserved = Token.reserved tokenizer

reservedOp :: String -> ParsecT String u Identity ()
reservedOp = Token.reservedOp tokenizer

operator :: ParsecT String u Identity String
operator = Token.operator tokenizer

colon :: ParsecT String u Identity String
colon = Token.colon tokenizer

integer :: ParsecT String u Identity Integer
integer = Token.integer tokenizer

brackets :: ParsecT String u Identity a -> ParsecT String u Identity a
brackets = Token.brackets tokenizer

parens :: ParsecT String u Identity a -> ParsecT String u Identity a
parens  = Token.parens tokenizer

braces :: ParsecT String u Identity a -> ParsecT String u Identity a
braces = Token.braces tokenizer

dot :: ParsecT String u Identity String
dot = Token.dot tokenizer

commaSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
commaSep1 = Token.commaSep1 tokenizer

semiSep1 :: ParsecT String u Identity a -> ParsecT String u Identity [a]
semiSep1 = Token.semiSep1 tokenizer

comma :: ParsecT String u Identity String
comma = Token.comma tokenizer

