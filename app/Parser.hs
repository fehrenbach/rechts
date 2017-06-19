{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Syntax
import Control.Monad (void)
import Control.Monad.State.Strict
import Data.Text
import Data.Functor.Identity (Identity)
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Text as MPT
import Data.Char (GeneralCategory(..))
import qualified Text.Megaparsec.Lexer as L
import qualified Data.Map.Strict as Map

type Parser = StateT Int MPT.Parser

sc :: Parser ()
sc = L.space (void spaceChar) lineCmnt blockCmnt
  where lineCmnt  = L.skipLineComment "//"
        blockCmnt = L.skipBlockComment "/*" "*/"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

rws = ["λ", "switch", "case"]

identifier :: Parser Text
identifier = pack <$> (lexeme . try) (p >>= check)
  where
    p       = (:) <$> charCategory LowercaseLetter <*> many alphaNumChar
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

tag :: Parser Text
tag = pack <$> (lexeme . try) p
  where p = (:) <$> charCategory UppercaseLetter <*> many alphaNumChar

variable :: Parser Variable
variable = NamedVar <$> identifier

var :: Parser Expr
var = Var <$> variable

fun :: Parser Expr
fun = do
  try $ symbol "λ" <|> symbol "\\"
  v <- variable
  symbol "."
  e <- expr
  return (Lam v e)

int :: Parser Value
int = VInt . fromInteger <$> L.signed sc L.integer -- this allows spaces between - and the number. Not really sure I want that...

constant :: Parser Expr
constant = Val <$> (try int)

term :: Parser Expr
term =
  constant <|> fun <|> record <|> try var <|> constructor <|> parens expr

wholeExpr :: Parser Expr
wholeExpr = do
  e <- expr
  eof
  return e

expr :: Parser Expr
expr = makeExprParser term table
  where
    table = [ [ Postfix (do symbol "."
                            l <- identifier
                            return (Proj l)) ]
            , [ InfixL (App <$ return ()) ]
            ]

record :: Parser Expr
record = (Rec . Map.fromList) <$> between (symbol "{") (symbol "}") (sepBy labelExprPair (symbol ","))
  where
    labelExprPair = do
      l <- identifier
      symbol "="
      e <- expr
      return (l, e)

freshVar :: StateT Int (ParsecT Dec Text Identity) Variable
freshVar = do
  s <- get
  put (s+1)
  return (GeneratedVar s)

constructor :: Parser Expr
constructor = do
  n <- tag
  v <- freshVar
  return (Lam v (Tag n (Var v)))
