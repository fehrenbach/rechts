{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Syntax
import Control.Monad (void)
import Data.Text
import Text.Megaparsec
import Text.Megaparsec.Expr
import Text.Megaparsec.Text
import qualified Text.Megaparsec.Lexer as L

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

rws = ["λ"]

identifier :: Parser Text
identifier = pack <$> (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

variable :: Parser Variable
variable = NamedVar <$> identifier

var :: Parser Expr
var = Var <$> variable

fun :: Parser Expr
fun = do
  try (symbol "λ")
  v <- variable
  symbol "."
  e <- expr
  return (Lam v e)

term :: Parser Expr
term =
  fun <|> try var <|> parens expr

wholeExpr :: Parser Expr
wholeExpr = do
  e <- expr
  eof
  return e

expr :: Parser Expr
expr = makeExprParser term table
  where
    table = [ [ InfixL (App <$ return ()) ] ]
