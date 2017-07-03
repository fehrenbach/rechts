{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Syntax
import Control.Monad (void)
import Control.Monad.State.Strict
import Data.Text (Text, pack, unpack)
import Data.Functor.Identity (Identity)
import Text.Megaparsec
import Text.Megaparsec.Expr
import qualified Text.Megaparsec.Text as MPT
import Data.Char (GeneralCategory(..))
import qualified Text.Megaparsec.Lexer as L
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

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

rws = ["λ", "switch", "case", "if", "then", "else", "trace", "prefixOf", "strip", "rmap", "with" ]

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

stringLit :: Parser Value
stringLit = VText . pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

constant :: Parser Expr
constant = Val <$> (int <|> stringLit) <* sc

term :: Parser Expr
term =
  try constant <|> fun <|> record <|> list <|> switch <|> for <|> trace <|> try var <|> constructor <|> ifthenelse <|> rmap <|> parens expr

trace :: Parser Expr
trace = do
  try $ symbol "trace"
  e <- expr
  return (Trace e)

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
                            return (Proj l))
              , Postfix (do symbol "!"
                            l <- variable
                            return (DynProj l)) ]
            , [ InfixL (App <$ return ()) ]
            , [ InfixN (Eq <$ symbol "==") ]
            , [ InfixR (And <$ symbol "&&") ]
            , [ InfixR (Union <$ symbol "++") ]
            , [ InfixN (PrefixOf <$ symbol "prefixOf" )
              , InfixN (StripPrefix <$ symbol "strip") ]
            ]

record :: Parser Expr
record = (Record . Map.fromList) <$> between (symbol "{") (symbol "}") (sepBy labelExprPair (symbol ","))
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

switch :: Parser Expr
switch = do
  try $ symbol "switch"
  e <- expr
  cases <- many case_
  return (Switch e (Map.fromList cases))
 where
   case_ = do
     symbol "case"
     l <- tag
     v <- variable
     symbol "=>"
     e <- expr
     return (l, (v, e))

list :: Parser Expr
list = do
  l <- between (symbol "[") (symbol "]") (sepBy expr (symbol ","))
  return (List (V.fromList l))

for :: Parser Expr
for = do
  try $ symbol "for"
  symbol "("
  v <- variable
  symbol "<-"
  l <- expr
  symbol ")"
  b <- expr
  return (For v l b)

ifthenelse :: Parser Expr
ifthenelse = do
  try $ symbol "if"
  c <- expr
  symbol "then"
  t <- expr
  symbol "else"
  e <- expr
  return (If c t e)

rmap :: Parser Expr
rmap = do
  try $ symbol "rmap"
  r <- expr
  symbol "with"
  symbol "("
  k <- variable
  symbol "="
  v <- variable
  symbol ")"
  symbol "=>"
  e <- expr
  return (RecordMap r k v e)

binding :: Parser Stmt
binding = do
  v <- variable
  symbol "="
  e <- expr
  symbol ";"
  return (Binding v e)

statement :: Parser Stmt
statement = do
  e <- expr
  symbol ";"
  return (Statement e)

toplevel :: Parser [Stmt]
toplevel = some (try binding <|> statement) <* eof
