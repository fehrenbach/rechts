{-# LANGUAGE OverloadedStrings #-}

module Main where

import Prelude hiding (getLine)
import Syntax
import Parser
import Pretty (printValue)
import Data.Text
import Data.Text.IO (getLine)
import qualified Data.Map.Strict as Map
import Text.Megaparsec (runParser)
import System.IO (hFlush, stdout)
import Control.Monad.State.Strict (evalStateT)

eval :: Env -> Expr -> Either String Value
eval _ (Val v) = Right v
eval env (Var v) = case Map.lookup v env of
  Just v -> Right v
  Nothing -> Left $ "Unbound variable " ++ show v
eval env (Lam v e) = Right (VFun v env e)
eval env (App f x) =
  case (eval env f, eval env x) of
    (Right (VFun var env f), Right x) -> eval (Map.insert var x env) f
    (_, _) -> Left "error in function application"
eval env (Rec fields) =
  either Left (Right . VRecord) (traverse (eval env) fields)
eval env (Proj l r) =
  case eval env r of
    Right (VRecord v) -> case Map.lookup l v of
      Nothing -> Left $ "Record " ++ show v ++ " does not have label " ++ unpack l
      Just f -> Right f
    Right v -> Left $ "Not a record: " ++ show v
    e -> e
eval env (Tag t e) = do
  e' <- eval env e
  return (VTagged t e')

main :: IO ()
main = loop
  where
    loop = do
      putStr "rechts> "
      hFlush stdout
      l <- getLine
      case runParser (evalStateT wholeExpr 0) "stdin" l of
        Left err -> putStrLn (show err)
        Right e -> do
          putStrLn (show e)
          case eval (Map.fromList []) e of
            Left err -> putStrLn ("ERROR: " ++ show err)
            Right v -> do printValue stdout v
                          putStrLn ""
      loop
