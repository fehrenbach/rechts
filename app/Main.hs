{-# LANGUAGE OverloadedStrings #-}

module Main where

import Syntax
import Parser
import Data.Text
import qualified Data.Map.Strict as Map
import Text.Megaparsec (parseTest)

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

i :: Expr
i = Lam (NamedVar "x") (Var (NamedVar "x"))

main :: IO ()
main = do
  parseTest expr "(λy.y y)(λx.x x)" -- why doesn't this work?
  putStrLn (show (eval (Map.fromList []) (Var (NamedVar "foo"))))
  putStrLn (show (eval (Map.fromList []) (App i i)))
  putStrLn (show (eval (Map.fromList []) (App (App i i) (Val (VInt 5)))))
