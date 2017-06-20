{-# LANGUAGE OverloadedStrings, TupleSections #-}

module Main where

import Prelude hiding (getLine)
import Syntax
import Parser
import Pretty (printValue)
import Data.Monoid
import Data.Text
import Data.Text.IO (getLine)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
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
eval env (Switch e cases) = do
  (VTagged l v) <- eval env e
  case Map.lookup l cases of
    Nothing -> Left "No match in case"
    Just (var, e) -> eval (Map.insert var v env) e
eval env (List e) =
  (VVector <$>) <$> traverse id $ V.imap (\i e -> do
                                       v <- (eval env) e
                                       return (PList i PEmpty, v)) e
  -- v <- eval env e
  -- return (VVector (V.singleton (PEmpty, v)))
eval env (Union l r) = do
  (VVector ls) <- eval env l
  VVector rs <- eval env r
  return (VVector $ (V.map (\(l, v) -> (PLeft l, v)) ls V.++ V.map (\(l, v) -> (PRight l, v)) rs))
eval env (For x l e) = case eval env l of
  Right (VVector l) ->
    let vs = traverse id $ V.map (\(p, v) -> do
                                     (VVector r) <- eval (Map.insert x v env) e
                                     return (V.map (\(rl, v) -> (rl <> p, v)) r)
                                 ) l
    in VVector . V.concat . V.toList <$> vs
    -- fmap VVector (traverse 
  _ -> Left "Something in FOR went wrong"

-- _ :: V.Vector (Either String (Prefix, Value)) -> Either String Value
-- V.Vector (Either String (Prefix, Value)) -> Either String (Prefix, Value)
-- Either String (V.Vector (Prefix, Value)) -> Either String Value

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
