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
eval env (Record fields) =
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
eval env (Union l r) = do
  (VVector ls) <- eval env l
  VVector rs <- eval env r
  return (VVector $ (V.map (\(l, v) -> (PLeft l, v)) ls V.++ V.map (\(l, v) -> (PRight l, v)) rs))
eval env (For x l e) = case eval env l of
  Right (VVector l) ->
    let vs = traverse id $ V.map (\(p, v) -> 
                                     case eval (Map.insert x v env) e of
                                       Right (VVector r) -> Right (V.map (\(rl, v) -> (rl <> p, v)) r)
                                       Right x -> Left $ "body of a for comprehension did not return a list: " ++ show x
                                       Left e -> Left $ "Error in for comprehension: " ++ show e
                                 ) l
    in VVector . V.concat . V.toList <$> vs
  _ -> Left "Something in FOR went wrong"

reflect :: Expr -> Expr
reflect (Val v) = Tag "Val" (Val v)
reflect (Var v) = Tag "Var" (Val (VText (pack (show v)))) -- need a better rep for this
reflect (Lam v e) = Tag "Lam" (Record (Map.fromList [ ("var", Val (VText (pack (show v)))) -- need a better rep for this
                                                    , ("body", reflect e) ]))
reflect (App f a) = Tag "App" (Record (Map.fromList [ ("f", reflect f), ("x", reflect a) ]))
reflect (Record flds) = Tag "Record" (Record (Map.map reflect flds))
reflect (Proj l e) = Tag "Proj" (Record (Map.fromList [ ("l", Val (VText l))
                                                      , ("r", reflect e) ])) -- call "w" for "consistency"?
reflect (Tag t e) = Tag "Tag" (Record (Map.fromList [ ("t", Val (VText t))
                                                    , ("v", reflect e) ]))
reflect (Switch e cs) = Tag "Switch" (Record (Map.fromList [ ("e", reflect e)
                                                           , ("cs", cases) ]))
  where
    cases :: Expr
    cases = List (V.fromList (Map.elems (Map.mapWithKey (\t (v, c) ->
                                                            Record (Map.fromList [ ("t", Val (VText t))
                                                                                 , ("v", Val (VText (pack (show v))))
                                                                                 , ("c", reflect c) ])) cs)))
reflect (List es) = Tag "List" (List (V.map reflect es))

trace :: Expr -> Either String Expr
trace (Val e)   = Right $ Tag "Val" (Val e)
trace (Var v)   = Right $ reflect (Var v)
trace (Lam v e) = Right $ Tag "Lam" (Record (Map.fromList [ ("var", Val (VText (pack (show v)))) -- factor out
                                                          , ("body", reflect e) ]))
trace (App f a) = do
  f <- trace f
  a <- trace a
  return (Tag "App" (Record (Map.fromList [ ("f", f), ("x", a) ])))
trace (Record flds) = do
  flds <- Map.traverseWithKey (\l e -> trace e) flds
  return (Tag "Record" (Record flds))
-- Since we currently don't allow dynamic labels (not clear how to do
-- on DB) and don't have any other record metaprogramming, we might
-- want to put the result here, too. It's not that easy though.
-- putting `te` fails, because the value will be wrapped by some trace tag
-- putting `e` works, but returns the result, not a traced result
trace (Proj l e) = do
  te <- trace e
  return $ Tag "Proj" (Record (Map.fromList [ ("l", (Val (VText l)))
                                            , ("w", te) -- whole record trace
                                            -- , ("r", (Proj l ???))
                                            ]))
trace (Tag t e) = do
  e <- trace e
  return (Tag "Tag" (Record (Map.fromList [ ("t", (Val (VText t)))
                                          , ("v", e) ])))
-- So, the idea is that we emit a switch where each case emits the actual trace structure.
-- I feel like there is something missing though.
trace (Switch e cases) = do
  te <- trace e
  cases' <- Map.traverseWithKey (\t (v, c) -> case trace c of
                                    Right tc -> Right $ (v, Tag "Switch" (Record (Map.fromList [ ("s", te) -- the switched value
                                                                                               , ("t", Val (VText t))  -- matching tag
                                                                                               , ("v", Val (VText (pack (show v))))  -- the variable
                                                                                               , ("c", reflect c) ]))) -- the case that matched (reflected)
                                    Left err -> Left err
                                    ) cases
  return (Switch e cases')
trace (List es) = do
  tes <- traverse trace es
  return (Tag "List" (List tes))
trace (Union l r) = do
  l <- trace l
  r <- trace r
  return $ Tag "Union" (Record (Map.fromList [ ("l", l), ("r", r) ]))
trace (For x l b) = do
  tl <- trace l
  return $ For x l (List (V.singleton (Val (VText "tracing body"))))

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
                          case trace e of
                            Left err -> putStrLn ("TRACE REWRITING ERROR: " ++ show err)
                            Right t -> do putStrLn (show t)
                                          case eval (Map.fromList []) t of
                                            Left err -> putStrLn ("TRACED EVALUATION ERROR: " ++ show err)
                                            Right v -> do printValue stdout v
                                                          putStrLn ""
      loop
