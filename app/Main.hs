{-# LANGUAGE OverloadedStrings, TupleSections #-}

module Main where

import Prelude hiding (getLine, readFile)
import Data.Text.IO (getLine, readFile)
import Syntax
import Parser
import Pretty (printValue, printCode)
import Data.Monoid
import Data.Text
import Data.Either.Unwrap (fromRight)
import System.Environment (getArgs)
import qualified Data.Map.Lazy as Map
import qualified Data.Vector as V
import Text.Megaparsec (runParser, ParsecT(..), runParserT', State(..), runParserT, parseErrorPretty)
import System.IO (hFlush, stdout)
import Control.Monad.State.Strict (evalStateT, runStateT)

eval :: Env -> Expr -> Either String Value
eval _ (Val v) = Right v
eval env (Var v) = case Map.lookup v env of
  Just v -> Right v
  Nothing -> Left $ "Unbound variable " ++ show v
eval env (Lam v e) = Right (VFun v env e)
eval env (Eq l r) = do
  l <- eval env l
  r <- eval env r
  return (VBool (l == r))
eval env (If c t e) = do
  VBool c <- eval env c
  if c
    then eval env t
    else eval env e
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
eval env (List es) = do
  vs <- traverse (eval env) es
  return (VVector vs)
eval env (Union l r) = do
  (VVector ls) <- eval env l
  VVector rs <- eval env r
  return (VVector $ ls V.++ rs)
eval env (For x l e) = case eval env l of
  Right (VVector l) ->
    let vs = traverse (\v -> 
                          case eval (Map.insert x v env) e of
                            Right (VVector r) -> Right r
                            Right x -> Left $ "body of a for comprehension did not return a list: " ++ show x
                            Left e -> Left $ "Error in for comprehension: " ++ show e
                      ) l
    in VVector . V.concat . V.toList <$> vs
  Right v -> Left $ "The expression to iterate over did not evaluate to a list: " ++ show v
  Left err -> Left $ "Some error in for body: " ++ err
eval env (PrependPrefix l r) = do
  (VText l) <- eval env l
  (VText r) <- eval env r
  return (VText $ l <> "/" <> r)

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
reflect (Eq l r) = Tag "Eq" (Record (Map.fromList [ ("left", reflect l)
                                                  , ("right", reflect r) ]))
reflect (If c t e) = Tag "If" (Record (Map.fromList [ ("condition", reflect c)
                                                    , ("then", reflect t)
                                                    , ("else", reflect e) ]))
reflect (For v l e) = Tag "For" (Record (Map.fromList [ ("var", Val (VText (pack (show v))))
                                                      , ("in", reflect l)
                                                      , ("body", reflect e) ]))

tr :: Expr -> Text -> Expr -> Either a Expr
tr v c t =
  Right (Record (Map.fromList [("v", v), ("t", Tag c t)]))

unit :: Expr
unit = Record (Map.fromList [])

rec :: [(Text, Expr)] -> Expr
rec = Record . Map.fromList

trace :: Expr -> Either String Expr
trace (Val e)   = tr (Val e) "Val" unit
trace (Var v)   = tr (Var v) "Var" (Val (VText (pack (show v)))) -- Ugh?
trace (Lam v e) = tr (Lam v e) "Lam" (rec [ ("var", Val (VText (pack (show v))))
                                          , ("body", reflect e) ])
trace (Eq l r) = do
  lt <- trace l
  rt <- trace r
  tr (Eq l r) "Eq" (rec [ ("left", Proj "t" lt)
                        , ("right", Proj "t" rt)])
trace (If c t e) = do
  ct <- trace c
  tt <- trace t
  et <- trace e
  tr (If c (Proj "v" tt)
           (Proj "v" et))
    "If"
    (rec [ ("condition", Proj "t" ct)
         , ("branch", Proj "t" (If c tt et)) ])
trace (App f x) = do
  ft <- trace f
  xt <- trace x
  tr (App (Proj "v" ft) (Proj "v" xt)) "App" (rec [("fun", Proj "t" ft), ("arg", Proj "t" xt)])
trace (Record flds) = do
  fldst <- Map.traverseWithKey (\l e -> Proj "t" <$> trace e) flds
  fldsv <- Map.traverseWithKey (\l e -> Proj "v" <$> trace e) flds
  tr (Record fldsv) "Record" (Record fldst)
trace (Proj l e) = do
  te <- trace e
  tr (Proj l (Proj "v" te)) "Proj" (rec [ ("lab", Val (VText l))
                                        , ("rec", Proj "t" te) ])
trace (Tag t e) = do
  te <- trace e
  tr (Tag t e) "Tag" (rec [ ("tag", Val (VText t))
                          , ("val", Proj "t" te) ])
trace (Switch e cases) = do
  te <- trace e
  casesv <- traverse (\(v, c) -> case trace c of
                                   Right tc -> Right (v, Proj "v" tc)
                                   Left err -> Left err)
            cases
  cases' <- Map.traverseWithKey (\t (v, c) -> case trace c of
                                    Right tc -> Right $ (v, Tag "Switch" (Record (Map.fromList [ ("arg", Proj "t" te) -- the switched value
                                                                                               , ("tag", Val (VText t))  -- matching tag
                                                                                               , ("var", Val (VText (pack (show v))))  -- the variable
                                                                                               , ("case", reflect c) ]))) -- the case that matched (reflected)
                                    Left err -> Left err
                                    ) cases
  return (Record (Map.fromList [ ("v", Switch (Proj "v" te) casesv)
                               , ("t", Switch e cases') ]))
trace (List es) = do
  tes <- traverse trace es
  let labelledValues = V.imap (\i x -> Record (Map.fromList [("p", Val (VText (pack (show i)))), ("v", x)])) es
  let labelledTraces = V.imap (\i e -> Record (Map.fromList [("p", Val (VText (pack (show i)))), ("e", e)])) tes
  let plain = V.map id tes
  tr (List labelledValues) "List" (List labelledTraces)
  -- return (Tag "List" (List plain))
trace (Union l r) = do
  lt <- trace l
  rt <- trace r
  tr (Union (For (GeneratedVar 100) (Proj "v" lt)
             (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (Val (VText "l")) (Proj "p" (Var (GeneratedVar 100)))),
                                                       ("v", Proj "v" (Var (GeneratedVar 100)))])))))
      (For (GeneratedVar 101) (Proj "v" rt)
        (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (Val (VText "r")) (Proj "p" (Var (GeneratedVar 101)))),
                                                  ("v", Proj "v" (Var (GeneratedVar 101)))]))))))
       "Union"
       (rec [("left", Proj "t" lt), ("right", Proj "t" rt)])
trace (For x l b) = do
  tl <- trace l
  y <- Right $ GeneratedVar 201
  z <- Right $ GeneratedVar 202
  tb <- trace b
  tr (For y (Proj "v" tl)
       (For z (Proj "v" (App (Lam x tb) (Proj "v" (Var y))))
         (List (V.singleton (Record (Map.fromList [ ("p", PrependPrefix (Proj "p" (Var z)) (Proj "p" (Var y)))
                                                  , ("v", Proj "v" (Var z)) ]))))))
     "For" (rec [ ("in", Proj "t" tl)
                , ("body", reflect b)
                , ("var", Val (VText (pack (show x))))
                , ("out", For y (Proj "v" tl)
                            (List (V.singleton (Record (Map.fromList [ ("p", Proj "p" (Var y))
                                                                     , ("t", Proj "t" (App (Lam x tb) (Proj "v" (Var y))))])))))
                ]) 

-- This is a huge fucking mess :( I think I actually might want some
-- sort of über-monad for my state and env and whatnot to live in

repl env pstate = do
  putStr "rechts> "
  hFlush stdout
  l <- getLine
  case runParser (runStateT wholeExpr pstate) "REPL" l of
    Left err -> putStrLn (parseErrorPretty err)
    Right (e, pstate) -> do
      putStrLn (show e)
      case eval env e of
        Left err -> putStrLn ("ERROR: " ++ show err)
        Right v -> do printValue stdout v
                      putStrLn ""
                      case trace e of
                        Left err -> putStrLn ("TRACE REWRITING ERROR: " ++ show err)
                        Right t -> do printCode stdout t
                                      putStrLn ""
                                      case eval env t of -- Not sure about this env here. Should this be a traced env?
                                        Left err -> putStrLn ("TRACED EVALUATION ERROR: " ++ show err)
                                        Right v -> do printValue stdout v
                                                      putStrLn ""
                                                      repl env pstate

sLoop :: Env -> [Stmt] -> IO (Either String Env)
sLoop env s = case s of
  [] -> return (Right env)
  ((Binding v e):rest) ->
    let val = eval (Map.insert v (fromRight val) env) e
    in case val of
      Left e -> return (Left e)
      Right val -> sLoop (Map.insert v val env) rest
  ((Statement e):rest) ->
    case eval env e of
      Left e -> return (Left e)
      Right val -> do
        printValue stdout val
        putStrLn ""
        sLoop env rest

main :: IO ()
main = do
  fileName <- (!! 0) <$> getArgs
  fileContents <- readFile fileName
  case runParser (runStateT toplevel 0) fileName fileContents of
    Left err -> putStrLn (parseErrorPretty err)
    Right (statements, varCount) -> do
      env <- sLoop (Map.fromList []) statements
      case env of
        Left err -> putStrLn ("Error during file evaluation: " ++ show err)
        Right env -> repl env varCount
