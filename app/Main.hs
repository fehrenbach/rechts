{-# LANGUAGE OverloadedStrings, TupleSections #-}

module Main where

import Prelude hiding (getLine, readFile)
import Data.Text.IO (getLine, readFile)
import Syntax
import Parser (wholeExpr, toplevel)
import Pretty (printCode)
import Data.Monoid
import Data.Text (Text, concat, pack, unpack, splitOn, isPrefixOf)
import qualified Debug.Trace as T
import Data.Either.Unwrap (fromRight)
import System.Environment (getArgs)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Text.Megaparsec (runParser, ParsecT(..), runParserT', State(..), runParserT, parseErrorPretty)
import System.IO (hFlush, stdout)
import Control.Monad.State.Strict (evalStateT, runStateT)

-- TODO decide what the proper primitive should be
-- Currently this is by length only, which seems either overkill or dangerous, or both
-- So far I only drop a one element, always matching prefix
-- We could just have a dropOnePrefix primitive, or use the argument to check that it is applied correctly.
doStripPrefix :: Text -> Text -> Text
doStripPrefix p l =
  Data.Text.concat $ Prelude.drop (Prelude.length (splitOn "⋅" p)) (splitOn "⋅" l)

eval :: Env -> Expr -> Either String Expr
eval env (VBool b) = Right (VBool b)
eval env (VInt i) = Right (VInt i)
eval env (VText s) = Right (VText s)
eval env (Var v) = case Map.lookup v env of
  Just v -> Right v
  Nothing -> Left $ "Unbound variable " ++ show v
eval env (Lam v e) =
  Right (Closure v env e)
eval env (Eq l r) = do
  l <- eval env l
  r <- eval env r
  return (VBool (l == r))
eval env (And l r) = do
  (VBool l) <- eval env l
  (VBool r) <- eval env r
  return (VBool (l && r))
eval env (If c t e) = do
  VBool c <- eval env c
  if c
    then eval env t
    else eval env e
eval env (App f x) =
  case (eval env f, eval env x) of
    (Right (Closure var fenv body), Right x) -> eval (Map.insert var x fenv) body
    (Right notafunction, Right arg) -> Left $ "Tried to apply something that is not a closure"
    (Left err, _) -> Left err
    (_, Left err) -> Left err
    (_, _) -> Left "error in function application"
eval env (Record fields) =
  Record <$> traverse (eval env) fields
eval env (Proj l r) =
  case eval env r of
    Right (Record v) -> case Map.lookup l v of
      Nothing -> Left $ "Record " ++ show v ++ " does not have label " ++ unpack l
      Just f -> Right f
    Right v -> Left $ "Not a record: " ++ show v
    e -> e
eval env (Tag t e) = do
  e' <- eval env e
  return (Tag t e')
eval env (Switch e cases) = do
  tv@(Tag l v) <- eval env e
  case Map.lookup l cases of
    Nothing -> Left $ "No match in case -- matched value: " ++ show tv ++ " cases: " ++ show cases
    Just (var, e) -> eval (Map.insert var v env) e
eval env (List es) = do
  vs <- traverse (eval env) es
  return (List vs)
eval env (Union l r) = do
  (List ls) <- eval env l
  List rs <- eval env r
  return (List $ ls V.++ rs)
eval env (For x l e) = case eval env l of
  Right (List l) ->
    let vs = traverse (\v -> 
                          case eval (Map.insert x v env) e of
                            Right (List r) -> Right r
                            Right x -> Left $ "body of a for comprehension did not return a list: " ++ show x
                            Left e -> Left $ "Error in for comprehension: " ++ show e
                      ) l
    in List . V.concat . V.toList <$> vs
  Right v -> Left $ "The expression to iterate over did not evaluate to a list: " ++ show v
  Left err -> Left $ "Some error in for body: " ++ err
eval env (PrependPrefix l r) = do
  (VText l) <- eval env l
  (VText r) <- eval env r
  return (VText $ l <> "⋅" <> r)
eval env (PrefixOf l r) = do
  (VText l) <- eval env l
  (VText r) <- eval env r
  return (VBool $ isPrefixOf l r)
eval env (StripPrefix p e) = do
  (VText p) <- eval env p
  (VText e) <- eval env e
  return (VText $ doStripPrefix p e)
eval env (Trace e) = do
  e' <- trace e
  v <- eval env e' -- in what env?
  return v
eval env (RecordMap r kv vv e) = do
  (Record r) <- eval env r
  r' <- Map.traverseWithKey (\l v -> eval (Map.insert kv (VText l) (Map.insert vv v env)) e) r
  return (Record r')
eval env (DynProj var@(NamedVar v) r) = do
  rec@(Record r) <- eval env r
  case Map.lookup var env of
    Just (VText l) -> case Map.lookup l r of
      Nothing -> Left $ "Can't find label " ++ show l ++ " in record " ++ show rec
      Just v -> Right v
    Just foo -> Left $ "looking up label variable " ++ show v ++ " returned something other than text: " ++ show foo
    Nothing -> Left $ "Unbound label variable " ++ show v 

reflect :: Expr -> Expr
reflect (Var v) = Tag "Var" (VText (pack (show v))) -- need a better rep for this
reflect (Lam v e) = Tag "Lam" (Record (Map.fromList [ ("var", VText (pack (show v))) -- need a better rep for this
                                                    , ("body", reflect e) ]))
reflect (App f a) = Tag "App" (Record (Map.fromList [ ("f", reflect f), ("x", reflect a) ]))
reflect (Record flds) = Tag "Record" (Record (Map.map reflect flds))
reflect (Proj l e) = Tag "Proj" (Record (Map.fromList [ ("l", VText l)
                                                      , ("r", reflect e) ])) -- call "w" for "consistency"?
reflect (Tag t e) = Tag "Tag" (Record (Map.fromList [ ("t", VText t)
                                                    , ("v", reflect e) ]))
reflect (Switch e cs) = Tag "Switch" (Record (Map.fromList [ ("e", reflect e)
                                                           , ("cs", cases) ]))
  where
    cases :: Expr
    cases = List (V.fromList (Map.elems (Map.mapWithKey (\t (v, c) ->
                                                            Record (Map.fromList [ ("t", VText t)
                                                                                 , ("v", VText (pack (show v)))
                                                                                 , ("c", reflect c) ])) cs)))
reflect (List es) = Tag "List" (List (V.map reflect es))
reflect (Eq l r) = Tag "Eq" (Record (Map.fromList [ ("left", reflect l)
                                                  , ("right", reflect r) ]))
reflect (And l r) = Tag "And" (Record (Map.fromList [ ("left", reflect l)
                                                    , ("right", reflect r) ]))
reflect (If c t e) = Tag "If" (Record (Map.fromList [ ("condition", reflect c)
                                                    , ("then", reflect t)
                                                    , ("else", reflect e) ]))
reflect (For v l e) = Tag "For" (Record (Map.fromList [ ("var", VText (pack (show v)))
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
trace (VBool b) = tr (VBool b) "Bool" (VBool b)
trace (VInt i) = tr (VInt i) "Int" (VInt i)
trace (VText s) = tr (VText s) "Text" (VText s)
trace (Var v)   = tr (Var v) "Var" (VText (pack (show v))) -- Ugh?
trace (Lam v e) = tr (Lam v e) "Lam" (rec [ ("var", VText (pack (show v)))
                                          , ("body", reflect e) ])
trace (Eq l r) = do
  lt <- trace l
  rt <- trace r
  tr (Eq l r) "Eq" (rec [ ("left", Proj "t" lt)
                        , ("right", Proj "t" rt)])
trace (And l r) = do
  lt <- trace l
  rt <- trace r
  tr (And (Proj "v" lt) (Proj "v" rt))
    "And" (rec [ ("left", Proj "t" lt)
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
  tr (App (Proj "v" ft) (Proj "v" xt)) "App" (rec [("fun", ft), ("arg", xt)])
trace (Record flds) = do
  fldst <- Map.traverseWithKey (\l e -> Proj "t" <$> trace e) flds
  fldsv <- Map.traverseWithKey (\l e -> Proj "v" <$> trace e) flds
  tr (Record fldsv) "Record" (Record fldst)
trace (Proj l e) = do
  te <- trace e
  tr (Proj l (Proj "v" te)) "Proj" (rec [ ("lab", VText l)
                                        , ("rec", te) ])
trace (Tag t e) = do
  te <- trace e
  tr (Tag t e) "Tag" (rec [ ("tag", VText t)
                          , ("val", Proj "t" te) ])
trace (Switch e cases) = do
  te <- trace e
  casesv <- traverse (\(v, c) -> case trace c of
                                   Right tc -> Right (v, Proj "v" tc)
                                   Left err -> Left err)
            cases
  cases' <- Map.traverseWithKey (\t (v, c) -> case trace c of
                                    Right tc -> Right $ (v, Tag "Switch" (Record (Map.fromList [ ("arg", Proj "t" te) -- the switched value
                                                                                               , ("tag", VText t)  -- matching tag
                                                                                               , ("var", VText (pack (show v)))  -- the variable
                                                                                               , ("case", reflect c) ]))) -- the case that matched (reflected)
                                    Left err -> Left err
                                    ) cases
  return (Record (Map.fromList [ ("v", Switch (Proj "v" te) casesv)
                               , ("t", Switch e cases') ]))
trace (List es) = do
  tes <- traverse trace es
  let labelledValues = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("v", (Proj "v" e))])) tes
  let labelledTraces = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("t", (Proj "t" e))])) tes
  let plain = V.map id tes
  tr (List labelledValues) "List" (List labelledTraces)
  -- return (Tag "List" (List plain))
trace (Union l r) = do
  lt <- trace l
  rt <- trace r
  tr (Union (For (GeneratedVar 100) (Proj "v" lt)
             (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "l") (Proj "p" (Var (GeneratedVar 100)))),
                                                       ("v", Proj "v" (Var (GeneratedVar 100)))])))))
      (For (GeneratedVar 101) (Proj "v" rt)
        (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "r") (Proj "p" (Var (GeneratedVar 101)))),
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
     "For" (rec [ ("in", tl)
                , ("body", reflect b)
                , ("var", VText (pack (show x)))
                , ("out", For y (Proj "v" tl)
                            (List (V.singleton (Record (Map.fromList [ ("p", Proj "p" (Var y))
                                                                     , ("t", Proj "t" (App (Lam x tb) (Proj "v" (Var y))))])))))
                ]) 

-- This is a huge fucking mess :( I think I actually might want some
-- sort of über-monad for my state and env and whatnot to live in

staticEq :: Expr -> Expr -> Maybe Bool
staticEq (VBool l) (VBool r) = Just $ l == r
staticEq (VInt l) (VInt r) = Just $ l == r
staticEq (VText l) (VText r) = Just $ l == r
staticEq (Record l) (Record r) = if Map.keys l == Map.keys r
  then do
    let z = zipWith staticEq (Map.elems l) (Map.elems r)
    l <- traverse id z
    return (and l)
  else Just False
staticEq l r = Nothing

beta :: [(Variable, Expr)] -> Expr -> Either String Expr
-- beta env e | T.trace ("beta " ++ show (length env) ++ " " ++ show e) False = undefined
beta env (VBool b) = return (VBool b)
beta env (VInt i) = return (VInt i)
beta env (VText t) = return (VText t)
beta env (Var v) = case Prelude.lookup v env of
  Just v -> Right v
  Nothing -> Left $ "unbound variable " ++ show v
beta env (App (Lam v body) arg) = do
  arg <- beta env arg
  beta ((v, arg):env) body
beta env (App (Closure v cenv body) arg) = do
  arg <- beta env arg
  beta ((v, arg) : Map.toList cenv) body
beta env (App f arg) = do
  f' <- beta env f
  beta env (App f' arg)
beta env (Proj l (Record flds)) =
  case Map.lookup l flds of
    Just e -> beta env e
    Nothing -> Left "label not found"
beta env (Proj l e) = do
  e' <- beta env e
  beta env (Proj l e')
beta env (If a b c) = do
  a' <- beta env a
  b' <- beta env b
  c' <- beta env c
  case a' of
    VBool True -> return b'
    VBool False -> return c'
    _ -> return $ If a' b' c'
-- TODO we could do better here, e.g.  if (5 == 7) then {a=7}.a else {b=9}.b  could evaluate to 9, instead of  if (5 == 7) then 7 else 9
beta env (Eq a b) = do
  a' <- beta env a
  b' <- beta env b
  case staticEq a' b' of
    Just True -> return $ VBool True
    Just False -> return $ VBool False
    Nothing -> return $ Eq a' b'
beta env (For v (List ls) e) = do
  es <- traverse (\x -> beta ((v, x) : env) e) ls
  beta env (Prelude.foldl Union (List mempty) es)
beta env (For v i e) = do
  i <- beta env i
  e <- beta ((v, (Var v)):env) e
  beta env $ For v i e -- Am I sure this always terminates?
beta env (Lam _ _) = undefined
beta env (And l r) = do
  l <- beta env l
  r <- beta env r
  case (l, r) of
    (VBool True, _) -> return r
    (_, VBool True) -> return l
    (VBool False, _) -> return $ VBool False
    (_, VBool False) -> return $ VBool False
    _ -> return $ And l r
beta env (Record es) =
  Record <$> traverse (beta env) es
beta env (DynProj _ _) = undefined
beta env (Tag t e) = do
  Tag t <$> beta env e
beta env (Switch e cs) = do
  (Tag t v) <- beta env e
  case Map.lookup t cs of
    Just (var, c) -> beta ((var, v):env) c
    Nothing -> Left $ "No case for constructor " ++ show t
beta env (List es) =
  List <$> traverse (beta env) es
beta env (Union l r) = do
  l' <- beta env l
  r' <- beta env r
  case (l', r') of
    (List l, List r) -> return $ List (l V.++ r)
    (_, _) -> return $ Union l' r'
beta env (Closure _ _ _) = undefined
beta env (PrependPrefix _ _) = undefined
beta env (PrefixOf _ _) = undefined
beta env (StripPrefix _ _) = undefined


beta' env =
  beta (Map.toList env)

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
        Right v -> do printCode stdout v
                      putStrLn ""
                      case beta' env e of
                        Left err -> putStrLn ("1st stage error: " ++ err)
                        Right e -> do printCode stdout e
                                      putStrLn ""
  repl env pstate
                      -- case trace e of
                      --   Left err -> putStrLn ("TRACE REWRITING ERROR: " ++ show err)
                      --   Right t -> do printCode stdout t
                      --                 putStrLn ""
                      --                 case eval env t of -- Not sure about this env here. Should this be a traced env?
                      --                   Left err -> putStrLn ("TRACED EVALUATION ERROR: " ++ show err)
                      --                   Right v -> do printValue stdout v
                      --                                 putStrLn ""
                      --                                 

sLoop :: Env -> [Stmt] -> IO (Either String Env)
sLoop env s = case s of
  [] -> return (Right env)
  ((Binding v e):rest) ->
    let val = eval env e
    in case val of
      Left e -> return (Left e)
      Right val -> sLoop (Map.insert v val env) rest
  ((Statement e):rest) ->
    case eval env e of
      Left e -> return (Left e)
      Right val -> do
        printCode stdout val
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
