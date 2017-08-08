{-# LANGUAGE OverloadedStrings, TupleSections, FlexibleContexts #-}

module Main where

import Prelude hiding (getLine, readFile)
import Data.Text.IO (getLine, readFile)
import Syntax
import Parser (wholeExpr, toplevel)
import Pretty (printCode, printType)
import Data.Monoid
import Data.Text (Text, concat, pack, unpack, splitOn, isPrefixOf)
import qualified Debug.Trace as T
import Data.Either.Unwrap (fromRight)
import System.Environment (getArgs)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import Text.Megaparsec (runParser, ParsecT(..), runParserT', State(..), runParserT, parseErrorPretty)
import System.IO (hFlush, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.State.Strict (evalStateT, runStateT, MonadState, get, put)
import Control.Monad.Reader (MonadReader, runReaderT, local, asks)
import Control.Monad.Except (MonadError, throwError, runExceptT, runExcept)

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
eval env (Var _ v) = case Map.lookup v env of
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
    (Left err, _) -> Left $ "error in function application (fun)" ++ err
    (_, Left err) -> Left $ "error in function application (arg)" ++ err
eval env (Record fields) =
  Record <$> traverse (eval env) fields
eval env (Proj l r) =
  case eval env r of
    Right (Record v) -> case Map.lookup l v of
      Nothing -> Left $ "Record " ++ show v ++ " does not have label " ++ unpack l
      Just f -> Right f
    Right v -> Left $ "Not a record: " ++ show v ++ " (projecting to label " ++ show l ++ ")"
    Left e -> Left $ "error in projection: " ++ e
eval env (Tag t e) = do
  e' <- eval env e
  return (Tag t e')
eval env (Switch e cases) = do
  tagged <- eval env e
  case tagged of
    Tag l v -> case Map.lookup l cases of
      Nothing -> Left $ "No match in case -- matched value: " ++ show tagged ++ " cases: " ++ show cases
      Just (var, e) -> eval (Map.insert var v env) e
    nottagged -> Left $ "Not a tagged value: " ++ show nottagged
eval env (List es) = do
  vs <- traverse (eval env) es
  return (List vs)
eval env (Union l r) = do
  List ls <- eval env l
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
  e' <- evalStateT (trace e) 2000 -- TODO
  v <- eval env e' -- in what env?
  return v
eval env (RecordMap r kv vv e) = do
  (Record r) <- eval env r
  r' <- Map.traverseWithKey (\l v -> eval (Map.insert kv (VText l) (Map.insert vv v env)) e) r
  return (Record r')
eval env (DynProj l r) = do
  rec@(Record r) <- eval env r
  (VText l) <- eval env l
  case Map.lookup l r of
    Nothing -> Left $ "Can't find (dynamic) label " ++ show l ++ " in record " ++ show rec
    Just v -> Right v
eval env (Table _ _) = Right (List mempty) -- TODO
eval env (Untrace e) = eval (Map.insert UntraceVar e env) e
eval env (Self newBindings arg) = do
  List vvs <- eval env newBindings
  let Just vvs' = traverse foo vvs
  let vvsMap = Map.fromList (V.toList vvs')
  case Map.lookup UntraceVar env of
    Just e -> eval (vvsMap `Map.union` env) (App e arg)
    Nothing -> Left $ "Untrace variable is unbound -- are you inside an Untrace block?"
 where
   foo :: Expr -> Maybe (Variable, Expr)
   foo (Record vv) = do
     VText var <- Map.lookup "var" vv
     val <- Map.lookup "val" vv
     return (SelfVar var, val)
eval env (Lookup v) = do
  case eval env v of
    Right (VText v) -> 
      case Map.lookup (SelfVar v) env of
        Just v -> Right $ v
        Nothing -> Left $ "Unbound self variable " ++ show v
    Right e ->
      Left $ "Not a variable name: " ++ show e
eval env (Indexed e) = do
  e <- eval env e
  case e of
    List xs -> Right (List (V.imap (\i x -> Record (Map.fromList [ ("p", VText (pack (show i)))
                                                                 , ("v", x) ])) xs))
    Table _ _ -> Right (List mempty)
    _ -> Left $ "in indexed: argument not a list or table"

reflectVar :: Variable -> Expr
reflectVar v = VText (pack (show v)) -- TODO make better

reflect :: Expr -> Expr
reflect (VBool b) = Tag "Bool" (VBool b)
reflect (VInt i) = Tag "Int" (VInt i)
reflect (VText t) = Tag "Text" (VText t)
reflect (Var _ v) = Tag "Var" (reflectVar v)
reflect (Lam v e) = Tag "Lam" (Record (Map.fromList [ ("var", reflectVar v)
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
reflect (Table n t) = Tag "Table" (Record (Map.fromList [ ("name", VText n) ]))

tr :: Expr -> Text -> Expr -> Either a Expr
tr v c t =
  Right (Record (Map.fromList [("v", v), ("t", Tag c t)]))

unit :: Expr
unit = Record (Map.fromList [])

rec :: [(Text, Expr)] -> Expr
rec = Record . Map.fromList

mtr :: Monad m => Text -> Expr -> Expr -> m Expr
mtr c v t =
  return (Record (Map.fromList [("v", v), ("t", Tag c t)]))

freshVar :: MonadState Int m => m Variable
freshVar = do
  i <- get
  let i' = i+1
  put i'
  return (GeneratedVar i')

trace :: MonadState Int m => Expr -> m Expr
trace b@(VBool _) = mtr "Bool" b b
trace i@(VInt _) =  mtr "Int" i i
trace t@(VText _) = mtr "Text" t t
trace v@(Var _ vn) = mtr "Var" v (VText (pack (show vn)))
trace l@(Lam v e) = mtr "Lam" l (rec [ ("var", reflectVar v)
                                     , ("body", reflect e) ])
trace (Eq l r) = do
  lt <- trace l
  rt <- trace r
  mtr "Eq" (Eq l r) (rec [ ("left", Proj "t" lt), ("right", Proj "t" rt) ])
trace (And l r) = do
  lt <- trace l
  rt <- trace r
  mtr "And" (And l r) (rec [ ("left", Proj "t" lt), ("right", Proj "t" rt) ])
trace (For x l b) = do
  tl <- trace l
  yv <- freshVar
  zv <- freshVar
  yt <- freshVar
  tb <- trace b
  let v = For yv (Proj "v" tl)
            (For zv (Proj "v" (App (Lam x tb) (Proj "v" (Var Nothing yv))))
               (List (V.singleton (Record (Map.fromList [ ("p", PrependPrefix (Proj "p" (Var Nothing zv)) (Proj "p" (Var Nothing yv)))
                                                        , ("v", Proj "v" (Var Nothing zv)) ])))))
  mtr "For" v
     (rec [ ("in", tl)
          -- , ("body", reflect b) -- not needed ATM, make my life a bit easier
          , ("var", VText (pack (show x)))
          , ("out", For yt (Proj "v" tl)
                      (List (V.singleton (Record (Map.fromList [ ("p", Proj "p" (Var Nothing yt))
                                                               , ("t", Proj "t" (App (Lam x tb) (Proj "v" (Var Nothing yt))))])))))
          ])
trace (Closure _ _ _) = undefined
trace (App f x) = do
  ft <- trace f
  xt <- trace x
  mtr "App" (App (Proj "v" ft) (Proj "v" xt)) (rec [("fun", ft), ("arg", xt)])
trace (Record flds) = do
  fldst <- Map.traverseWithKey (\l e -> Proj "t" <$> trace e) flds
  fldsv <- Map.traverseWithKey (\l e -> Proj "v" <$> trace e) flds
  mtr "Record" (Record fldsv) (Record fldst)
trace (Proj l e) = do
  te <- trace e
  mtr "Proj" (Proj l (Proj "v" te)) (rec [ ("lab", VText l),
                                           ("rec", te),
                                           ("res", Proj l (Proj "t" te)) ])
trace (If c t e) = do
  ct <- trace c
  tt <- trace t
  et <- trace e
  mtr "If"
    (If c (Proj "v" tt)
          (Proj "v" et))
    (rec [ -- ("condition", Proj "t" ct) -- not needed ATM, so remove to make my life easier 
          ("branch", Proj "t" (If c tt et)) ])
trace (List es) = do
  tes <- traverse trace es
  let labelledValues = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("v", (Proj "v" e))])) tes
  let labelledTraces = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("t", (Proj "t" e))])) tes
  let plain = V.map id tes
  mtr "List" (List labelledValues) (List labelledTraces)
trace (Union l r) = do
  lt <- trace l
  rt <- trace r
  lv <- freshVar
  rv <- freshVar
  mtr "Union"
    (Union
      (For lv (Proj "v" lt)
        (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "l") (Proj "p" (Var Nothing lv))),
                                                  ("v", Proj "v" (Var Nothing lv))])))))
      (For rv (Proj "v" rt)
        (List (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "r") (Proj "p" (Var Nothing rv))),
                                                  ("v", Proj "v" (Var Nothing rv))]))))))
    (rec [("left", Proj "t" lt), ("right", Proj "t" rt)])
trace tbl@(Table n _) = do
  let v = Indexed tbl
  mtr "Table" v (Record (Map.fromList [ ("name", VText n)
                                      , ("ref", tbl) ]))
trace (Trace e) = trace e
trace (PrependPrefix _ _) = undefined
trace (PrefixOf _ _) = undefined
trace (StripPrefix _ _) = undefined
trace (RecordMap _ _ _ _) = undefined
trace (DynProj _ _) = undefined
trace (Tag _ _) = undefined
trace (Switch _ _) = undefined

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

unsafeLogCode :: Expr -> a -> a
unsafeLogCode e a = unsafePerformIO $ do
  printCode stdout e
  return a

subst :: Variable -> Variable -> Expr -> Expr
subst x y (Var t z)
  | x == z = Var t y
  | otherwise = Var t z
subst x y (Switch a cs) =
  Switch (subst x y a) (fmap (\(v, c) -> if v == x then (v, c) else (v, subst x y c)) cs)
subst x y (For z a b)
  | x == z = For z (subst x y a) b
  | otherwise = For z (subst x y a) (subst x y b)
subst x y (RecordMap arg kv vv e)
  | kv == x = RecordMap (subst x y arg) kv vv e
  | vv == x = RecordMap (subst x y arg) kv vv e
  | otherwise = RecordMap (subst x y arg) kv vv (subst x y e)
subst x y (Lookup a) =
  Lookup (subst x y a)  
subst x y (Indexed a) =
  Indexed (subst x y a)
subst x y (Proj l a) =
  Proj l (subst x y a)
subst x y (If a b c) =
  If (subst x y a) (subst x y b) (subst x y c)
subst x y (Eq a b) =
  Eq (subst x y a) (subst x y b)
subst x y (Union a b) =
  Union (subst x y a) (subst x y b)
subst x y (DynProj a b) =
  DynProj (subst x y a) (subst x y b)
subst x y (List ls) =
  List (fmap (subst x y) ls)
subst x y (Self vars arg) =
  Self (subst x y vars) (subst x y arg)
subst x y (Record fs) =
  Record (fmap (subst x y) fs)
subst _ _ otherwise = error $ show otherwise

freshen :: MonadState Int m => Expr -> m Expr
freshen (For x y z) = do
  x' <- freshVar
  y' <- freshen y
  z' <- freshen (subst x x' z)
  return (For x' y' z')
freshen (Lam x y) = do
  x' <- freshVar
  y' <- freshen (subst x x' y)
  return (Lam x' y')
freshen (Switch x ys) = do
  x' <- freshen x
  ys' <- traverse (\(v, y) -> (v,) <$> freshen y) ys
  return (Switch x' ys')
freshen (RecordMap x kv vv y) = do
  x' <- freshen x
  kv' <- freshVar
  vv' <- freshVar
  y' <- freshen (subst vv vv' (subst kv kv' y))
  return (RecordMap x' kv' vv' y')
freshen (Var t x) = return (Var t x)
freshen (Lookup x) = Lookup <$> freshen x
freshen (Indexed x) = Indexed <$> freshen x
freshen (Proj l x) = Proj l <$> freshen x
freshen (If a b c) = If <$> freshen a <*> freshen b <*> freshen c
freshen (Eq a b) = Eq <$> freshen a <*> freshen b
freshen (Union a b) = Union <$> freshen a <*> freshen b
freshen (DynProj a b) = DynProj <$> freshen a <*> freshen b
freshen (List xs) = List <$> traverse freshen xs
freshen (Record xs) = Record <$> traverse freshen xs
freshen (Self vars arg) = Self <$> freshen vars <*> freshen arg
freshen otherwise = error $ show otherwise

elementType :: Type -> Type
elementType (VectorT et) = et

-- Ugh, I think this idea to avoid putting types into the Expr datatype was a bad one
typeof :: Expr -> Type
typeof (VBool _) = BoolT
typeof (VText _) = TextT
typeof (For _ _ body) = typeof body
typeof (Table n t) = VectorT t
typeof (Record r) = RecordT (fmap typeof r)
typeof (Proj l e) = case typeof e of
  RecordT r -> case Map.lookup l r of
    Just t -> t
typeof (Tag l e) = VariantT (Map.singleton l (typeof e))
typeof otherwise = error (show otherwise)

tc :: (MonadReader (Map.Map Variable Type) m,
       MonadError String m,
       MonadState Int m) =>
      Env -> Expr -> m Expr
tc env (For x a b) = do
  a' <- tc env a
  let xt = elementType (typeof a')
  b' <- local (Map.insert x xt) (tc env b)
  return (For x a' b')
tc env (Proj l a) = do
  a' <- tc env a
  case typeof a' of
    RecordT r -> return (Proj l a')
    _ -> throwError $ "Not a record type in projection"
tc env (Trace a) = do
  ta <- trace a
  tc env ta
tc env (Record a) = do
  Record <$> traverse (tc env) a
tc env (Table n t) = do
  -- TODO check that table has relation type
  return (Table n t)
tc env (Tag l a) =
  Tag l <$> tc env a
tc env (VText t) = return (VText t)
tc env (Indexed a) = do
  a' <- tc env a
  case typeof a' of
    VectorT _ -> return (Indexed a')
    _ -> throwError $ "argument to indexed must have vector type"
tc env (Var Nothing v) = do
  t <- asks (Map.lookup v)
  -- already got a type in the environment?
  case t of
    Just t -> return (Var (Just t) v)
    Nothing -> case Map.lookup v env of
      -- variable bound in the global/file environment?
      Just a -> do
        a' <- tc env a
        return (Var (Just (typeof a')) v)
      Nothing -> throwError $ "unbound variable in type context or global env"
tc _ otherwise = throwError $ "no tc case for: " ++ show otherwise

beta :: (MonadError String m, MonadState Int m) => Env -> Expr -> m Expr
-- beta env e | T.trace ("beta " ++ show env ++ " " ++ show e) False = undefined
-- beta env e | unsafeLogCode e False = undefined
beta env (VBool b) = return (VBool b)
beta env (VInt i) = return (VInt i)
beta env (VText t) = return (VText t)
-- beta env e@(Var _) | unsafeLogCode e False = undefined
beta env (Var _ v) = case Map.lookup v env of
  -- This is a bit tricky: when iterating over a table, we bind the
  -- iteration variable to the lookup code, which means v => (Var v)
  -- which runs into an infinite loop if you try to beta reduce it
  -- further. At the moment I'm not really sure how this works with
  -- closures. Do we have to beta reduce the whole environment once
  -- over where we actually resolve variables?
  Just v -> return v
  Nothing -> throwError $ "unbound variable " ++ show v
beta env (App f arg) = do
  f <- beta env f
  arg <- beta env arg
  case f of
    Lam v body -> beta (Map.insert v arg env) body -- can this even happen?
    Closure v cenv body -> beta (Map.insert v arg cenv) body -- not sure about this
    _ -> throwError $ "not a function " ++ show f
beta env (Proj l e) = do
  e <- beta env e
  case e of
    Record flds -> case Map.lookup l flds of
      Just e -> beta env e
      Nothing -> throwError "label not found"
    If a b c -> beta env (If a (Proj l b) (Proj l c))
    e -> return $ Proj l e
beta env (If a b c) = do
  a' <- beta env a
  b' <- beta env b
  c' <- beta env c
  case a' of
    VBool True -> return b'
    VBool False -> return c'
    _ -> return $ If a' b' c'
beta env (Eq a b) = do
  a' <- beta env a
  b' <- beta env b
  case staticEq a' b' of
    Just True -> return $ VBool True
    Just False -> return $ VBool False
    Nothing -> return $ Eq a' b'
beta env (For x i n) = do
  i <- beta env i
  case i of
    -- FOR-beta
    List s | V.length s == 1 -> beta (Map.insert x (V.head s) env) n
    -- FOR-beta multi (and FOR-ZERO-L)
    List is -> do
      let ns = fmap (\i -> For x (List (V.singleton i)) n) is
      beta env (Prelude.foldl Union (List mempty) ns)
    -- t@(Table tn tt) -> do
    --   e <- beta (Map.insert x (Var x) env) n
    --   return (For x t e)
    -- FOR-ASSOC
    For y l m -> -- TODO if y \notin FV(e)
      beta env (For y l (For x m n))
    -- FOR-UNION-SRC
    Union m1 m2 ->
      beta env (Union (For x m1 n) (For x m2 n))
    -- FOR-IF-SRC
    If b m (List empty) | V.null empty -> beta env (If b (For x m n) (List empty))
    -- otherwise -> throwError $ show otherwise
    _ -> do
      e <- beta (Map.insert x (Var (Just (elementType (typeof i))) x) env) n
      return $ For x i e
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
beta env (Tag t e) =
  Tag t <$> beta env e
beta env s@(Switch e cs) = do
  e' <- beta env e
  case e' of
    Tag t v -> case Map.lookup t cs of
                 Just (var, c) -> beta (Map.insert var v env) c
                 Nothing -> throwError $ "No case for constructor " ++ show t
    If c th el -> beta env (If c (Switch th cs) (Switch el cs))
    _ -> throwError $ "error in switch: " ++ show e ++ " normalized to " ++ show e' ++ " in " ++ show s
beta env (List es) = do
  -- let xs = fmap (List . V.singleton) es
  -- beta env (Prelude.foldl Union (List mempty) xs)
  List <$> traverse (beta env) es
beta env (Union l r) = do
  l' <- beta env l
  r' <- beta env r
  case (l', r') of
    (List l, _) | V.null l -> return r'
    (_, List r) | V.null r -> return l'
    (List l, List r) -> return $ List (l V.++ r)
    (_, _) -> return $ Union l' r'
beta env tbl@(Table n t) = return tbl
beta env (Trace e) = do
  varC <- get
  (e', varC') <- runStateT (trace e) varC
  put varC'
  v <- beta env e' -- in what env?
  return v
beta env (Lam v e) = return (Lam v e) -- not so sure about this one...
-- beta env (Closure v cenv e) =
  -- return (Closure v cenv e)
beta env (PrependPrefix l r) = do
  l <- beta env l
  r <- beta env r
  case (l, r) of
    (VText l, VText r) -> return (VText $ l <> "⋅" <> r)
    (_, _) -> return (PrependPrefix l r)
beta env (PrefixOf l r) = PrefixOf <$> beta env l <*> beta env r
beta env (StripPrefix _ _) = undefined
beta env (DynProj l r) = do
  VText l' <- beta env l
  r' <- beta env r
  case r' of
    Record els -> case Map.lookup l' els of
      Just e -> beta env e
      Nothing -> throwError "label not found"
    _ -> return r'
    -- We might need to do something fancy here, if the argument does
    -- not happen to normalize to a record immediately.
    _ -> throwError $ "Not a record in dyn projection: " ++ show r
beta env rm@(RecordMap r kv vv e) = do
  r' <- beta env r
  case r' of
    Record els -> do
      els' <- Map.traverseWithKey (\l el -> beta (Map.insert kv (VText l) (Map.insert vv el env)) e) els
      return $ Record els'
    -- We can partially evaluate rmap based on type information alone:
    -- for (x <- table "foo" {abc: Text, cde: Int}) [rmap x (k = v) => v]
    --  -> for (x <- ...) [{abc = x!"abc", cde = x!"cde"}]
    -- but we need type information!
    _ -> throwError $ "not a record in rmap " ++ show r'
beta env dbg@(Self newVars arg) = do
  List newVars' <- beta env newVars
  vvs <- traverse foo newVars'
  let vvsMap = Map.fromList (V.toList vvs)
  case Map.lookup UntraceVar env of
    Just v -> do
      v <- freshen v
      beta (vvsMap `Map.union` env) (App v arg)
    Nothing -> throwError "unbound SELF"
 where
   foo (Record vv) =
     case Map.lookup "var" vv of
       Just (VText var) -> case Map.lookup "val" vv of
         Just val -> return (SelfVar var, val)
         Nothing -> throwError $ "No field val in key value binding record"
       Nothing -> throwError $ "No field var in key value binding record"
beta env test@(Lookup v) = do
  (VText v) <- beta env v
  case Map.lookup (SelfVar v) env of
    Just v -> return v
    Nothing -> throwError $ "unbound selfVar " ++ show v ++ " " ++ show env
beta env (Indexed e) = do
  e <- beta env e
  case e of
    Table n typ -> return $ Indexed (Table n typ)
    List xs -> return $ List (V.imap (\i x -> Record (Map.fromList [ ("p", VText (pack (show i)))
                                                                   , ("v", x) ])) xs)
    otherwise -> throwError $ "In indexed: " ++ show otherwise 
beta env (Untrace _) = undefined

beta' env =
  beta env

repl env pstate = do
  putStr "rechts> "
  hFlush stdout
  l <- getLine
  case runParser (runStateT wholeExpr pstate) "REPL" l of
    Left err -> putStrLn (parseErrorPretty err)
    Right (e, pstate) -> do
      -- putStrLn (show e)
      case eval env e of
        Left err -> putStrLn ("ERROR: " ++ show err)
        Right v -> do
          printCode stdout v
          putStrLn ""
          case evalStateT (trace e) 5500 of
            Left err -> putStrLn ("TRACE REWRITING ERROR: " ++ err)
            Right t -> do
              -- printCode stdout t; putStrLn ""
              putStrLn "trace code omitted"
                --                 case eval env t of -- Not sure about this env here. Should this be a traced env?
                --                   Left err -> putStrLn ("TRACED EVALUATION ERROR: " ++ show err)
                --                   Right v -> do printValue stdout v
                --                                 putStrLn ""
                --
              -- case runExcept $ evalStateT (beta' env e) 20000 of
                -- Left err -> putStrLn ("1st stage error: " ++ err)
                -- Right e -> do
                  -- printCode stdout e
                  -- putStrLn ""
          case runExcept $ flip runReaderT mempty $ evalStateT (tc env e) 10000 of
            Left err -> putStrLn ("type checking error: " ++ err)
            Right te -> do
              printType stdout (typeof te)
              putStrLn ""
              case runExcept $ evalStateT (beta' env te) 20000 of
                Left err -> putStrLn ("1st stage error: " ++ err)
                Right e -> do
                  printCode stdout e
                  putStrLn ""
  repl env pstate
                      

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
