{-# LANGUAGE OverloadedStrings, TupleSections, FlexibleContexts, PartialTypeSignatures #-}

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
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.Megaparsec (runParser, ParsecT(..), runParserT', State(..), runParserT, parseErrorPretty)
import System.IO (hFlush, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Control.Exception.Base (assert)
import Control.Monad.State.Strict (evalStateT, runStateT, MonadState, get, put)
import Control.Monad.Reader (MonadReader, runReaderT, local, asks)
import Control.Monad.Except (MonadError, throwError, runExceptT, runExcept)
import Control.Monad.Writer (MonadWriter, runWriterT, tell, pass)
import Control.Monad (replicateM, forM_)
import GHC.Stack

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
eval env (Lam Nothing v e) =
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
eval env (Proj Nothing l r) =
  case eval env r of
    Right (Record v) -> case Map.lookup l v of
      Nothing -> Left $ "Record " ++ show v ++ " does not have label " ++ unpack l
      Just f -> Right f
    Right v -> Left $ "Not a record: " ++ show v ++ " (projecting to label " ++ show l ++ ")"
    Left e -> Left $ "error in projection: " ++ e
eval env (Tag t e) = do
  e' <- eval env e
  return (Tag t e')
eval env (Switch Nothing e cases) = do
  tagged <- eval env e
  case tagged of
    Tag l v -> case Map.lookup l cases of
      Nothing -> Left $ "No match in case -- matched value: " ++ show tagged ++ " cases: " ++ show cases
      Just (var, e) -> eval (Map.insert var v env) e
    nottagged -> Left $ "Not a tagged value: " ++ show nottagged
eval env (List Nothing es) = do
  vs <- traverse (eval env) es
  return (List Nothing vs)
eval env (Union l r) = do
  List Nothing ls <- eval env l
  List Nothing rs <- eval env r
  return (List Nothing $ ls V.++ rs)
eval env (For x l e) = case eval env l of
  Right (List Nothing l) ->
    let vs = traverse (\v ->
                          case eval (Map.insert x v env) e of
                            Right (List Nothing r) -> Right r
                            Right x -> Left $ "body of a for comprehension did not return a list: " ++ show x
                            Left e -> Left $ "Error in for comprehension: " ++ show e
                      ) l
    in List Nothing . V.concat . V.toList <$> vs
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
eval env (RecordMap Nothing r kv vv e) = do
  (Record r) <- eval env r
  r' <- Map.traverseWithKey (\l v -> eval (Map.insert kv (VText l) (Map.insert vv v env)) e) r
  return (Record r')
eval env (DynProj Nothing l r) = do
  rec@(Record r) <- eval env r
  (VText l) <- eval env l
  case Map.lookup l r of
    Nothing -> Left $ "Can't find (dynamic) label " ++ show l ++ " in record " ++ show rec
    Just v -> Right v
eval env (Table _ _) = Right (List Nothing mempty) -- TODO
eval env (View e) = return (View e) -- eval (Map.insert ViewVar e env) e
eval env (Self newBindings arg) = do
  List Nothing vvs <- eval env newBindings
  let Just vvs' = traverse foo vvs
  let vvsMap = Map.fromList (V.toList vvs')
  case Map.lookup ViewVar env of
    Just e -> eval (vvsMap `Map.union` env) (App e arg)
    Nothing -> Left $ "View variable is unbound -- are you inside an View block?"
 where
   foo :: Expr -> Maybe (Variable, Expr)
   foo (Record vv) = do
     VText var <- Map.lookup "var" vv
     val <- Map.lookup "val" vv
     return (SelfVar var, val)
eval env (Lookup Nothing v) = do
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
    List Nothing xs -> Right (List Nothing (V.imap (\i x -> Record (Map.fromList [ ("p", VText (pack (show i)))
                                                                 , ("v", x) ])) xs))
    Table _ _ -> Right (List Nothing mempty)
    _ -> Left $ "in indexed: argument not a list or table"
eval env (Untrace v e) = do
  e' <- eval env e
  v' <- eval env v
  case v' of
    View v'' -> eval (Map.insert ViewVar v'' env) (App v'' e')

reflectVar :: Variable -> Expr
reflectVar v = VText (pack (show v)) -- TODO make better

reflect :: Expr -> Expr
reflect (VBool b) = Tag "Bool" (VBool b)
reflect (VInt i) = Tag "Int" (VInt i)
reflect (VText t) = Tag "Text" (VText t)
reflect (Var _ v) = Tag "Var" (reflectVar v)
reflect (Lam Nothing v e) = Tag "Lam" (Record (Map.fromList [ ("var", reflectVar v)
                                                    , ("body", reflect e) ]))
reflect (App f a) = Tag "App" (Record (Map.fromList [ ("f", reflect f), ("x", reflect a) ]))
reflect (Record flds) = Tag "Record" (Record (Map.map reflect flds))
reflect (Proj Nothing l e) = Tag "Proj" (Record (Map.fromList [ ("l", VText l)
                                                      , ("r", reflect e) ])) -- call "w" for "consistency"?
reflect (Tag t e) = Tag "Tag" (Record (Map.fromList [ ("t", VText t)
                                                    , ("v", reflect e) ]))
reflect (Switch Nothing e cs) = Tag "Switch" (Record (Map.fromList [ ("e", reflect e)
                                                           , ("cs", cases) ]))
  where
    cases :: Expr
    cases = List Nothing (V.fromList (Map.elems (Map.mapWithKey (\t (v, c) ->
                                                            Record (Map.fromList [ ("t", VText t)
                                                                                 , ("v", VText (pack (show v)))
                                                                                 , ("c", reflect c) ])) cs)))
reflect (List Nothing es) = Tag "List" (List Nothing (V.map reflect es))
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

freshTVar :: MonadState Int m => m Type
freshTVar = do
  i <- get
  let i' = i+1
  put i'
  return (TyVar i')

trace :: MonadState Int m => Expr -> m Expr
trace b@(VBool _) = mtr "Bool" b b
trace i@(VInt _) =  mtr "Int" i i
trace t@(VText _) = mtr "Text" t t
trace v@(Var _ vn) = mtr "Var" v (VText (pack (show vn)))
trace l@(Lam Nothing v e) = mtr "Lam" l (rec [ ("var", reflectVar v)
                                     , ("body", reflect e) ])
trace (Eq l r) = do
  lt <- trace l
  rt <- trace r
  mtr "Eq" (Eq l r) (rec [ ("left", Proj Nothing "t" lt), ("right", Proj Nothing "t" rt) ])
trace (And l r) = do
  lt <- trace l
  rt <- trace r
  mtr "And" (And l r) (rec [ ("left", Proj Nothing "t" lt), ("right", Proj Nothing "t" rt) ])
trace (For x l b) = do
  tl <- trace l
  yv <- freshVar
  zv <- freshVar
  yt <- freshVar
  tb <- trace b
  let v = For yv (Proj Nothing "v" tl)
            (For zv (Proj Nothing "v" (App (Lam Nothing x tb) (Proj Nothing "v" (Var Nothing yv))))
               (List Nothing (V.singleton (Record (Map.fromList [ ("p", PrependPrefix (Proj Nothing "p" (Var Nothing zv)) (Proj Nothing "p" (Var Nothing yv)))
                                                        , ("v", Proj Nothing "v" (Var Nothing zv)) ])))))
  mtr "For" v
     (rec [ ("in", tl)
          -- , ("body", reflect b) -- not needed ATM, make my life a bit easier
          , ("var", VText (pack (show x)))
          , ("out", For yt (Proj Nothing "v" tl)
                      (List Nothing (V.singleton (Record (Map.fromList [ ("p", Proj Nothing "p" (Var Nothing yt))
                                                                       , ("t", Proj Nothing "t" (App (Lam Nothing x tb) (Proj Nothing "v" (Var Nothing yt))))])))))
          ])
trace (Closure _ _ _) = undefined
trace (App f x) = do
  ft <- trace f
  xt <- trace x
  mtr "App" (App (Proj Nothing "v" ft) (Proj Nothing "v" xt)) (rec [("fun", ft), ("arg", xt)])
trace (Record flds) = do
  fldst <- Map.traverseWithKey (\l e -> Proj Nothing "t" <$> trace e) flds
  fldsv <- Map.traverseWithKey (\l e -> Proj Nothing "v" <$> trace e) flds
  mtr "Record" (Record fldsv) (Record fldst)
trace (Proj Nothing l e) = do
  te <- trace e
  mtr "Proj"
      (Proj Nothing l (Proj Nothing "v" te))
      (rec [ ("lab", VText l),
             ("rec", te)
             -- ("res", Proj Nothing l (Proj Nothing "v" te))
             ])
trace (If c t e) = do
  ct <- trace c
  tt <- trace t
  et <- trace e
  mtr "If"
    (If c (Proj Nothing "v" tt)
          (Proj Nothing "v" et))
    (rec [ -- ("condition", Proj Nothing "t" ct) -- not needed ATM, so remove to make my life easier
          ("branch", Proj Nothing "t" (If c tt et)) ])
trace (List Nothing es) = do
  tes <- traverse trace es
  let labelledValues = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("v", (Proj Nothing "v" e))])) tes
  let labelledTraces = V.imap (\i e -> Record (Map.fromList [("p", VText (pack (show i))), ("t", (Proj Nothing "t" e))])) tes
  let plain = V.map id tes
  mtr "List" (List Nothing labelledValues) (List Nothing labelledTraces)
trace (Union l r) = do
  lt <- trace l
  rt <- trace r
  lv <- freshVar
  rv <- freshVar
  mtr "Union"
    (Union
      (For lv (Proj Nothing "v" lt)
        (List Nothing (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "l") (Proj Nothing "p" (Var Nothing lv))),
                                                  ("v", Proj Nothing "v" (Var Nothing lv))])))))
      (For rv (Proj Nothing "v" rt)
        (List Nothing (V.singleton (Record (Map.fromList [("p", PrependPrefix (VText "r") (Proj Nothing "p" (Var Nothing rv))),
                                                  ("v", Proj Nothing "v" (Var Nothing rv))]))))))
    (rec [("left", Proj Nothing "t" lt), ("right", Proj Nothing "t" rt)])
trace tbl@(Table n _) = do
  let v = Indexed tbl
  mtr "Table" v (Record (Map.fromList [ ("name", VText n)
                                      , ("ref", tbl) ]))
trace (Trace e) = trace e
trace (PrependPrefix _ _) = undefined
trace (PrefixOf _ _) = undefined
trace (StripPrefix _ _) = undefined
trace (RecordMap Nothing _ _ _ _) = undefined
trace (DynProj Nothing _ _) = undefined
trace (Tag _ _) = undefined
trace (Switch Nothing _ _) = undefined
trace (View _) = undefined

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
  putStrLn ""
  return a

unsafeLogType :: Type -> a -> a
unsafeLogType e a = unsafePerformIO $ do
  printType stdout e
  putStrLn ""
  return a

unsafeLogEnv :: (Map.Map Variable b) -> a -> a
unsafeLogEnv e a = unsafePerformIO $ do
  putStrLn (show (Map.keys e))
  return a

unsafeLogCode' :: Expr -> Expr
unsafeLogCode' c = unsafePerformIO $ do
  printCode stdout c
  putStrLn ""
  return c

unsafeLogTEnv e a = unsafePerformIO $ do
  let l = Map.toList e
  mapM_ (\(k, v) -> do
            putStr (show k ++ " :: ")
            unsafeLogType v (return ())) l
  return a

subst :: Variable -> Variable -> Expr -> Expr
subst x y (Var t z)
  | x == z = Var t y
  | otherwise = Var t z
subst x y (Switch mt a cs) =
  Switch mt (subst x y a) (fmap (\(v, c) -> if v == x then (v, c) else (v, subst x y c)) cs)
subst x y (For z a b)
  | x == z = For z (subst x y a) b
  | otherwise = For z (subst x y a) (subst x y b)
subst x y (RecordMap Nothing arg kv vv e)
  | kv == x = RecordMap Nothing (subst x y arg) kv vv e
  | vv == x = RecordMap Nothing (subst x y arg) kv vv e
  | otherwise = RecordMap Nothing (subst x y arg) kv vv (subst x y e)
subst x y (Lookup Nothing a) =
  Lookup Nothing (subst x y a)
subst x y (Indexed a) =
  Indexed (subst x y a)
subst x y (Proj Nothing l a) =
  Proj Nothing l (subst x y a)
subst x y (If a b c) =
  If (subst x y a) (subst x y b) (subst x y c)
subst x y (Eq a b) =
  Eq (subst x y a) (subst x y b)
subst x y (Union a b) =
  Union (subst x y a) (subst x y b)
subst x y (DynProj Nothing a b) =
  DynProj Nothing (subst x y a) (subst x y b)
subst x y (List Nothing ls) =
  List Nothing (fmap (subst x y) ls)
subst x y (Self vars arg) =
  Self (subst x y vars) (subst x y arg)
subst x y (Record fs) =
  Record (fmap (subst x y) fs)
subst x y l@(Lam Nothing var body)
  | x == var = l
  | otherwise = Lam Nothing var (subst x y body)
subst _ _ otherwise = error $ show otherwise

freshen :: MonadState Int m => Expr -> m Expr
freshen (For x y z) = do
  x' <- freshVar
  y' <- freshen y
  z' <- freshen (subst x x' z)
  return (For x' y' z')
freshen (Lam Nothing x y) = do
  x' <- freshVar
  y' <- freshen (subst x x' y)
  return (Lam Nothing x' y')
freshen (Switch Nothing x ys) = do
  x' <- freshen x
  ys' <- traverse (\(v, y) -> (v,) <$> freshen y) ys
  return (Switch Nothing x' ys')
freshen (RecordMap Nothing x kv vv y) = do
  x' <- freshen x
  kv' <- freshVar
  vv' <- freshVar
  y' <- freshen (subst vv vv' (subst kv kv' y))
  return (RecordMap Nothing x' kv' vv' y')
freshen (Var Nothing x) = return (Var Nothing x)
freshen (Lookup Nothing x) = Lookup Nothing <$> freshen x
freshen (Indexed x) = Indexed <$> freshen x
freshen (Proj Nothing l x) = Proj Nothing l <$> freshen x
freshen (If a b c) = If <$> freshen a <*> freshen b <*> freshen c
freshen (Eq a b) = Eq <$> freshen a <*> freshen b
freshen (Union a b) = Union <$> freshen a <*> freshen b
freshen (DynProj Nothing a b) = DynProj Nothing <$> freshen a <*> freshen b
freshen (List Nothing xs) = List Nothing <$> traverse freshen xs
freshen (Record xs) = Record <$> traverse freshen xs
freshen (Self vars arg) = Self <$> freshen vars <*> freshen arg
freshen otherwise = error $ show otherwise

elementType :: Type -> Type
elementType (VectorT et) = et
elementType err = error (show err)

-- Ugh, I think this idea to avoid putting types into the Expr datatype was a bad one
typeof :: HasCallStack => Expr -> Type
typeof (VInt _) = IntT
typeof (VBool _) = BoolT
typeof (VText _) = TextT
typeof (For _ _ body) = typeof body
typeof (Table n t) = VectorT t
typeof (Record r) = RecordT (fmap typeof r)
typeof (Proj (Just t) l e) = t
typeof (Tag l e) = VariantT (Map.singleton l (typeof e))
typeof (App f x) = case typeof f of
  FunT argt bodyt -> bodyt  -- uh, need to subst arg type / polymorphism?
typeof (Lam (Just t) _ _) = t
typeof (Var (Just t) _) = t
typeof (List (Just t) _) = VectorT t
typeof (Switch (Just t) _ _) = t
typeof (Indexed e) = VectorT (RecordT (Map.fromList [ ("p", TextT)
                                                    , ("v", elementType (typeof e)) ]))
typeof (Eq _ _) = BoolT
typeof (And _ _) = BoolT
typeof (PrependPrefix _ _) = TextT
typeof (If a b c) = typeof b -- This is not quite true, because type variables might not have been instantiated yet: assert (typeof b == typeof c) (typeof b)
typeof (Union l r) = typeof r -- Same as IF...
-- typeof (List Nothing _) = UnknownT -- ugh... one ugly hack after another
-- typeof (Var Nothing _) = UnknownT
typeof (Switch Nothing _ _) = UnknownT
typeof (Proj Nothing _ _) = UnknownT
typeof (DynProj (Just t) _ _) = t
typeof otherwise = error (show otherwise)

data Constraint
  = EqC Type Type
  | VariantLabelHasType Type Text Type
  | RecordLabelHasType  Expr Type Text Type
 deriving (Eq, Ord, Show)

uniEq x y =
  tell (Set.singleton (EqC x y))

uniVariantLabelHasType v l t =
  tell (Set.singleton (VariantLabelHasType v l t))

uniRecordLabelHasType e r l t =
  tell (Set.singleton (RecordLabelHasType e r l t))


tc :: (MonadReader (Map.Map Variable Type) m,
       MonadError String m,
       MonadWriter (Set.Set Constraint) m,
       MonadState Int m) =>
      Env -> Expr -> m Expr
tc env x@(VBool _) = return x
tc env x@(VInt _) = return x
tc env x@(VText _) = return x
-- eh, stupid duplication..
tc env (Lam (Just t) v e) = do
  tv <- freshTVar
  e <- local (Map.insert v tv) (tc env e)
  uniEq t (FunT tv (typeof e))
  return (Lam (Just (FunT tv (typeof e))) v e)
tc env (Lam Nothing v e) = do
  tv <- freshTVar
  e <- local (Map.insert v tv) (tc env e)
  return (Lam (Just (FunT tv (typeof e))) v e)
tc env (App f x) = do
  f <- tc env f
  x <- tc env x
  v <- freshTVar
  uniEq (typeof f) (FunT (typeof x) v)
  -- tell (Set.singleton (EqC (typeof f) (FunT (typeof x) v)))
  return (App f x)
tc env (For x a b) = do
  a' <- tc env a
  xt <- freshTVar
  uniEq (typeof a') (VectorT xt)
  -- let xt = elementType (typeof a')
  b' <- local (Map.insert x xt) (tc env b)
  return (For x a' b')
tc env e@(Proj (Just _) _ _) = return e -- already have a type
tc env e@(Proj Nothing l a) = do
  a <- tc env a
  res <- freshTVar
  uniRecordLabelHasType (Proj Nothing l a) (typeof a) l res
  return (Proj (Just res) l a)
tc env (Record a) = do
  Record <$> traverse (tc env) a
-- tc env (RecordMap Nothing a kv vv b) = do
--   a <- tc env a
--   res <- freshTVar
--   vt <- freshTVar
--   -- uhm.. don't i need fresh type variables for every label in the
--   -- record? I think I should be using an existential quantifier. That
--   -- is, there can be a fresh type in every branch when we finally
--   -- unroll it, it just has to be consistent. Right? Not sure.
--   b <- local (\m -> Map.insert kv TextT (Map.insert vv vt m)) (tc env b)
  
--   return $ RecordMap (Just (RecordMapT res)) a kv vv b
tc env (Trace a) = do
  ta <- trace a
  tc env ta
tc env (Table n t) = do
  -- TODO check that table has relation type
  return (Table n t)
tc env (Tag l a) =
  Tag l <$> tc env a
tc env (Indexed a) = do
  a' <- tc env a
  case typeof a' of
    VectorT _ -> return (Indexed a')
    _ -> throwError $ "argument to indexed must have vector type"
-- better way of dealing with duplication? Check as if there's no type, then verify?
-- actually, if the type is (Just UnknownT) this will fail... We need some subtyping for handling unknown...
tc env var@(Var (Just t) v) = do
  Var (Just t') _ <- tc env (Var Nothing v)
  uniEq t t'
  return var
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
      Nothing -> throwError $ "unbound variable in type context or global env: " ++ show v
        -- return (Var (Just UnknownT) v)
tc env (List (Just t) as) = do
  List (Just t') as <- tc env (List Nothing as)
  -- uniEq t t'
  return (List (Just t') as)
tc env (List Nothing as) = do
  elt <- freshTVar
  as <- traverse (\a -> do
                    a <- tc env a
                    uniEq elt (typeof a)
                    return a) as
  return (List (Just elt) as)
tc env (Switch Nothing a bs) = do
  a <- tc env a
  res <- freshTVar
  bs <- Map.traverseWithKey (\l (v, b) -> do
                                t <- freshTVar
                                uniVariantLabelHasType (typeof a) l t
                                b <- local (Map.insert v t) (tc env b)
                                return $ ((t, typeof b), (v, b))) bs
  uniEq res (SwitchT (typeof a) (fmap fst bs))
  return $ Switch (Just res) a (fmap snd bs)
tc env (If c t e) = do
  c <- tc env c
  uniEq (typeof c) BoolT
  t <- tc env t
  e <- tc env e
  uniEq (typeof t) (typeof e)
  return $ If c t e
tc env (And l r) = do
  l <- tc env l
  r <- tc env r
  uniEq (typeof l) BoolT
  uniEq (typeof r) BoolT
  return $ And l r
tc env (Eq l r) = do
  l <- tc env l
  r <- tc env r
  uniEq (typeof l) (typeof r)
  return $ Eq l r
tc env (PrependPrefix l r) = do
  l <- tc env l
  r <- tc env r
  uniEq (typeof l) TextT
  uniEq (typeof r) TextT
  return $ PrependPrefix l r
tc env (DynProj (Just t) field record) =
  DynProj (Just t) <$> tc env field <*> tc env record
tc env (Lookup (Just runtimeEnv) var) = do
  -- Eh, Lookup close over some environement or something?
  re <- tc env runtimeEnv
  var <- tc env var
  return (Lookup (Just re) var)
tc env (Union l r) =
  -- eh, this is completely fucked up
  Union <$> tc env l <*> tc env r
tc _ otherwise = throwError $ "no tc case for: " ++ show otherwise

substT s (TyVar z) = case Map.lookup z s of
  Just y -> y
  Nothing -> TyVar z
substT s BoolT = BoolT
substT s IntT = IntT
substT s TextT = TextT
substT s UnknownT = UnknownT
substT s (FunT a b) = FunT (substT s a) (substT s b)
substT s (VectorT a) = VectorT (substT s a)
substT s (RecordT a) = RecordT (fmap (substT s) a)
substT s (VariantT a) = VariantT (fmap (substT s) a)
substT s (SwitchT a b) = case substT s a of
  VariantT v ->
    case Map.toList v of
      [(label, typ)] -> case Map.lookup label b of
        Just (TyVar bound, b) -> substT (Map.insert bound typ s) b
        -- Nothing -> AbsurdT
  otherwise -> SwitchT otherwise (fmap (\(l, c) -> (l, substT s c)) b)

substC s (EqC a b) = EqC (substT s a) (substT s b)
substC s (VariantLabelHasType v l t) = VariantLabelHasType (substT s v) l (substT s t)
substC s (RecordLabelHasType x r l t) = RecordLabelHasType x (substT s r) l (substT s t)

applySubst s x@(VInt _) = x
applySubst s x@(VBool _) = x
applySubst s x@(VText _) = x
applySubst s x@(Table _ _) = x
applySubst s (Indexed a) = Indexed (applySubst s a)
applySubst s (App a b) = App (applySubst s a) (applySubst s b)
applySubst s (And a b) = And (applySubst s a) (applySubst s b)
applySubst s (Union a b) = Union (applySubst s a) (applySubst s b)
applySubst s (Eq a b) = Eq (applySubst s a) (applySubst s b)
applySubst s (PrependPrefix a b) = PrependPrefix (applySubst s a) (applySubst s b)
applySubst s (For v a b) = For v (applySubst s a) (applySubst s b)
applySubst s (Lam (Just t) v a) = Lam (Just (substT s t)) v (applySubst s a)
applySubst s (Tag t a) = Tag t (applySubst s a)
applySubst s (Proj (Just t) l a) = Proj (Just (substT s t)) l (applySubst s a)
applySubst s (Var (Just t) x) = Var (Just (substT s t)) x
applySubst s (Switch (Just t) a bs) = Switch (Just (substT s t)) (applySubst s a) (fmap (\(v, b) -> (v, applySubst s b)) bs)
applySubst s (List (Just t) a) = List (Just (substT s t)) (fmap (applySubst s) a)
applySubst s (Record a) = Record (fmap (applySubst s) a)
applySubst s (If a b c) = If (applySubst s a) (applySubst s b) (applySubst s c)
applySubst s otherwise = error $ "APPLYSUBST " ++ show otherwise

solve :: (MonadError String m) => Map.Map Int Type -> [Constraint] -> m (Map.Map Int Type)
solve s [] = return s
solve s (c : cs) = case c of
  EqC (TyVar v) t ->
    let s' = Map.insert v t (fmap (substT (Map.singleton v t)) s)
    in solve s' (fmap (substC s') cs)
  EqC t (TyVar v) ->
    let s' = Map.insert v t (fmap (substT (Map.singleton v t)) s)
    in solve s' (fmap (substC s') cs)
  EqC (FunT a b) (FunT c d) -> solve s ([EqC a c, EqC b d] ++ cs)
  EqC (VectorT a) (VectorT b) -> solve s ([EqC a b] ++ cs)
  EqC (RecordT a) (RecordT b) -> if (Map.keys a == Map.keys b)
    then solve s (zipWith (\(_, l) (_, r) -> EqC l r) (Map.toList a) (Map.toList b) ++ cs)
    else throwError $ "records have different keys " ++ show (Map.keys a) ++ " != " ++ show (Map.keys b)
  EqC (VariantT a) (VariantT b) -> if (Map.keys a == Map.keys b)
    then solve s (zipWith (\(_, l) (_, r) -> EqC l r) (Map.toList a) (Map.toList b) ++ cs)
    else throwError "variants have different keys"
  EqC TextT TextT -> solve s cs
  EqC BoolT BoolT -> solve s cs
  EqC IntT IntT -> solve s cs
  EqC UnknownT UnknownT -> solve s cs
  EqC x UnknownT -> solve s cs
  EqC UnknownT x -> solve s cs
  VariantLabelHasType (VariantT variant) l (TyVar v)
    | Map.size variant == 1 ->
      case Map.lookup l variant of
        Just t ->
          let s' = Map.insert v t (fmap (substT (Map.singleton v t)) s)
          in solve s' (fmap (substC s') cs)
        Nothing -> throwError "not a label in variant type or something"
        -- Nothing ->
          -- let t = AbsurdT 
              -- s' = Map.insert v t (fmap (substT (Map.singleton v t)) s)
          -- in solve s' (fmap (substC s') cs)
  VariantLabelHasType (VariantT variant) l t ->
    case Map.lookup l variant of
      Just t' | t == t' -> solve s cs
  RecordLabelHasType _ (RecordT r) l (TyVar v) ->
    case Map.lookup l r of
      Just t ->
        let s' = Map.insert v t (fmap (substT (Map.singleton v t)) s)
        in solve s' (fmap (substC s') cs)
  RecordLabelHasType _ (RecordT r) l t' ->
    case Map.lookup l r of
      Just t -> solve s ((EqC t t'):cs)
  r@(RecordLabelHasType (Proj _ _ _) (TyVar _) l _) ->
    -- We don't have enough information to do anything with this at
    -- the moment, without introducing row types. Just defer for
    -- now. TODO this is not safe, might loop forever...
    solve s (cs ++ [r])
  otherwise -> throwError $ "todo solve " ++ show otherwise

substSelf ev s (Self newVars arg) = App (App s (Union newVars (Var Nothing ev))) arg
substSelf ev s x@(Var Nothing _) = x
substSelf ev s (Lookup Nothing a) = Lookup (Just (Var Nothing ev)) (substSelf ev s a)
substSelf ev s (Lam Nothing x a) = Lam Nothing x (substSelf ev s a)
substSelf ev s (Proj Nothing x a) = Proj Nothing x (substSelf ev s a)
substSelf ev s (List Nothing as) = List Nothing (fmap (substSelf ev s) as)
substSelf ev s (Record as) = Record (fmap (substSelf ev s) as)
substSelf ev s (Switch Nothing a bs) = Switch Nothing (substSelf ev s a) (fmap (\(v, b) -> (v, substSelf ev s b)) bs)
substSelf ev s (Eq a b) = Eq (substSelf ev s a) (substSelf ev s b)
substSelf ev s (Union a b) = Union (substSelf ev s a) (substSelf ev s b)
substSelf ev s (DynProj Nothing a b) = DynProj Nothing (substSelf ev s a) (substSelf ev s b)
substSelf ev s (For v a b) = For v (substSelf ev s a) (substSelf ev s b)
substSelf ev s (RecordMap Nothing a x y b) = RecordMap Nothing (substSelf ev s a) x y (substSelf ev s b)
substSelf ev s (If a b c) = If (substSelf ev s a) (substSelf ev s b) (substSelf ev s c)
substSelf ev s otherwise = error $ "SUBSTSELF " ++  (show otherwise)

unroll 0 ev view = Undefined "did not unroll often enough"
unroll n (ev:rest) view = Lam Nothing ev (substSelf ev (unroll (n-1) rest view) view) -- substSelf ev (Lam Nothing ev (unroll (n-1) ev view)) view

sp :: (MonadError String m, MonadState Int m, HasCallStack) => (Expr, Variable) -> Map.Map Variable Type -> Expr -> Type -> m Expr
sp v tenv x y | T.trace "SP ---------------------------------- " False = undefined
sp v tenv x y | unsafeLogCode x False = undefined
sp v tenv x y | unsafeLogType y False = undefined
-- sp v tenv x y | T.trace (" :: " ++ show y) False = undefined
-- sp v tenv x y | unsafeLogTEnv tenv False = undefined
sp v tenv x@(VInt _) _ = return x
sp v tenv x@(VText _) _ = return x
sp v tenv (Record a) UnknownT =
  Record <$> traverse (\x -> sp v tenv x UnknownT) a
sp v tenv (Union a b) t = do
  -- Yeah.. this really needs to be constraint-based. FML.
  let t' = mj (mj (typeof a) (typeof b)) t
  a <- sp v tenv a t'
  b <- sp v tenv b t'
  return (Union a b)
sp v tenv (App f x) t = do
  x <- sp v tenv x UnknownT
  f <- sp v tenv f (FunT (typeof x) t)
  return $ App f x
sp (view, envvar) tenv (Self bindings arg) t = do
  arg <- sp (view, envvar) tenv arg UnknownT
  -- envvar' <- freshVar
  -- throwError $ "wtf is going on?" ++ show view
  newView@(Lam _ newEnvVar _) <- freshen view
  spNewView <- sp (view, newEnvVar) tenv newView (FunT UnknownT (FunT (typeof arg) UnknownT))
  return (App (App spNewView (Union bindings (Var Nothing envvar))) arg)
  -- sp (view, newEnvVar) tenv (App (App newView (Union bindings (Var Nothing envvar))) arg) (FunT UnknownT (FunT t UnknownT))
sp v tenv (List Nothing a) t =
  case t of
    VectorT elt -> do
      as <- traverse (\x -> sp v tenv x elt) a
      let t' = V.foldl' mj elt (fmap typeof as)
      return $ List (Just t') as
    otherwise -> do
      as <- traverse (\x -> sp v tenv x UnknownT) a
      let t' = V.foldl' mj UnknownT (fmap typeof as)
      return $ List (Just t') as
sp v tenv (Eq a b) BoolT =
  -- yeah.. this is definitely a unification problem
  Eq <$> sp v tenv a UnknownT <*> sp v tenv b UnknownT
sp v tenv (If a b c) t =
  If <$> sp v tenv a BoolT <*> sp v tenv b t <*> sp v tenv c t
sp v tenv p@(Proj Nothing l x) t = do
  x <- sp v tenv x UnknownT -- really? Shouldn't it be {l :: UnknownT | _} 
  case typeof x of
    UnknownT -> return (Proj (Just t) l x)
    RecordT r -> case Map.lookup l r of
      Just t2 -> return (Proj (Just (mj t t2)) l x)
sp v tenv (For var i o) t = do
  i <- sp v tenv i UnknownT
  case typeof i of
    VectorT elt -> For var i <$> sp v (Map.insert var elt tenv) o t
sp v tenv (Lam Nothing var body) (FunT a b) = do
  body <- sp v (Map.insert var a tenv) body b
  -- Yeah, this is more like it. But my environment and state handling is a mess.
  return $ Lam (Just (FunT a (typeof body))) var body
sp v@(_, envvar) tenv (Lookup Nothing x) t =
  Lookup (Just (Var Nothing envvar)) <$> sp v tenv x TextT
sp v tenv (RecordMap Nothing x kv vv e) t = do
  x <- sp v tenv x UnknownT
  case typeof x of
    RecordT r -> do
      r' <- Map.traverseWithKey
        (\l t' -> do
            -- kv' <- freshTVar
            -- vv' <- freshTVar
            -- let e' = subst vv vv' (subst kv kv' e)
            -- rmap x with (k = v) => foo
            -- ~> (\k.\v.foo) k x.k  forall k in x
            let fun = Lam Nothing kv (Lam Nothing vv e)
            let app = App (App fun (VText l)) (Proj Nothing l x)
            sp v tenv app t')
        r
            -- e' <- freshen e
            -- sp v (Map.insert kv TextT (Map.insert vv t' tenv)) e UnknownT) r
      return (Record r')
sp v tenv (DynProj Nothing val lab) t =
  -- Eh, we know something about the type of VAL: it's a record with *some* label and type t.
  -- But we can't represent that, and it's not even clear that we could use that information at this point, so whatever...
  DynProj (Just t) <$> sp v tenv val UnknownT <*> sp v tenv lab TextT
sp v tenv sw@(Switch Nothing x cs) t = do
  x <- sp v tenv x UnknownT
  case typeof x of
    VariantT vs -> do
      let cs' = Map.filterWithKey (\variant _ -> Map.member variant vs) cs
      cs'' <- Map.traverseWithKey (\variant (var, e) -> do
                                      let (Just ty) = Map.lookup variant vs
                                      -- No, v has type ty
                                      body' <- sp v (Map.insert var ty tenv) e t
                                      return (var, body')) cs'
      -- TODO I might need to combine the types of the bodies with the "pushed" type t (= UnknownT)
      return (Switch Nothing x cs'')
    -- UnknownT ->
    --   return (Switch (Just t) x cs)
    -- otherwise -> throwError $ unsafeLogCode sw (show otherwise)
sp v tenv x y | unsafeLogTEnv tenv False = undefined
sp v tenv (Var mt1 var) t3 =
  -- we have three sources of type information we need to potentially combine
  -- this is a mess
  case (mt1, Map.lookup var tenv) of
    (Just t1, Just t2) -> return $ Var (Just (mj (mj t1 t2) t3)) var
    (Nothing, Just t2) -> return $ Var (Just (mj t2 t3)) var
    (Nothing, Nothing) -> return $ Var (Just t3) var
sp v tenv fun ty = -- unsafeLogCode fun $
  throwError $ "SPECIALIZE: " ++ show fun ++ "   ::   " ++ show ty ++ "   in context   " ++ show tenv

-- meet or join or whatever -- combine partial type information as much as possible
-- hmm.. so it currently looks like we don't actually ever need interesting partial information.
-- partiality at the toplevel either known or unknown seems to be enough
-- this suggests a bidirectional approach could actually work
-- that would make everything a bit cleaner
mj :: HasCallStack => Type -> Type -> Type
mj UnknownT t = t
mj t UnknownT = t
mj x y | x == y = x
mj x y = error $ show x ++ " <mj> " ++ show y

-- specialize :: Expr -> Type -> m Expr
specialize envvar fun ty = sp (fun, envvar) mempty fun ty

-- get rid of all tracing related stuff
desugar (Untrace (Var Nothing v) a) = do
  a' <- desugar a
  env <- asks id
  (a'', cs) <- runWriterT $ flip runReaderT mempty (tc env a')
  subst <- solve mempty (Set.toList cs)
  let a''' = applySubst subst a''
  let ta = typeof a'''
  v' <- asks (Map.lookup v)
  fv <- freshVar
  case v' of
    Just (View v'') -> do
      f <- specialize fv (Lam Nothing fv v'') (FunT UnknownT (FunT ta UnknownT))
      let f' = unsafeLogCode f f
      -- let steps = 10
      -- vars <- replicateM steps freshVar
      return (App (App f' (List Nothing mempty)) a''')
      -- return (App (App (unroll steps vars v'') (List Nothing mempty)) a')
    _ -> throwError $ "Variable " ++ show v ++ " did not evaluate to a VIEW"
desugar (Untrace notavar _) = throwError $ "For now, the first argument to UNTRACE has to be a variable referring to a VIEW, but is: " ++ show notavar
desugar (Trace a) = trace a
desugar x@(VBool _) = return x
desugar x@(VInt _) = return x
desugar x@(VText _) = return x
desugar v@(View _) = return v
desugar s@(Self _ _) = throwError $ "All references to SELF should have been desugared"
desugar t@(Table _ _) = return t
desugar x@(Var Nothing _) = return x
desugar (Indexed a) = Indexed <$> desugar a
desugar (Tag t a) = Tag t <$> desugar a
desugar (Proj Nothing l a) = Proj Nothing l <$> desugar a
desugar (Lam Nothing v a) = Lam Nothing v <$> desugar a
desugar (List Nothing as) = List Nothing <$> traverse desugar as
desugar (App a b) = App <$> desugar a <*> desugar b
desugar (Switch Nothing a bs) = Switch Nothing <$> desugar a <*> traverse (\(v, e) -> (v,) <$> desugar e) bs
desugar (Record as) = Record <$> traverse desugar as
desugar otherwise = throwError $ "DESUGAR: " ++ show otherwise

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
-- beta env e@(App _ _) | unsafeLogEnv env False = undefined
-- beta env e@(App _ _) | unsafeLogCode e False = undefined
beta env (App f arg) = do
  f <- beta env f
  arg <- beta env arg
  case f of
    -- Lam v body -> beta (Map.insert v arg env) body -- can this even happen?
    Closure v cenv body -> beta (Map.insert v arg cenv) body -- not sure about this
    _ -> throwError $ "not a function " ++ show f
beta env (Proj (Just t) l e) = do
  e <- beta env e
  case e of
    Record flds -> case Map.lookup l flds of
      Just e -> beta env e
      Nothing -> throwError "label not found"
    If a b c -> beta env (If a (Proj (Just t) l b) (Proj (Just t) l c))
    e -> return $ Proj (Just t) l e
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
    List _ s | V.length s == 1 -> beta (Map.insert x (V.head s) env) n
    -- FOR-beta multi (and FOR-ZERO-L)
    List _ is -> do
      let ns = fmap (\i -> For x (List (Just (typeof i)) (V.singleton i)) n) is
      beta env (Prelude.foldl Union (List (Just (typeof i)) mempty) ns)
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
    If b m (List t empty) | V.null empty -> beta env (If b (For x m n) (List t empty))
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
beta env s@(Switch (Just t) e cs) = do
  e' <- beta env e
  case e' of
    Tag t v -> case Map.lookup t cs of
                 Just (var, c) -> beta (Map.insert var v env) c
                 Nothing -> throwError $ "No case for constructor " ++ show t
    If c th el -> beta env (If c (Switch Nothing th cs) (Switch Nothing el cs))
    _ -> throwError $ "error in switch: " ++ show e ++ " normalized to " ++ show e' ++ " in " ++ show s
beta env (List t es) = do
  -- let xs = fmap (List . V.singleton) es
  -- beta env (Prelude.foldl Union (List mempty) xs)
  List t <$> traverse (beta env) es
beta env (Union l r) = do
  l' <- beta env l
  r' <- beta env r
  case (l', r') of
    (List _ l, _) | V.null l -> return r'
    (_, List _ r) | V.null r -> return l'
    (List s l, List t r) | s == t -> return $ List t (l V.++ r)
    (_, _) -> return $ Union l' r'
beta env tbl@(Table n t) = return tbl
beta env (Trace e) = do
  varC <- get
  (e', varC') <- runStateT (trace e) varC
  put varC'
  v <- beta env e' -- in what env?
  return v
beta env (Lam _ v e) =
  return (Closure v env e)
  -- return (Lam v e) -- not so sure about this one...
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
beta env (DynProj Nothing l r) = do
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
beta env rm@(RecordMap Nothing r kv vv e) = do
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
  List t newVars' <- beta env newVars
  vvs <- traverse foo newVars'
  let vvsMap = Map.fromList (V.toList vvs)
  case Map.lookup ViewVar env of
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
beta env test@(Lookup (Just analysisEnv) x) = do
  x' <- beta env x
  List _ l <- beta env analysisEnv
  case V.find (\(Record r) -> case Map.lookup "var" r of
                                Just var -> var == x'
                                Nothing -> False) l of
    Just (Record r) -> case Map.lookup "val" r of
                         Just res -> return res
                         Nothing -> throwError "No val field"
    Nothing -> throwError $ "no binding for " ++ show x'
beta env (Indexed e) = do
  e <- beta env e
  case e of
    Table n typ -> return $ Indexed (Table n typ)
    List (Just t) xs ->
      return $ List (Just (pvt t)) (V.imap (\i x -> Record (Map.fromList [ ("p", VText (pack (show i)))
                                                                         , ("v", x) ])) xs)
    otherwise -> throwError $ "In indexed: " ++ show otherwise
  where pvt vt = RecordT (Map.fromList [ ("p", TextT), ("v", vt) ])
beta env (View _) = throwError $ "There should not be a VIEW left"
beta env (Undefined reason) = throwError $ "Tried to beta reduce UNDEFINED: " ++ unpack reason
beta env otherwise = throwError $ "BETA case missing: " ++ show otherwise

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
        Left err -> putStrLn ("EVAL error: " ++ show err)
        Right v -> do
          printCode stdout v
          putStrLn ""
      case runExcept $ flip runReaderT env $ evalStateT (desugar e) 10000 of
        Left err -> putStrLn ("DESUGAR error: " ++ show err)
        Right de -> do
          -- printCode stdout de
          -- putStrLn ""
          putStrLn "desugared code omitted"
          case runExcept $ runWriterT $ flip runReaderT mempty $ evalStateT (tc env de) 15000 of
            Left err -> putStrLn $ show err
            Right (tt, cs) -> do
              printType stdout (typeof tt)
              putStrLn ""
              case runExcept $ solve mempty (Set.toList cs) of
                Left err -> putStrLn $ show err
                Right s -> do
                  let tt' = applySubst s tt
                  printCode stdout tt'
                  putStrLn ""
                  printType stdout (typeof tt')
                  putStrLn ""
                  case runExcept $ evalStateT (beta' env tt') 20000 of
                    Left err -> putStrLn ("1st stage error: " ++ err)
                    Right e -> do
                      printCode stdout e
                      putStrLn ""
          -- case runExcept $ evalStateT (beta' env de) 20000 of
          --   Left err -> putStrLn ("1st stage error: " ++ err)
          --   Right e -> do
          --     printCode stdout e
          --     putStrLn ""
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
