module Syntax where

import Data.Text
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

data Variable
  = NamedVar Text
  | GeneratedVar Int
  | ViewVar
  | SelfVar Text
  deriving (Eq, Ord, Show)

type Env = Map.Map Variable Expr

data Type
  = BoolT
  | IntT
  | TextT
  | VectorT Type
  | RecordT (Map.Map Text Type)
  | VariantT (Map.Map Text Type)
  -- No. These should just be VariantT/RecordT over abstractions
  | SwitchT Type (Map.Map Text (Type, Type)) -- typevar -> type
  -- | RecordMapT Type
  | FunT Type Type
  | TyVar Int
  | AbsurdT
  deriving (Show, Eq, Ord)

data Expr
  = VBool Bool
  | VInt Int
  | VText Text
  | Var (Maybe Type) Variable
  | Lam (Maybe Type) Variable Expr
  | Closure Variable Env Expr
  | Eq Expr Expr
  | And Expr Expr
  | App Expr Expr
  | Record (Map.Map Text Expr)
  | Proj (Maybe Type) Text Expr
  | DynProj Expr Expr -- this is flipped for little good reason: a!b == DynProj b a
  | Tag Text Expr
  | Switch (Maybe Type) Expr (Map.Map Text (Variable, Expr))
  | If Expr Expr Expr
  | List (Maybe Type) (V.Vector Expr)
  | Union Expr Expr
  | For Variable Expr Expr
  | PrependPrefix Expr Expr
  | PrefixOf Expr Expr
  | StripPrefix Expr Expr
  | RecordMap (Maybe Type) Expr Variable Variable Expr
  | Table Text Type
  | Lookup (Maybe Expr) Expr
  | Indexed Expr -- indexed : [a] -> [{p : PrefixLabel, v : a}]
  | Untrace Expr Expr -- this is flipped in parser: untrace te with ve == Untrace ve te
  | View Expr
  | Self Expr Expr
  | Trace Expr
  | Undefined Text
  deriving (Show, Eq, Ord)

data Stmt
  = Binding Variable Expr
  | Statement Expr
  deriving (Show)
