module Syntax where

import Data.Text
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

data Variable
  = NamedVar Text
  | GeneratedVar Int
  deriving (Eq, Ord, Show)

type Env = Map.Map Variable Expr

data Type
  = BoolT
  | IntT
  | TextT
  | VectorT Type
  | RecordT (Map.Map Text Type)
  deriving (Show, Eq)

data Expr
  = VBool Bool
  | VInt Int
  | VText Text
  | Var Variable
  | Lam Variable Expr
  | Closure Variable Env Expr
  | Eq Expr Expr
  | And Expr Expr
  | App Expr Expr
  | Record (Map.Map Text Expr)
  | Proj Text Expr
  | DynProj Variable Expr
  | Tag Text Expr
  | Switch Expr (Map.Map Text (Variable, Expr))
  | If Expr Expr Expr
  | List (V.Vector Expr)
  | Union Expr Expr
  | For Variable Expr Expr
  | PrependPrefix Expr Expr
  | PrefixOf Expr Expr
  | StripPrefix Expr Expr
  | Trace Expr
  | RecordMap Expr Variable Variable Expr
  | Table Text Type
  deriving (Show, Eq)

data Stmt
  = Binding Variable Expr
  | Statement Expr
  deriving (Show)
