module Syntax where

import Data.Text
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

data Variable
  = NamedVar Text
  | GeneratedVar Int
  deriving (Eq, Ord, Show)

type Env = Map.Map Variable Value

data Value
  = VBool Bool
  | VInt Int
  | VText Text
  | VFun Variable Env Expr
  | VRecord (Map.Map Text Value)
  | VTagged Text Value
  | VVector (V.Vector Value)
  deriving (Show)

-- Using Map and Vector here was a terrible idea
-- Lists are so much easier
data Expr
  = Val Value
  | Var Variable
  | Lam Variable Expr
  | App Expr Expr
  | Record (Map.Map Text Expr)
  | Proj Text Expr
  | Tag Text Expr
  | Switch Expr (Map.Map Text (Variable, Expr))
  | List (V.Vector Expr)
  | Union Expr Expr
  | For Variable Expr Expr
  | PrependPrefix Expr Expr
  deriving (Show)
