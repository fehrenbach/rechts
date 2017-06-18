module Syntax where

import Data.Text
import qualified Data.Map.Strict as Map

data Variable
  = NamedVar Text
  deriving (Eq, Ord, Show)

type Env = Map.Map Variable Value

data Value
  = VBool Bool
  | VInt Int
  | VText Text
  | VFun Variable Env Expr
  | VRecord (Map.Map Text Value)
  deriving (Show)

data Expr
  = Val Value
  | Var Variable
  | Lam Variable Expr
  | App Expr Expr
  | Rec (Map.Map Text Expr)
  | Proj Text Expr
  deriving (Show)
