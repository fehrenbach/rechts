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

instance Eq Value where
  (VBool l) == (VBool r) = l == r
  (VInt l) == (VInt r) = l == r
  (VText l) == (VText r) = l == r
  (VRecord l) == (VRecord r) = l == r
  (VVector l) == (VVector r) = l == r
  (VTagged lt l) == (VTagged rt r) = lt == rt && l == r
  (VFun _ _ _) == _ = error "Can't compare functions"
  _ == (VFun _ _ _) = error "Can't compare functions"
  _ == _ = False

-- Using Map and Vector here was a terrible idea
-- Lists are so much easier
data Expr
  = Val Value
  | Var Variable
  | Lam Variable Expr
  | Eq Expr Expr
  | And Expr Expr
  | App Expr Expr
  | Record (Map.Map Text Expr)
  | Proj Text Expr
  | Tag Text Expr
  | Switch Expr (Map.Map Text (Variable, Expr))
  | If Expr Expr Expr
  | List (V.Vector Expr)
  | Union Expr Expr
  | For Variable Expr Expr
  | PrependPrefix Expr Expr
  deriving (Show)

data Stmt
  = Binding Variable Expr
  | Statement Expr
  deriving (Show)
