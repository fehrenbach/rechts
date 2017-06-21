module Syntax where

import Data.Text
import qualified Data.Vector as V
import qualified Data.Map.Strict as Map

data Variable
  = NamedVar Text
  | GeneratedVar Int
  deriving (Eq, Ord, Show)

type Env = Map.Map Variable Value

data Prefix
  = PEmpty
  | PList Int Prefix
  | PLeft Prefix
  | PRight Prefix
  deriving (Show)

instance Monoid Prefix where
  mempty = PEmpty
  mappend = appendPrefix

appendPrefix :: Prefix -> Prefix -> Prefix
appendPrefix PEmpty p = p
appendPrefix p PEmpty = p
appendPrefix (PLeft l) p = PLeft (appendPrefix l p)
appendPrefix (PRight r) p = PRight (appendPrefix r p)
appendPrefix (PList i l) p = PList i (appendPrefix l p)

data Value
  = VBool Bool
  | VInt Int
  | VText Text
  | VFun Variable Env Expr
  | VRecord (Map.Map Text Value)
  | VTagged Text Value
  | VVector (V.Vector (Prefix, Value))
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
  deriving (Show)
