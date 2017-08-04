{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Prelude hiding ((<$>))
import Syntax
import Text.PrettyPrint.ANSI.Leijen
import System.IO (Handle)
import Data.Text (Text, unpack)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

prettyVariable :: Variable -> Doc
prettyVariable (NamedVar n) = pretty (unpack n)
prettyVariable (GeneratedVar n) = "v_" <> pretty n

label :: Text -> Doc
label t = blue (pretty (unpack t))

prettyType _ = "..."

prettyCode :: Expr -> Doc
prettyCode (VBool b) = pretty b
prettyCode (VInt i) = pretty i
prettyCode (VText t) = "\"" <> pretty (unpack t) <> "\""
prettyCode (Var v) = prettyVariable v
prettyCode (Record es) =
  braces (align (ke (Map.toAscList es)))
  where
    ke [] = empty
    ke [(k, e)] = label k <> " = " <> group (prettyCode e)
    ke ((k, e):kes) = label k <> " = " <> group (prettyCode e) <> "," <$> ke kes
prettyCode (List es) =
  brackets (align (ke (V.toList es)))
  where
    ke [] = empty
    ke [e] = group $ prettyCode e
    ke (e:es) = group (prettyCode e) <> "," <$> ke es
prettyCode (Tag t e) = parens $ align $ green (pretty (unpack t)) </> prettyCode e
prettyCode (Switch e cs) = hang 2 $ magenta "switch" <+> prettyCode e <$> cases (Map.toAscList cs)
  where
    cases [] = empty
    cases [c] = case' c
    cases (c:cs) = case' c <$> cases cs
    case' (t, (v, e)) = hang 2 $ magenta "case" <+> green (pretty (unpack t)) <+> prettyVariable v <+> "=>" </> prettyCode e
prettyCode (App a b) =
  parens $ prettyCode a <+> prettyCode b
prettyCode (Proj l e) =
  prettyCode e <> magenta "." <> label l
prettyCode (Union l r) =
  parens $ prettyCode l <+> "++" <+> prettyCode r
prettyCode (Eq l r) =
  parens $ prettyCode l <+> "==" <+> prettyCode r
prettyCode (And l r) =
  parens $ prettyCode l <+> "&&" <+> prettyCode r
prettyCode (PrependPrefix l r) =
  parens $ prettyCode l <+> magenta "⋅" <+> prettyCode r
prettyCode (Indexed e) =
  parens $ magenta "indexed" <+> prettyCode e
prettyCode (Table tn tt) =
  magenta "table" <+> prettyCode (VText tn) <+> prettyType tt
prettyCode (For x l e) =
  hang 2 $ magenta "for" <+> parens (prettyVariable x <+> "<-" <+> group (prettyCode l)) <$> prettyCode e
prettyCode (Lam x e) =
  hang 2 $ parens $ magenta "λ" <> prettyVariable x <> "." </> prettyCode e
prettyCode (Closure x env e) =
  hang 2 $ parens $ red "λ" <> prettyVariable x <> "." </> prettyCode e
prettyCode (If c t e) =
  align $ magenta "if" <+> group (prettyCode c) <$> hang 2 (magenta "then" </> prettyCode t) <$> hang 2 (magenta "else" </> prettyCode e)
prettyCode other = string (show other)

printCode :: Handle -> Expr -> IO ()
printCode h c = displayIO h (renderPretty 0.8 120 (prettyCode c))
