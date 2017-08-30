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

tag :: Text -> Doc
tag t = green (pretty (unpack t))

prettyType BoolT = "Bool"
prettyType IntT = "Int"
prettyType TextT = "Text"
prettyType (VectorT t) = brackets (prettyType t)
prettyType (RecordT r) = braces (align (vt (Map.toAscList r)))
  where vt [] = empty
        vt [(k, t)] = label k <> ":" <+> group (prettyType t)
        vt ((k, t):tes) = label k <> ":" <+> group (prettyType t) <> "," <$> vt tes
prettyType (VariantT r) = "[|" <+> align (vt (Map.toAscList r)) <+> "|]"
  where vt [] = empty
        vt [(k, t)] = tag k <> ":" <+> group (prettyType t)
        vt ((k, t):tes) = tag k <> ":" <+> group (prettyType t) <> "|" <$> vt tes
prettyType (FunT a b) = parens $ prettyType a <+> "->" <+> prettyType b
prettyType otherwise = pretty (show otherwise)

prettyCode :: Expr -> Doc
prettyCode (VBool b) = pretty b
prettyCode (VInt i) = pretty i
prettyCode (VText t) = "\"" <> pretty (unpack t) <> "\""
prettyCode (Var Nothing v) = prettyVariable v
prettyCode (Var (Just t) v) = prettyVariable v -- <> ":" <+> prettyType t
prettyCode (Record es) =
  braces (align (ke (Map.toAscList es)))
  where
    ke [] = empty
    ke [(k, e)] = label k <> " = " <> group (prettyCode e)
    ke ((k, e):kes) = label k <> " = " <> group (prettyCode e) <> "," <$> ke kes
prettyCode (List _ es) =
  brackets (align (ke (V.toList es)))
  where
    ke [] = empty
    ke [e] = group $ prettyCode e
    ke (e:es) = group (prettyCode e) <> "," <$> ke es
prettyCode (Tag t e) = parens $ align $ tag t </> prettyCode e
prettyCode (Switch _ e cs) = hang 2 $ magenta "switch" <+> prettyCode e <$> cases (Map.toAscList cs)
  where
    cases [] = empty
    cases [c] = case' c
    cases (c:cs) = case' c <$> cases cs
    case' (t, (v, e)) = hang 2 $ magenta "case" <+> green (pretty (unpack t)) <+> prettyVariable v <+> "=>" </> prettyCode e
prettyCode (App a b) =
  -- red "(" <> prettyCode a <+> red "$" <+> prettyCode b <> red ")"
  prettyCode a </> prettyCode b
prettyCode (Proj _ l e) =
  prettyCode e <> magenta "." <> label l
prettyCode (DynProj _ a b) =
  parens (prettyCode b) <> magenta "!" <> parens (prettyCode a)
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
prettyCode (Lam _ x e) =
  parens $ hang 2 $ magenta "λ" <> prettyVariable x <> "." <$> prettyCode e
prettyCode (Closure x env e) =
  hang 2 $ parens $ red "λ" <> prettyVariable x <> "." </> prettyCode e
prettyCode (If c t e) =
  align $ magenta "if" <+> group (prettyCode c) <$> hang 2 (magenta "then" </> prettyCode t) <$> hang 2 (magenta "else" </> prettyCode e)
prettyCode (RecordMap _ a x y b) =
  magenta "rmap" <+> prettyCode a <+> magenta "with" <+> parens (prettyVariable x <+> "=" <+> prettyVariable y) <+> "=>" </> prettyCode b
prettyCode (Lookup _ b) =
  magenta "lookup" <+> prettyCode b
prettyCode (Undefined t) =
  magenta "undefined" <+> prettyCode (VText t)
prettyCode (Self b e) =
  magenta "self" <+> prettyCode b <+> prettyCode e
prettyCode other = string (show other)

printCode :: Handle -> Expr -> IO ()
printCode h c = displayIO h (renderSmart 0.8 120 (prettyCode c))

printType :: Handle -> Type -> IO ()
printType h t = displayIO h (renderPretty 0.8 120 (prettyType t))
