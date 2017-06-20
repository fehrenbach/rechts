{-# LANGUAGE OverloadedStrings #-}

module Pretty where

import Syntax
import Text.PrettyPrint.ANSI.Leijen
import System.IO (Handle)
import Data.Text (Text, unpack)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

prettyVariable :: Variable -> Doc
prettyVariable (NamedVar n) = pretty (unpack n)

label :: Text -> Doc
label t = blue (pretty (unpack t))

prettyPrefix PEmpty = dullyellow ":"
prettyPrefix (PLeft p) = dullyellow $ "l" <> prettyPrefix p
prettyPrefix (PRight p) = dullyellow $ "r" <> prettyPrefix p
prettyPrefix (PList i p) = dullyellow $ brackets (pretty i) <> prettyPrefix p


prettyValue :: Value -> Doc
prettyValue (VBool b) = pretty b
prettyValue (VInt i) = pretty i
prettyValue (VText t) = "\"" <> pretty (unpack t) <> "\""
prettyValue (VFun v _ e) = "function"
prettyValue (VRecord flds) = braces (align (kv (Map.toAscList flds)))
  where
    kv [] = empty
    kv [(k, v)] = label k <> " = " <> group (prettyValue v)
    kv ((k, v):kvs) = label k <> " = " <> group (prettyValue v) <> "," </> kv kvs
prettyValue (VVector v) = brackets $ align $ fillSep (els (V.toList v))
  where
    els [] = []
    els [(l, v)] = [prettyPrefix l <> prettyValue v]
    els ((l, v):ls) = (prettyPrefix l <> prettyValue v <> ","):els ls 
    
prettyValue (VTagged t v) = parens $ align $ green (pretty (unpack t)) </> group (prettyValue v)

printValue :: Handle -> Value -> IO ()
printValue h v = displayIO h (renderSmart 0.8 120 (prettyValue v))
