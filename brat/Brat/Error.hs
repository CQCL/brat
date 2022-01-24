module Brat.Error where

import Brat.FC

data ParseError = PE { ugly :: String
                     , pretty :: String
                     }
instance Show ParseError where
  show pe = pretty pe

data ErrorMsg
 = TypeErr String
 | PattErr String
 | ParseErr ParseError
 | LexErr ParseError
 | DesugarErr String
 | EvalErr String
 | NameClash String
 -- function, [argument]
 | Unimplemented String [String]

instance Show ErrorMsg where
  show (TypeErr x) = "Type error: " ++ x
  show (PattErr x) = "Type error in pattern: " ++ x
  show (ParseErr x) = "Parse error " ++ show x
  show (LexErr x) = "Lex error " ++ show x
  show (DesugarErr x) = "Desugar error " ++ x
  show (EvalErr x) = "Eval error " ++ x
  show (NameClash x) = "Name clash: " ++ x
  show (Unimplemented f args) = unwords ("Unimplemented, sorry! --":f:args)

data Error = Err { fc  :: Maybe FC
                 , src :: Maybe String
                 , msg :: ErrorMsg
                 }
instance Show Error where
  show (Err _ (Just src) msg) = src ++ ": " ++ show msg
  show (Err _ Nothing msg) = show msg

debug :: Error -> String
debug e@(Err (Just fc) _ _) = unlines ["err@" ++ show fc, show e]
debug e@(Err Nothing _ _) = unlines ["err@???", show e]

addSrc :: String -> Error -> Error
addSrc name (Err fc _ msg) = Err fc (Just name) msg

