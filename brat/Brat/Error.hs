module Brat.Error where

import Brat.FC

import System.Exit

newtype ParseError = PE { pretty :: String }

instance Show ParseError where
  show pe = pretty pe

data ErrorMsg
 = TypeErr String
 | TypeMismatch String String String
 | ExpectedThunk String
 | PattErr String
 | VarNotFound String
 | KVarNotFound String
 | NothingToBind String
 -- Expected, type, Actual, term
 | VecLength Int String String String
 -- Binder, Type
 | VecPatLength String String
 -- Term, Type
 | NotVecPat String String

 | VecEval String
 | ParseErr ParseError
 | LexErr ParseError
 | DesugarErr String
 | EvalErr String
 | NameClash String
 | MainNotFound
 | BadCons String
 -- function, [argument]
 | Unimplemented String [String]
 | ImportCycle String String
 | FileNotFound String
 | InternalError String

instance Show ErrorMsg where
  show (TypeErr x) = "Type error: " ++ x
  show (TypeMismatch tm exp act)
    = unlines ["Type mismatch when checking " ++ tm
              ,"Expected: " ++ exp
              ,"But got:  " ++ act
              ]
  show (ExpectedThunk row)
    = unlines ["Expected function to be a thunk, but found:"
              ,"  " ++ row
              ]
  show (NothingToBind x) = "Nothing to bind to: " ++ x
  show (VecLength m ty n tm) = unlines ["Expected vector of length " ++ show m
                                       ,"from the type:  " ++ ty
                                       ,"but got vector: " ++ tm
                                       ,"of length " ++ n
                                       ]
  show (VecPatLength abs ty) = unlines ["Pattern: " ++ abs
                                       ,"doesn't match type " ++ ty
                                       ,"(because it's the wrong length)"
                                       ]
  show (NotVecPat tm ty)= unwords ["Expected", tm
                                  ,"to be a vector pattern when binding type", ty]
  show (VecEval n) = "Couldn't determine that " ++ n ++ " is a Nat"
  show (PattErr x) = "Type error in pattern: " ++ x
  show (ParseErr x) = "Parse error " ++ show x
  show (LexErr x) = "Lex error " ++ show x
  show (DesugarErr x) = "Desugar error " ++ x
  show (EvalErr x) = "Eval error " ++ x
  show (NameClash x) = "Name clash: " ++ x
  show (VarNotFound x) = x ++ " not found in (value) environment"
  show (KVarNotFound x) = x ++ " not found in kernel context"
  show MainNotFound = "No function found called \"main\""
  show (BadCons x) = "Expected two arguments to `cons` but got: " ++ x
  show (Unimplemented f args) = unwords ("Unimplemented, sorry! --":f:args)
  show (ImportCycle a b) = unwords ["Cycle detected in imports:", a, "is reachable from", b]
  show (FileNotFound f) = "File not found: " ++ show f
  show (InternalError x) = "Internal error: " ++ x

data Error = Err { fc  :: Maybe FC
                 , src :: Maybe String
                 , msg :: ErrorMsg
                 }
instance Show Error where
  show (Err mfc (Just src) msg)
    = let bonus = maybe "" (\fc -> '@':show fc) mfc in
        unlines ["Error in " ++ src ++ bonus ++ ":"
                ,"  " ++ show msg
                ]
  show (Err _ Nothing msg) = show msg

addSrc :: String -> Error -> Error
addSrc name (Err fc _ msg) = Err fc (Just name) msg

eitherIO :: Either Error a -> IO a
eitherIO (Left e) = die (show e)
eitherIO (Right a) = pure a

dumbErr :: ErrorMsg -> Error
dumbErr = Err Nothing Nothing
