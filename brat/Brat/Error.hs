module Brat.Error (ParseError(..)
                  ,LengthConstraintF(..), LengthConstraint
                  ,ErrorMsg(..)
                  ,Error(..), showError
                  ,SrcErr(..)
                  ,addSrcName, addSrcContext
                  ,eitherIO
                  ,dumbErr
                  ) where

import Brat.FC

import System.Exit

newtype ParseError = PE { pretty :: String }

instance Show ParseError where
  show pe = pretty pe

data LengthConstraintF a = Length a | LongerThan a deriving (Eq, Functor)
instance Show a => Show (LengthConstraintF a) where
  show (Length a) = show a
  show (LongerThan a) = "(> " ++ show a ++ ")"

type LengthConstraint = LengthConstraintF Int

data ErrorMsg
 = TypeErr String
 | TypeMismatch String String String
 | ExpectedThunk String String
 | PattErr String
 | VarNotFound String
 | KVarNotFound String
 | NothingToBind String
 -- Expected Length, Type, Actual Length, Actual term
 | VecLength Int String LengthConstraint String
 -- Binder, Type
 | VecPatLength String String
 -- Term, Type
 | NotVecPat String String

 | EmptyRow String
 | MultipleOutputsForThunk String
 | VecEval String
 | ParseErr ParseError
 | LexErr ParseError
 | ElabErr String
 | DesugarErr String
 | EvalErr String
 | NameClash String
 | MainNotFound
 | BadCons String
 -- function, [argument]
 | Unimplemented String [String]
 | ImportCycle String String
 | FileNotFound String
 | AmbiguousPortPull String String
 | InternalError String

instance Show ErrorMsg where
  show (TypeErr x) = "Type error: " ++ x
  show (TypeMismatch tm exp act)
    = unlines ["Type mismatch when checking " ++ tm
              ,"Expected: " ++ exp
              ,"But got:  " ++ act
              ]
  show (ExpectedThunk m row)
    = unlines ["Expected function to be a " ++ m ++ "thunk, but found:"
              ,"  " ++ row
              ]
  show (NothingToBind x) = "Nothing to bind to: " ++ x
  show (VecLength m ty l tm) = unlines ["Expected vector of length " ++ show m
                                       ,"from the type:  " ++ ty
                                       ,"but got vector: " ++ tm
                                       ,"of length " ++ show l
                                       ]
  show (VecPatLength abs ty) = unlines ["Pattern: " ++ abs
                                       ,"doesn't match type " ++ ty
                                       ,"(because it's the wrong length)"
                                       ]
  show (NotVecPat tm ty)= unwords ["Expected", tm
                                  ,"to be a vector pattern when binding type", ty]

  show (EmptyRow fn) = "Declaration of " ++ fn ++ " doesn't have any outputs"
  show (MultipleOutputsForThunk fn) = unwords ["Declaration of"
                                              ,fn
                                              ,"has too many outputs:"
                                              ,"expected one thunk type"
                                              ]
  show (VecEval n) = "Couldn't determine that " ++ n ++ " is a Nat"
  show (PattErr x) = "Type error in pattern: " ++ x
  show (ParseErr x) = "Parse error " ++ show x
  show (LexErr x) = "Lex error " ++ show x
  show (ElabErr x) = "Elab error " ++ show x
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
  show (AmbiguousPortPull p row) = "Port " ++ p ++ " is ambiguous in " ++ row
  show (InternalError x) = "Internal error: " ++ x

data Error = Err { fc  :: Maybe FC
                 , msg :: ErrorMsg
                 }
-- We could make this just 'instance Show' but this makes the few cases
-- where we show an Error (without filename or contents) explicit.
showError :: Error -> String
showError (Err _ msg) = show msg

data SrcErr = SrcErr String Error

instance Show SrcErr where
  show (SrcErr prelim Err{msg=msg}) = unlines [prelim, "  " ++ (show msg)]

errHeader :: String -> String
errHeader name = "Error in " ++ name ++ ":"

addSrcName :: String -> Error -> SrcErr
addSrcName fname err = SrcErr (errHeader fname) err

addSrcContext :: String -> String -> Either Error t -> Either SrcErr t
addSrcContext _ _ (Right r) = Right r
addSrcContext fname cts (Left err@Err{fc=fc}) = Left (SrcErr msg err)
 where
  msg = case fc of
    Just fc -> unlines ((errHeader $ fname ++ '@':(show fc)):
                        (showFileContext cts fc))
    Nothing -> errHeader fname

showFileContext :: String -> FC -> [String]
showFileContext contents fc = let
    -- taking 1 off to convert 1-indexed user line numbers to 0-indexed list indices
    startLineN = line (start fc) - 1
    endLineN = line (end fc) - 1
    startCol = col (start fc) - 1
    endCol = col (end fc) - 1 -- exclusive
    ls = lines contents
  in if startLineN == endLineN then
      [ls!!startLineN, highlightSection startCol endCol]
    else let (first:rest) = drop (startLineN - 1) $ take (endLineN + 1) ls
             (last:rmid) = reverse rest
          in [first, highlightSection startCol (length first)]
            ++ ((reverse rmid) >>= (\l -> [l, highlightSection 0 (length l)]))
            ++ [last, highlightSection 0 endCol]
 where
  highlightSection :: Int -> Int -> String
  highlightSection start end =
    (replicate start ' ') ++ (replicate (end - start) '^')


eitherIO :: Either SrcErr a -> IO a
eitherIO (Left e) = die (show e)
eitherIO (Right a) = pure a

dumbErr :: ErrorMsg -> Error
dumbErr = Err Nothing
