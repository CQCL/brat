module Brat.LSP.State (ProgramState(..), emptyPS, updateState) where

import Brat.Checker (TypedHole)
import Brat.Syntax.Raw
import Brat.Syntax.Value (VDecl)

data ProgramState
  = PS { decls :: [VDecl]
       , aliases :: [(String, TypeAlias)]
       , holes :: [TypedHole]
       } deriving Show

emptyPS :: ProgramState
emptyPS = PS [] [] []

updateState :: ([VDecl], [TypedHole]) -> ProgramState -> ProgramState
updateState (decls, holes) st = st { decls = decls, holes = holes }
