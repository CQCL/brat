module Brat.LSP.State (ProgramState(..), emptyPS, updateState) where

import Brat.Checker (TypedHole)
import Brat.Syntax.Core
import Brat.Syntax.Raw

data ProgramState
  = PS { decls :: [Decl]
       , aliases :: [(String, TypeAlias)]
       , holes :: [TypedHole]
       } deriving Show

emptyPS :: ProgramState
emptyPS = PS [] [] []

updateState :: ([Decl], [TypedHole]) -> ProgramState -> ProgramState
updateState (decls, holes) st = st { decls = decls, holes = holes }
