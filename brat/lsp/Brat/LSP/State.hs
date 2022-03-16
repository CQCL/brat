module Brat.LSP.State (ProgramState(..), emptyPS, ps) where

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

ps :: ([Decl], [TypedHole]) -> ProgramState
ps (decls, holes) = PS decls [] holes
