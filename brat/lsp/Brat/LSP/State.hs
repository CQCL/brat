module Brat.LSP.State (ProgramState(..), emptyPS, ps) where

import Brat.Checker (TypedHole)
import Brat.Syntax.Core
import Brat.Syntax.Raw

data ProgramState
  = PS { ndecls :: [NDecl]
       , vdecls :: [VDecl]
       , aliases :: [(String, TypeAlias)]
       , holes :: [TypedHole]
       } deriving Show

emptyPS :: ProgramState
emptyPS = PS [] [] [] []

ps :: ([NDecl], [VDecl], [TypedHole]) -> ProgramState
ps (nouns, verbs, holes) = PS nouns verbs [] holes
