module Brat.Checker.Types (Overs, Unders, Outputs, Connectors
                          ,Mode(..)
                          ,Graph, Node, Wire
                          ,VEnv, KEnv
                          ,TypedHole(..)
                          ) where

import Brat.Checker.Quantity
import Brat.Graph (Graph', Node', Wire', Src, Tgt)
import Brat.FC (FC)
import Brat.Naming (Name)
import Brat.Syntax.Common (Dir(..), Kind(..))
import Brat.Syntax.Core (SType, VType, Term)
import Brat.UserName (UserName)

import Data.Kind (Type)
import qualified Data.Map as M

type Graph = Graph' Term
type Node = Node' Term
type Wire = Wire' Term

type family Overs (m :: Mode) (k :: Kind) :: Type where
  Overs m Noun = ()
  Overs m Verb = [(Src, ValueType m)]

type family Unders (m :: Mode) (d :: Dir) :: Type where
  Unders m Syn = ()
  Unders m Chk = [(Tgt, ValueType m)]

type family Outputs (m :: Mode) (d :: Dir) :: Type where
  Outputs m Syn = [(Src, ValueType m)]
  Outputs m Chk = ()

type Connectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)

data Mode = Brat | Kernel

type family ValueType (m :: Mode) where
  ValueType Brat = VType
  ValueType Kernel = SType

type VEnv = [(UserName, [(Src, VType)])]
type KEnv = M.Map UserName (Quantity, (Src, SType))

data TypedHole
  = NBHole Name FC [String] (Connectors Brat Chk Noun)
  | VBHole Name FC (Connectors Brat Chk Verb)
  | NKHole Name FC (Connectors Kernel Chk Noun)
  | VKHole Name FC (Connectors Kernel Chk Verb)
  deriving (Eq, Show)
