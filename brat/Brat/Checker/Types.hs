module Brat.Checker.Types (Overs, Unders, Outputs, Connectors
                          ,Mode(..), Modey(..)
                          ,Graph, Node, Wire
                          ,Env, VEnv, KEnv, EnvData
                          ,TypedHole(..)
                          ,ValueType
                          ) where

import Brat.Checker.Quantity
import Brat.Graph (Graph, Node, Wire, Src, Tgt)
import Brat.FC (FC)
import Brat.Naming (Name)
import Brat.Syntax.Common (Dir(..), Kind(..))
import Brat.Syntax.Core (SType, VType)
import Brat.UserName (UserName)

import Data.Kind (Type)
import qualified Data.Map as M

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

type family EnvData (m :: Mode) where
  EnvData Brat = [(Src, VType)]
  EnvData Kernel = (Quantity, (Src, SType))

type Env e = M.Map UserName e
type VEnv = Env (EnvData Brat)
type KEnv = Env (EnvData Kernel)

data TypedHole
  = NBHole Name FC [String] (Connectors Brat Chk Noun)
  | VBHole Name FC (Connectors Brat Chk Verb)
  | NKHole Name FC (Connectors Kernel Chk Noun)
  | VKHole Name FC (Connectors Kernel Chk Verb)
  deriving (Eq, Show)

data Modey :: Mode -> Type where
  Braty :: Modey Brat
  Kerny :: Modey Kernel