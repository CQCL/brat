module Brat.Checker.Types (Overs, Unders
                          ,Outputs, Inputs
                          ,ChkConnectors, SynConnectors
                          ,Mode(..), Modey(..)
                          ,Graph, Node, Wire
                          ,Env, VEnv, KEnv, EnvData
                          ,TypedHole(..)
                          ,ValueType
                          ) where

import Brat.Checker.Quantity
import Brat.Graph (Graph, Node, Wire)
import Brat.FC (FC)
import Brat.Naming (Name)
import Brat.Syntax.Common (Dir(..), Kind(..), Src, Tgt)
import Brat.Syntax.Core (SType, VType)
import Brat.UserName (UserName)

import Data.Kind (Type)
import qualified Data.Map as M

-- Inputs against which a term is checked
type family Overs (m :: Mode) (k :: Kind) :: Type where
  Overs m Noun = ()
  Overs m UVerb = [(Src, ValueType m)]
  Overs m KVerb = ()

-- Inputs synthesized by the term
type family Inputs (m:: Mode) (k :: Kind) :: Type where
  Inputs m Noun = ()
  Inputs m UVerb = ()
  Inputs m KVerb = [(Tgt, ValueType m)]

-- Outputs against which a term is checked
type family Unders (m :: Mode) (d :: Dir) :: Type where
  Unders m Syn = ()
  Unders m Chk = [(Tgt, ValueType m)]

-- Outputs synthesized by the term
type family Outputs (m :: Mode) (d :: Dir) :: Type where
  Outputs m Syn = [(Src, ValueType m)]
  Outputs m Chk = ()

type ChkConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)
type SynConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Inputs m k, Outputs m d)

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
  = NBHole Name FC [String] (ChkConnectors Brat Chk Noun)
  | VBHole Name FC (ChkConnectors Brat Chk UVerb)
  | NKHole Name FC (ChkConnectors Kernel Chk Noun)
  | VKHole Name FC (ChkConnectors Kernel Chk UVerb)
  deriving (Eq, Show)

data Modey :: Mode -> Type where
  Braty :: Modey Brat
  Kerny :: Modey Kernel
