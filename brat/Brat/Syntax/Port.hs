module Brat.Syntax.Port where

import Brat.Naming (Name)

type PortName = String

data OutPort = Ex Name Int deriving (Eq, Ord, Show)
data InPort = In Name Int deriving (Eq, Show)

data NamedPort e = NamedPort {end :: e
                             ,portName :: PortName
                             } deriving Show

instance (Eq e) => Eq (NamedPort e) where
  (NamedPort {end=e1}) == NamedPort {end=e2} = e1 == e2

type Src = NamedPort OutPort
type Tgt = NamedPort InPort
