module Brat.Compile.Circuit where

import Data.Aeson

type Classical = ()
type Conditional = ()
type Box = ()

data Pauli = I | X | Y | Z deriving (Show, ToJSON)

data Box = Box { _type :: OpType
               , id :: Int -- Uh oh need to keep track of this now
               , paulis :: Maybe [Pauli]
               } deriving (Eq, Show)

data OpType
  = Condition
  | ClassicalTransform
  | CopyBits
  | SetBits
  | MultiBit
  | RangePredicate
  | ExplicitModifier
  deriving (Show, ToJSON)

data Operation = Op { _type :: OpType
                    , n_qb :: Int
                    , params :: Array
                    , box :: Maybe Box
                    , conditional :: Maybe Conditional
                    , classical :: Maybe Classical
                    } deriving (Show, ToJSON) -- TODO: work out how maybe works with JSON

data Command = Command { op :: Operation
                       , args :: [UnitId]
                       } deriving (Show, ToJSON)

type Qubit = ()

-- Left register, Right (qu)bit, Right (qu)bit, ...
type UnitId = [Either String Int]

type Array = [UnitId]

data Circuit
  = Circuit { phase  :: String
            , qubits :: UnitId
            , bits   :: UnitId
            , permutation :: ()
            , commands :: [Command]
            } deriving (Show, Eq, ToJSON)

