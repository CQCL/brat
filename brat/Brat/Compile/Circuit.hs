{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module Brat.Compile.Circuit where

import Lens.Micro hiding (_Just, _Nothing)
import Lens.Micro.Type (ASetter)
import qualified Data.Map as M
import Data.ProtoLens (defMessage)
import Data.ProtoLens.Prism
import Proto.Graph as G
import Proto.Graph_Fields as G
import Data.Text (Text)
import Brat.Syntax.Core (VType, Term(..))
import Brat.Syntax.Common (Quantum, Row(..), SType, Dir(..), Kind(..))

type Classical = ()
type Conditional = ()

data Pauli = I | X | Y | Z deriving Show

data Box = Box { boxType :: OpType
               , id :: Int -- Uh oh need to keep track of this now
               , paulis :: Maybe [Pauli]
               } deriving Show

data OpType
  = Condition
  | ClassicalTransform
  | CopyBits
  | SetBits
  | MultiBit
  | RangePredicate
  | ExplicitModifier
  deriving Show

data Operation = Op { opType :: OpType
                    , n_qb :: Int
                    , params :: Array
                    , box :: Maybe Box
                    , conditional :: Maybe Conditional
                    , classical :: Maybe Classical
                    } deriving Show

data Command = Command { op :: Operation
                       , args :: [UnitId]
                       } deriving Show

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
            } deriving Show

process :: Term Chk Noun
        -> (Row Term Quantum, Row Term Quantum)
        -> Circuit
process tm (ins, outs) = undefined

none :: G.Value
none = let nothing :: G.OptionValue = defMessage & G.maybe'inner .~ Nothing in
         defMessage & G.maybe'option .~ (_Just # nothing)
         
-- Shortcut for setting a `maybe` field
(.-) :: ASetter s t k (Maybe v) -> v -> s -> t
k .- v = k .~ (_Just # v)

circuit2Tierkreis :: Circuit -> G.StructValue
circuit2Tierkreis Circuit{..} = defMessage & G.map .~ m
 where
  m :: M.Map Text G.Value
  m = M.fromList
      [("implicitPermutation", emptyStruct)
      ,("bits",     defMessage & G.maybe'vec .- bits)
      ,("commands", defMessage & G.maybe'vec .- commands)
      ,("name",     none)
      ,("phase",    defMessage & G.maybe'flt .- 0.0)
      ,("qubits",   defMessage & G.maybe'vec .- qubits)
      ]

  bits :: G.VecValue
  bits = undefined

  commands :: G.VecValue
  commands = undefined

  qubits :: G.VecValue
  qubits = undefined

  emptyStruct :: G.Value
  emptyStruct = let struct :: G.StructValue = (defMessage & G.map .~ M.empty) in
                  defMessage & G.maybe'struct .~ (_Just # struct)
