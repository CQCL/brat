{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module Brat.Compile.Circuit (compileCircuit) where

import Lens.Micro hiding (_Just, _Nothing)
import Lens.Micro.Type (ASetter)
import qualified Data.Map as M
import Data.ProtoLens (defMessage)
import Data.ProtoLens.Prism
import Proto.Graph as G
import Proto.Graph_Fields as G
import Data.Text (Text)
import Brat.FC
import Brat.Syntax.Core (VType, Term(..))
import Brat.Syntax.Common
import Brat.Syntax.Raw (desugarEnv)
import Util

type Classical = ()
type Conditional = ()

data Pauli = I | X | Y | Z deriving Show

data Box = Box { boxType :: OpType
               , ident :: Int -- Uh oh need to keep track of this now
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

data Command = Command { op   :: Operation
                       , args :: [UnitId]
                       } deriving Show

type Qubit = ()

-- Left register, Right (qu)bit, Right (qu)bit, ...
type UnitId = [Either String Int]

type Array = [UnitId]

data Circuit
  = Circuit { phase  :: String
            , qubits :: Int
            , bits   :: Int
            , permutation :: ()
            , commands :: [Command]
            } deriving Show

process :: Term Chk Noun
        -> (Row Term Quantum, Row Term Quantum)
        -> Circuit
process tm (ins, outs) = let qbits = max (count countQ ins) (count countQ outs)
                             bits  = max (count countB ins) (count countB outs)
                         in  Circuit { phase  = "0.0" -- isn't actually read
                                     , qubits = qbits
                                     , bits   = bits
                                     , permutation = ()
                                     , commands = []
                                     }
 where
  count :: (SType' Term Quantum -> Int) -> Row Term Quantum -> Int
  count f (R r) = sum $ fmap (f . snd) r

  countQ :: SType' Term Quantum -> Int
  countQ (Q _) = 1
  countQ Bit = 0
  -- Absolute hack
  countQ (Of sty (Simple (Num n))) | copyable sty = 0
                                   | otherwise = n
  countQ (Rho r) = count countQ r

  countB :: SType' Term Quantum -> Int
  countB (Q _) = 0
  countB Bit = 1
  -- Absolute hack
  countB (Of sty (Simple (Num n))) | copyable sty = 1
                                   | otherwise = 0
  countB (Rho r) = count countB r

none :: G.Value
none = let nothing :: G.OptionValue = defMessage & G.maybe'inner .~ Nothing in
         defMessage & G.maybe'option .- nothing
         
-- Shortcut for setting a `maybe` field
(.-) :: ASetter s t k (Maybe v) -> v -> s -> t
k .- v = k .~ (_Just # v)

circuit2Tierkreis :: Circuit -> G.StructValue
circuit2Tierkreis Circuit{..} = defMessage & G.map .~ m
 where
  m :: M.Map Text G.Value
  m = M.fromList
      [("implicitPermutation", emptyStruct)
      ,("bits",     toReg "c" bits)
      ,("commands", defMessage & G.maybe'vec .- cmds)
      ,("name",     none)
      ,("phase",    defMessage & G.maybe'flt .- 0.0)
      ,("qubits",   toReg "q" qubits)
      ]

  cmds :: G.VecValue
  cmds = undefined

  toReg :: Text -> Int -> G.Value
  toReg reg n = let structs :: [G.StructValue]
                      = (\bit -> defMessage & G.map .~ M.fromList [("reg_name", mkStr reg)
                                                                  ,("index", mkStr . pack $ show bit)])
                        <$> [0..n-1]
                    vecVal = defMessage & G.vec .~ ((\x -> defMessage & G.maybe'struct .- x)
                                                    <$> structs)
                in  defMessage & G.maybe'vec .- vecVal

  mkStr :: Text -> G.Value
  mkStr txt = defMessage & G.maybe'str .- txt

  emptyStruct :: G.Value
  emptyStruct = let struct :: G.StructValue = (defMessage & G.map .~ M.empty) in
                  defMessage & G.maybe'struct .- struct

compileCircuit :: Term Chk Noun
               -> (Row Term Quantum, Row Term Quantum)
               -> G.Value
compileCircuit tm tys = defMessage & G.maybe'struct .- (circuit2Tierkreis $ process tm tys)
