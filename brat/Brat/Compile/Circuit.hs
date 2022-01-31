{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module Brat.Compile.Circuit (Circuit(..)
                            ,Command(..)
                            ,Operation(..)
                            ,compileCircuit
                            ,process
                            ,wrapCircuit
                            ) where

import Control.Arrow ((***), (&&&))
import Control.Monad (unless)
import Data.Array ((!))
import Data.Graph as Graph
import Data.Maybe (fromJust)
import Lens.Micro hiding (_Just, _Nothing)
import Lens.Micro.Type (ASetter)
import qualified Data.Map as M
import Data.ProtoLens (defMessage)
import Data.ProtoLens.Prism
import qualified Data.Map as Map
import Data.Text (Text, pack)

import Brat.Graph
import Brat.FC
import Brat.Naming
import Brat.Syntax.Core (VType, Term(..))
import Brat.Syntax.Common
import Brat.Syntax.Raw (desugarEnv)
import Proto.Graph as G
import Proto.Graph_Fields as G
import Util

import Debug.Trace

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

data Operation = Op { opType :: String --OpType
--                    , n_qb :: Int
                    , params :: [String]
--                    , box :: Maybe Box
--                    , conditional :: Maybe Conditional
--                    , classical :: Maybe Classical
                    } deriving (Eq, Show)

data Command = Cmd { op   :: Operation
                   , args :: [Int]
                   } deriving (Eq, Show)

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

process :: Graph' Term
        -> (Row Term Quantum, Row Term Quantum)
        -> Circuit
process tm (ins, outs) = let qbits = max (count countQ ins) (count countQ outs)
                             bits  = max (count countB ins) (count countB outs)
                         in  Circuit { phase  = "0.0" -- isn't actually read
                                     , qubits = qbits
                                     , bits   = bits
                                     , permutation = ()
                                     , commands = trace ("graph: " ++show tm) (fromJust (smth tm))
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

  cmds :: [Command]
  cmds = let (g, f, _) = toGraph tm
             ns = Graph.topSort g
             cmds = (nodeToCmd . f) <$> ns
         in  cmds

  smth :: Graph' Term -> Maybe [Command]
  smth graph = do
    let (g, f, _) = toGraph graph
    let t = transposeG g
    let sources = [ f n | n <- topSort g, t ! n == []]
    traceM ("sources: " ++ show sources)
    traceM ("ins: " ++ show ins)
    unless (length sources == length ins) $ Nothing
    traceShowM sources
    pure []

  nodeToCmd :: (Node' Term, Name, [Name]) -> Command
  nodeToCmd (KernelNode _ (Prim p) _ _, nm, tgts)
    = Cmd { op = Op { opType = p, params = [] }
          , args = [] -- hmmmmmmm!!! (TODO:)
          }

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

  mkCmd :: Command -> G.Value
  mkCmd Cmd{..} = let qs = defMessage
                           & G.maybe'vec .- (defMessage
                                             & G.vec .~ (toReg "q" <$> args))
                      m :: Map.Map Text G.Value
                        = Map.fromList [("op"
                                        ,defMessage & G.maybe'str .- pack (opType op))
                                       ,("args", qs)]
                      struct :: G.StructValue = defMessage & G.map .~ m
                  in  defMessage & G.maybe'struct .- struct

  cmds :: G.VecValue
  cmds = defMessage & G.vec .~ (mkCmd <$> commands)

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

compileCircuit :: Graph' Term
               -> (Row Term Quantum, Row Term Quantum)
               -> G.Value
compileCircuit tm tys = defMessage & G.maybe'struct .- (circuit2Tierkreis $ process tm tys)

empty :: G.Empty
empty = defMessage

wrapCircuit :: G.Value -> G.Graph
wrapCircuit v = let node :: G.Node = defMessage & G.maybe'const .~ (_Just # v) in
                   defMessage
                   & G.nodes .~ (Map.fromList [("circuit", node)
                                              ,("output", defMessage
                                                          & G.maybe'output .~ (_Just # empty))
                                              ])
                   & G.edges .~ [defMessage
                                 & G.portFrom .~ "value"
                                 & G.portTo   .~ "value"
                                 & G.nodeFrom .~ "circuit"
                                 & G.nodeTo   .~ "output"
                                ]
