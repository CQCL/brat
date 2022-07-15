{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

module Brat.Compile.Circuit (Circuit(..)
                            ,Command(..)
                            ,Operation(..)
                            ,compileCircuit
                            ,process
                            ,wrapCircuit
                            ) where

import Control.Monad (unless)
import Data.Array ((!))
import Data.Graph as Graph
import Data.Maybe (fromJust)
import Lens.Micro hiding (_Just, _Nothing)
import Data.ProtoLens (defMessage)
import Data.ProtoLens.Prism
import qualified Data.Map as M
import Data.Text (Text, pack)

import Brat.Graph as BG
import Brat.Syntax.Core (SType, Term(..))
import Brat.Syntax.Common
import Proto.Graph as PG
import Proto.Graph_Fields as PG

import Debug.Trace

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

data Circuit
  = Circuit { phase  :: String
            , qubits :: Int
            , bits   :: Int
            , permutation :: ()
            , commands :: [Command]
            } deriving Show

process :: BG.Graph
        -> (Row Term, Row Term)
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
  count :: (SType -> Int) -> Row Term -> Int
  count f (R r) = sum $ fmap (f . snd) r

  countQ :: SType -> Int
  countQ (Q _) = 1
  countQ Bit = 0
  -- Absolute hack
  countQ (Of sty (Simple (Num n))) | copyable sty = 0
                                   | otherwise = n
  countQ (Rho r) = count countQ r

  countB :: SType -> Int
  countB (Q _) = 0
  countB Bit = 1
  -- Absolute hack
  countB (Of sty (Simple (Num _))) | copyable sty = 1
                                   | otherwise = 0
  countB (Rho r) = count countB r

  smth :: BG.Graph -> Maybe [Command]
  smth graph = do
    let (g, f, _) = toGraph graph
    let t = transposeG g
    let sources = [ f n | n <- topSort g, t ! n == []]
    traceM ("sources: " ++ show sources)
    traceM ("ins: " ++ show ins)
    unless (length sources == length ins) $ Nothing
    traceShowM sources
    pure []

none :: PG.Value
none = let nothing :: PG.OptionValue = defMessage & PG.maybe'inner .~ Nothing in
         defMessage & PG.maybe'option .- nothing
         
-- Shortcut for setting a `maybe` field
(.-) :: ASetter s t k (Maybe v) -> v -> s -> t
k .- v = k .~ (_Just # v)

circuit2Tierkreis :: Circuit -> PG.StructValue
circuit2Tierkreis Circuit{..} = defMessage & PG.map .~ m
 where
  m :: M.Map Text PG.Value
  m = M.fromList
      [("implicitPermutation", emptyStruct)
      ,("bits",     toReg "c" bits)
      ,("commands", defMessage & PG.maybe'vec .- cmds)
      ,("name",     none)
      ,("phase",    defMessage & PG.maybe'flt .- 0.0)
      ,("qubits",   toReg "q" qubits)
      ]

  mkCmd :: Command -> PG.Value
  mkCmd Cmd{..} = let qs = defMessage
                           & PG.maybe'vec .- (defMessage
                                             & PG.vec .~ (toReg "q" <$> args))
                      m :: M.Map Text PG.Value
                        = M.fromList
                          [("op"
                           ,defMessage & PG.maybe'str .- pack (opType op))
                          ,("args", qs)]
                      struct :: PG.StructValue = defMessage & PG.map .~ m
                  in  defMessage & PG.maybe'struct .- struct

  cmds :: PG.VecValue
  cmds = defMessage & PG.vec .~ (mkCmd <$> commands)

  toReg :: Text -> Int -> PG.Value
  toReg reg n = let structs :: [PG.StructValue]
                      = (\bit -> defMessage & PG.map .~ M.fromList [("reg_name", mkStr reg)
                                                                   ,("index", mkStr . pack $ show bit)])
                        <$> [0..n-1]
                    vecVal = defMessage & PG.vec .~ ((\x -> defMessage & PG.maybe'struct .- x)
                                                     <$> structs)
                in  defMessage & PG.maybe'vec .- vecVal

  mkStr :: Text -> PG.Value
  mkStr txt = defMessage & PG.maybe'str .- txt

  emptyStruct :: PG.Value
  emptyStruct = let struct :: PG.StructValue = (defMessage & PG.map .~ M.empty) in
                  defMessage & PG.maybe'struct .- struct

compileCircuit :: BG.Graph
               -> (Row Term, Row Term)
               -> PG.Value
compileCircuit tm tys = defMessage & PG.maybe'struct .- (circuit2Tierkreis $ process tm tys)

empty :: PG.Empty
empty = defMessage

wrapCircuit :: PG.Value -> PG.Graph
wrapCircuit v = let node :: PG.Node = defMessage & PG.maybe'const .~ (_Just # v) in
                   defMessage
                   & PG.nodes .~ (M.fromList
                                 [("circuit", node)
                                 ,("output", defMessage
                                             & PG.maybe'output .~ (_Just # empty))
                                 ])
                   & PG.edges .~ [defMessage
                                 & PG.portFrom .~ "value"
                                 & PG.portTo   .~ "value"
                                 & PG.nodeFrom .~ "circuit"
                                 & PG.nodeTo   .~ "output"
                                ]
