{-# LANGUAGE ScopedTypeVariables, UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName

import Hasochism (N(..))

import qualified Data.Graph as G
import qualified Data.Map as M

data Node
  -- Inputs first, then outputs
  = BratNode Thing [(PortName, Val Z)] [(PortName, Val Z)]
  | KernelNode Thing [(PortName, Val Z)] [(PortName, Val Z)]
 deriving Show

nodeThing :: Node -> Thing
nodeThing (BratNode t _ _) = t
nodeThing (KernelNode t _ _) = t

data ComboType = Row | Thunk deriving (Eq, Show)

data Thing
  = Prim String  -- Something in the env
  | Const SimpleTerm
  | Eval OutPort   -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Constructor UserName
  | Selector UserName
  | ArithNode ArithOp
  deriving (Eq, Show)

type Graph = (M.Map Name Node, [Wire])
emptyGraph :: Graph
emptyGraph = (M.empty, [])

instance {-# OVERLAPPING #-} Show Graph where
  show (ns, ws) = unlines (("Nodes:":(show <$> M.toList ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire = (OutPort, Val Z, InPort)

toGraph :: Graph -> (G.Graph, G.Vertex -> (Node, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges adj
 where
  -- TODO: Reduce the complexity (O(n^2)) of this function
  adj = [ (node
          ,name
          ,[ tgt | (Ex src _, _, In tgt _) <- ws, src == name ]
          )
        | (name, node) <- M.toList ns]

wiresFrom :: Name -> Graph -> [Wire]
wiresFrom src (_, ws) = [ w | w@(Ex a _, _, _) <- ws, a == src ]

lookupNode :: Name -> Graph -> Maybe (Node)
lookupNode name (ns, _) = M.lookup name ns

wireStart :: Wire -> Name
wireStart (Ex x _, _, _) = x

wireEnd :: Wire -> Name
wireEnd (_, _, In x _) = x
