{-# LANGUAGE UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

import qualified Data.Graph as G

data Node' tm
  = BratNode Name Thing [Input' tm] [Output' tm]
  | KernelNode Name Thing [(Port, SType tm)] [(Port, SType tm)]

nodeName :: Node' tm -> Name
nodeName (BratNode nm _ _ _) = nm
nodeName (KernelNode nm _ _ _) = nm

nodeThing :: Node' tm -> Thing
nodeThing (BratNode _ t _ _) = t
nodeThing (KernelNode _ t _ _) = t

deriving instance Show (tm Chk Noun) => Show (Node' tm)
deriving instance Eq (tm Chk Noun) => Eq (Node' tm)

data Thing
  = Prim String  -- Something in the env
  | Eval Src     -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Combo Src Src
  deriving (Eq, Show)

type Graph' tm = ([Node' tm], [Wire' tm])
{-
newtype BGraph' tm nl el = BG ([Node tm], [Wire tm])
type BGraph tm = BGraph' tm String String

deriving instance Eq (tm Chk Noun) => Eq (BGraph tm)
deriving instance Show (tm Chk Noun) => Show (BGraph tm)
-}
instance {-# OVERLAPPING #-} Show (tm Chk Noun) => Show (Graph' tm) where
  show (ns, ws) = unlines (("Nodes:":(show <$> ns)) ++ ("":"Wires:":(show <$> ws)))

type Wire' tm = (Src, Either (SType tm) (VType' tm), Tgt)

type Src = (Name, Port)
type Tgt = (Name, Port)

type Input' tm = (Port, VType' tm)
type Output' tm = (Port, VType' tm)

toGraph :: Graph' tm -> (G.Graph, G.Vertex -> (Node' tm, Name, [Name]), Name -> Maybe G.Vertex)
toGraph (ns, ws) = G.graphFromEdges $ adj
 where
  adj = [ (n
          ,nodeName n
          ,[ tgt | ((src,_), _, (tgt, _)) <- ws, src == nodeName n ]
          )
        | n <- ns]
