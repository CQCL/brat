{-# LANGUAGE UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common

data Thing' tm
  = Prim String  -- Something in the env
  | Eval Src     -- Something on a wire
  | Name :>>: Name -- Graph in a box
  | Source       -- For building..
  | Target       -- ..boxes
  | Id           -- Identity node for convenient wiring
  | Hypo         -- Hypothesis for type checking
  | Combo Src Src
  | Cluster [Node' tm]

deriving instance Eq (Node' tm) => Eq (Thing' tm)
deriving instance Show (Node' tm) => Show (Thing' tm)

type Graph' tm = ([Node' tm], [Wire' tm])
{-
newtype BGraph' tm nl el = BG ([Node tm], [Wire tm])
type BGraph tm = BGraph' tm String String

deriving instance Eq (tm Chk Noun) => Eq (BGraph tm)
deriving instance Show (tm Chk Noun) => Show (BGraph tm)
-}

data Node' tm
  = BratNode Name (Thing' tm) [Input' tm] [Output' tm]
  | KernelNode Name (Thing' tm) [(Port, SType tm)] [(Port, SType tm)]

deriving instance Eq (tm Chk Noun) => Eq (Node' tm)
deriving instance Show (tm Chk Noun) => Show (Node' tm)

type Wire' tm = (Src, Either (SType tm) (VType' tm), Tgt)


type Src = (Name, Port)
type Tgt = (Name, Port)

type Input' tm = (Port, VType' tm)
type Output' tm = (Port, VType' tm)
