{-# LANGUAGE UndecidableInstances #-}

module Brat.Graph where

import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Brat.UserName

import Hasochism (N(..))

import qualified Data.Graph as G
import qualified Data.Map as M
import Data.List.NonEmpty (NonEmpty)
import Data.Kind (Type)

data Node
  -- Inputs first, then outputs
  = BratNode (Thing Brat) [(PortName, Val Z)] [(PortName, Val Z)]
  | KernelNode (Thing Kernel) [(PortName, Val Z)] [(PortName, Val Z)]
 deriving Show

nodeIns :: Node -> [(PortName, Val Z)]
nodeIns (BratNode _ ins _) = ins
nodeIns (KernelNode _ ins _) = ins

nodeOuts :: Node -> [(PortName, Val Z)]
nodeOuts (BratNode _ _ outs) = outs
nodeOuts (KernelNode _ _ outs) = outs

data ComboType = Row | Thunk deriving (Eq, Show)

data Thing :: Mode -> Type where
  Prim  :: (String, String) -> Thing Brat  -- Something external
  Const :: SimpleTerm -> Thing a
  Eval  :: OutPort -> Thing Brat   -- A computation on a wire
  Splice :: OutPort -> Thing Kernel  -- A computation (classical) to add to this kernel
  (:>>:) :: Name -> Name -> Thing Brat -- Graph in a box - Names are those of Source and Target nodes
  Source :: Thing a  -- For building..
  Target :: Thing a  -- ..boxes
  Id     :: Thing a  -- Identity node for convenient wiring
  TestMatch :: TestMatchData a -> Thing a -- pattern match LHS as conjunctive sequence
  FunClauses :: (NonEmpty
                 ( Name  -- The node for the LHS test match
                 , Name  -- The node for the RHS box
                )) -> Thing a
  Hypo :: Thing a  -- Hypothesis for type checking
  Constructor :: UserName -> Thing a
  Selector :: UserName -> Thing a -- TODO: Get rid of this in favour of FunClauses based matching
  ArithNode :: ArithOp -> Thing Brat

deriving instance Show (Thing a)

-- TestMatch nodes take the function's input row as inputs and yield one
-- output, namely a value in a sum type
-- tag 0 with the function's inputs returned as they were
-- tag 1 with the environment of pattern variables from a successful
data TestMatchData (m :: Mode) where
  TestMatchData :: Show (BinderType m) => Modey m -> MatchSequence (BinderType m) -> TestMatchData m

deriving instance Show (TestMatchData a)

-- A collections of tests to determine if a clause matches.
-- Invariants:
--    1. Each src in `matchTests` has been mentioned earlier (either in `matchInputs`
--       or in the srcs outputted by a previous `PrimCtorTest`
--    2. The same goes for the sources in `matchOutputs`
data MatchSequence ty = MatchSequence
  { matchInputs :: [(Src, ty)]
  , matchTests :: [(Src, PrimTest ty)]
  , matchOutputs ::[(Src, ty)]
  } deriving (Foldable, Functor, Traversable)
deriving instance Show ty => Show (MatchSequence ty)

data PrimTest ty
  = PrimCtorTest
      UserName      -- the data constructor
      UserName      -- the type constructor
      -- (CtorArgs m)  -- (hope we don't need) its entry in the constructor table
      Name          -- the name of the node which "outputs" the data packed inside
      [(Src, ty)]  -- ...these sources for extracted data descend
  | PrimLitTest
      SimpleTerm    -- the literal against which we're testing for equality
 deriving (Foldable, Functor, Traversable)
deriving instance Show ty => Show (PrimTest ty)

primTestOuts :: PrimTest ty -> [(Src, ty)]
primTestOuts (PrimCtorTest _ _ _ xs) = xs
primTestOuts (PrimLitTest _) = []

{- TODO: update the repertoire of available `Thing`s to reflect what hugr lets us do

In particular, we need conditional nodes (with a list of pairs of source and target nodes).
For each primitive test on type tau, we need
  try : tau -> tau + rho
  retreat : rho -> tau

where try gives you some pieces if you succeed and your input back if you don't, and
retreat reassembles the input from the pieces in the situation where a test succeeds
but a subsequent test fails.

We adopt the same style when compiling the left hand side of a clause: we either give
you the values of the pattern variables or your old data back. These are given as
right-nested trees of trys, where the left forks retreat.

IN FACT, the Brat graph should have nodes which specify the tests in these trees, not the
details of how they turn into hugr. We may find ourselves with different sorts of
special-purpose conditionals, corresponding to the ways compiled Brat uses hugr. We
should say which trope of hugr construction we need, rather than doing it here and now.
-}

data LogicOp = LNot | LOr | LAnd deriving (Eq, Show)

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
