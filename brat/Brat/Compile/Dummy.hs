{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}

{- This file should contain a dummy tierkreis graph into which a circuit can be
   put for demo purposes. Obviously this is a temporary hack
-}
module Brat.Compile.Dummy where

import Proto.Graph as G
import Proto.Graph_Fields as G
import Data.ProtoLens
import Data.ProtoLens.Prism
import Lens.Micro hiding (_Nothing, _Just)
import qualified Data.Map as Map

wrapCircuit :: G.Value -> G.Graph
wrapCircuit v = let node :: G.Node = defMessage & G.maybe'const .~ (_Just # v) in
                   defMessage
                   & G.nodes .~ (Map.singleton "circuit" node)
                   & G.edges .~ []
