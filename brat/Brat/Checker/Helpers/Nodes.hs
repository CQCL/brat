{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Helpers.Nodes where

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Graph
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Bwd

constNode :: DeBruijn (BinderType m) => Modey m -> BinderType m -> SimpleTerm -> Checking Src
constNode m ty tm = let ?my = m in do
  (_, _, [(value,_)], _) <- anext (show tm) (Const tm) (B0,B0) [] [("value", ty)]
  pure value
