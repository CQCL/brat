{-# LANGUAGE FlexibleContexts, TypeApplications #-}

module Brat.Checker.Helpers.Nodes where

import Brat.Checker.Helpers
import Brat.Checker.Monad
import Brat.Checker.Types
import Brat.Graph
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.Syntax.Value
import Hasochism

constNode :: Modey m -> BinderType m -> SimpleTerm -> Checking Src
constNode Braty ty tm = case ty of
  Left k -> do
    (_, _, [(value,_)], _) <- next (show tm) (Const tm) (S0, Some (Zy :* S0)) R0 (REx ("value", k) (S0 ::- R0))
    pure value
  Right ty -> do
    (_, _, [(value,_)], _) <- next (show tm) (Const tm) (S0, Some (Zy :* S0)) R0 (RPr ("value", ty) R0)
    pure value
constNode Kerny ty tm = do
  (_, _, [(value,_)], _) <- knext (show tm) (Const tm) (S0, Some (Zy :* S0)) R0 (RPr ("value", ty) R0)
  pure value
