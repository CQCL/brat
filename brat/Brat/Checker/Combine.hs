{-# LANGUAGE PatternSynonyms #-}

module Brat.Checker.Combine where

import Brat.Checker.Monad (Checking, AType(..))
import Brat.Graph (Src, Thing(..), ComboType(..))
import Brat.Syntax.Common (pattern R, pattern Rho, VType'(..))
import Brat.Syntax.Core (VType, SType)

import Data.List.NonEmpty (NonEmpty(..), (<|))

-- Combine types of two thunks (either classical or kernel) in a list of outputs
-- return Nothing if they can't be combined, else return type of the combined thunk
class CombineThunks a where
  combineThunks :: a -> a -> Maybe a

combineHead :: (CombineThunks a, AType a) => [(Src, a)] -> Checking (Maybe ((Src, a), [(Src, a)]))
combineHead ((s,f):(s',g):hs) = case combineThunks f g of
  Just fg -> do
    node <- anext (show s ++ "_" ++ show s') (Combo Thunk) [("in1", f), ("in2", g)] [("fun", fg)]
    awire (s, f, (node, ("in1")))
    awire (s', g, (node, ("in2")))
    pure $ Just (((node, "fun"), fg), hs)
  Nothing -> pure Nothing
combineHead _ = pure Nothing

-- Apply `combineHead` until it yields nothing and obtain list of the results
-- just like `iterate` from the prelude. Include original argument in results
combinationsWithLeftovers :: (CombineThunks a, AType a) => NonEmpty (Src, a) -> Checking (NonEmpty ((Src, a), [(Src, a)]))
combinationsWithLeftovers (f :| xs) =
  combineHead (f:xs) >>= \case
    Nothing -> pure ((f, xs) :| [])
    Just (fg, ys) -> ((f, xs) <|) <$> combinationsWithLeftovers (fg :| ys)

-- instance for `Outputs Brat Syn`
instance CombineThunks VType where
  combineThunks (C cty) (C cty') = Just $ C (cty <> cty')

  combineThunks (K (R ss) (R ts)) (K (R us) (R vs)) = Just $ K (R (ss <> us)) (R (ts <> vs))

  combineThunks _ _ = Nothing

-- instance for `Outputs Kernel Syn`
instance CombineThunks SType where
  combineThunks (Rho (R r)) (Rho (R r')) = Just $ Rho (R (r <> r'))

  combineThunks _ _ = Nothing

-- instance for `forall k. Outputs k Chk`
instance CombineThunks () where
  combineThunks _ _ = Nothing
