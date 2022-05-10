{-# LANGUAGE PatternSynonyms #-}

module Brat.Checker.Combine where

import Brat.Checker.Monad (Checking, next, knext)
import Brat.Graph (Src, Thing(..))
import Brat.Syntax.Common (pattern R, pattern Rho, VType'(..))
import Brat.Syntax.Core (VType, SType)

import Data.List.NonEmpty (NonEmpty(..), (<|))

-- Combine two thunks (either classical or kernel) in a list of outputs
-- return Nothing if nothing changes, else return the new thunk
class CombineThunks a where
  combineThunks :: a -> a -> Checking (Maybe a)

combineHead :: CombineThunks a => [a] -> Checking (Maybe (a, [a]))
combineHead (f:g:hs) = combineThunks f g >>= \case
  Just fg -> pure (Just (fg, hs))
  Nothing -> pure Nothing
combineHead _ = pure Nothing

-- Apply `combineHead` until it yields nothing and obtain list of the results
-- just like `iterate` from the prelude. Include original argument in results
combinationsWithLeftovers :: CombineThunks a => NonEmpty a -> Checking (NonEmpty (a, [a]))
combinationsWithLeftovers (f :| xs) =
  combineHead (f:xs) >>= \case
    Nothing -> pure ((f, xs) :| [])
    Just (fg, ys) -> ((f, xs) <|) <$> combinationsWithLeftovers (fg :| ys)

-- instance for `Outputs Brat Syn`
instance CombineThunks (Src, VType) where
  combineThunks (src, C cty) (src', C cty') = do
    let newTy = C (cty <> cty')
    node <- next (show src ++ "_" ++ show src') (Combo src src') [] [("fun", newTy)]
    pure $ Just ((node, "fun"), newTy)

  combineThunks (src, K (R ss) (R ts)) (src', K (R us) (R vs)) = do
    let newTy = K (R (ss <> us)) (R (ts <> vs))
    node <- next (show src ++ "_" ++ show src') (Combo src src') [] [("fun", newTy)]
    pure $ Just ((node, "fun"), newTy)

  combineThunks _ _ = pure Nothing

-- instance for `Outputs Kernel Syn`
instance CombineThunks (Src, SType) where
  combineThunks (src, (Rho (R r))) (src', (Rho (R r'))) = do
    let newTy = Rho (R (r <> r'))
    node <- knext (show src ++ "_" ++ show src') (Combo src src') [] [("fun", newTy)]
    pure $ Just ((node, "fun"), newTy)

  combineThunks _ _ = pure Nothing

-- instance for `forall k. Outputs k Chk`
instance CombineThunks () where
  combineThunks _ _ = pure Nothing
