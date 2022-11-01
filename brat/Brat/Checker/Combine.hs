{-# LANGUAGE PatternSynonyms #-}

module Brat.Checker.Combine where

import Brat.Checker.Helpers (next, wire)
import Brat.Checker.Monad (Checking)
import Brat.Graph (Thing(..), ComboType(..))
import Brat.Syntax.Common (pattern R, VType'(..), Src)
import Brat.Syntax.Core (VType)

import Data.List.NonEmpty (NonEmpty(..), (<|))

-- Combine types of two thunks (either classical or kernel) in a list of outputs
-- return Nothing if they can't be combined, else return type of the combined thunk
combineThunks :: VType -> VType -> Maybe VType
combineThunks (C cty) (C cty') = Just $ C (cty <> cty')
combineThunks (K (R ss) (R ts)) (K (R us) (R vs)) = Just $ K (R (ss <> us)) (R (ts <> vs))
combineThunks _ _ = Nothing

combineHead :: [(Src, VType)] -> Checking (Maybe ((Src, VType), [(Src, VType)]))
combineHead (((s,_),f):((s',_),g):hs) = case combineThunks f g of
  Just fg -> do
    (_, [in1, in2], [fun]) <- next (show s ++ "_" ++ show s') (Combo Thunk)
                             [("in1", f), ("in2", g)] [("fun", fg)]
    wire (s, f, fst (fst in1))
    wire (s', g, fst (fst in2))
    pure $ Just (fun, hs)
  Nothing -> pure Nothing
combineHead _ = pure Nothing

-- Apply `combineHead` until it yields nothing and obtain list of the results
-- just like `iterate` from the prelude. Include original argument in results
combinationsWithLeftovers :: NonEmpty (Src, VType) -> Checking (NonEmpty ((Src, VType), [(Src, VType)]))
combinationsWithLeftovers (f :| xs) =
  combineHead (f:xs) >>= \case
    Nothing -> pure ((f, xs) :| [])
    Just (fg, ys) -> ((f, xs) <|) <$> combinationsWithLeftovers (fg :| ys)
