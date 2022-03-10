{-# LANGUAGE OverloadedStrings #-}

module Test.Import.Cycle (getCycleTests) where

import Test.Tasty
import Test.Tasty.Silver
import System.FilePath

goldenTest file = goldenVsProg (takeBaseName file) (file <.> "golden") "brat" [file] ""

getCycleTests :: IO TestTree
getCycleTests = testGroup "cycle" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/cycle"
