{-# LANGUAGE OverloadedStrings #-}

module Test.Failure.Binding (getBindingTests) where

import Test.Tasty
import Test.Tasty.Silver
import System.FilePath

goldenTest file = goldenVsProg (takeBaseName file) (file <.> "golden") "brat" [file] ""

getBindingTests :: IO TestTree
getBindingTests = testGroup "binding" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/binding"
