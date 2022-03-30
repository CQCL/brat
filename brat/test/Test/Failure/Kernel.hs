{-# LANGUAGE OverloadedStrings #-}

module Test.Failure.Kernel (getKernelTests) where

import Test.Tasty
import Test.Tasty.Silver
import System.FilePath

goldenTest file = goldenVsProg (takeBaseName file) (file <.> "golden") "brat" [file] ""

getKernelTests :: IO TestTree
getKernelTests = testGroup "kernel" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/kernel"
