module Test.Failure where

import Test.Tasty

import Test.Failure.Import.Cycle
import Test.Failure.Kernel

getFailureTests = do
  cycleTests <- getCycleTests
  kernelTests <- getKernelTests
  pure $ testGroup "Failure" [cycleTests, kernelTests]
