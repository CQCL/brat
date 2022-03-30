module Test.Failure where

import Test.Tasty

import Test.Failure.Binding
import Test.Failure.Import.Cycle
import Test.Failure.Kernel

getFailureTests = do
  bindingTests <- getBindingTests
  cycleTests   <- getCycleTests
  kernelTests  <- getKernelTests
  pure $ testGroup "Failure" [bindingTests, cycleTests, kernelTests]
