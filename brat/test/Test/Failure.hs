module Test.Failure (getFailureTests) where

import Test.Tasty
import Test.Tasty.Silver
import System.Exit (ExitCode(..))
import Control.Monad (unless)
import Control.Exception
import System.FilePath
import System.IO
import System.IO.Silently
import Data.Text (pack)

import Brat.Compiler

goldenTest file = goldenVsAction (takeBaseName file) (file <.> "golden") (runGetStderr file $ compileFile file) pack

getKernelTests :: IO TestTree
getKernelTests = testGroup "kernel" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/kernel"

getCycleTests :: IO TestTree
getCycleTests = testGroup "cycle" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/cycle"

getBindingTests :: IO TestTree
getBindingTests = testGroup "binding" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/binding"

getTypeErrorTests :: IO TestTree
getTypeErrorTests = testGroup "type_error" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/type_error"

runGetStderr :: String -> IO () -> IO String
runGetStderr name action = do
    (output, ()) <- hCapture [stderr] $
      action `catch` \(ExitFailure c) -> return ()
    return output


getFailureTests = do
  bindingTests <- getBindingTests
  cycleTests <- getCycleTests
  kernelTests <- getKernelTests
  typeErrTests <- getTypeErrorTests
  pure $ testGroup "Failure" [bindingTests, cycleTests, kernelTests, typeErrTests]
