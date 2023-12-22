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
import Test.Parsing (expectFailForPaths)

goldenTest file = goldenVsAction (takeBaseName file) (file <.> "golden") (runGetStderr file $ compileFile [] file) pack

getKernelTests :: IO TestTree
getKernelTests = testGroup "kernel" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/kernel"

getCycleTests :: IO TestTree
getCycleTests = testGroup "cycle" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/cycle"

getImportTests :: IO TestTree
getImportTests = testGroup "imports"
                 . fmap goldenTest
                 . filter ((`notElem` ignored) . takeBaseName)
                 <$> findByExtension [".brat"] "test/golden/imports"
 where ignored = ["lib"]

getBindingTests :: IO TestTree
getBindingTests = testGroup "binding" . fmap goldenTest <$> findByExtension [".brat"] "test/golden/binding"

getErrorTests :: IO TestTree
getErrorTests = testGroup "error" . fmap (expectFailForPaths ["test/golden/error/unreachablebranch.brat"] goldenTest) <$> findByExtension [".brat"] "test/golden/error"

runGetStderr :: String -> IO () -> IO String
runGetStderr name action = do
    (output, ()) <- hCapture [stderr] $
      action `catch` \(ExitFailure c) -> return ()
    return output


getFailureTests = do
  bindingTests <- getBindingTests
  cycleTests   <- getCycleTests
  importTests  <- getImportTests
  kernelTests  <- getKernelTests
  errTests     <- getErrorTests
  pure $ testGroup "Failure" [bindingTests, cycleTests, importTests, kernelTests, errTests]
