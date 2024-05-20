module Test.Compile.Hugr where

import Brat.Checker (run, emptyEnv, Checking, TypedHole)
import Brat.Compiler (compileFile)
import Brat.Error (Error)
import Brat.Graph (Graph)
import Brat.Naming (root)
import Test.Parsing (expectedParsingFails, expectFailForPaths)
import Test.Util (parseAndCheck)

import qualified Data.ByteString.Lazy as BS
import Data.Traversable (for)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

prefix = "test/compilation"
outputDir = prefix </> "output"

expectedFails = map (prefix </>) []

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCase (show file) $ do
  let outFile = outputDir </> replaceExtension (takeFileName file) "json"
  bs <- compileFile [] file
  BS.writeFile outFile bs

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  createDirectoryIfMissing False outputDir
  pure $ testGroup "compilation" (expectFailForPaths expectedFails compileToOutput <$> tests)
