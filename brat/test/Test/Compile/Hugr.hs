module Test.Compile.Hugr where

import Brat.Checker (run, emptyEnv, Checking, TypedHole)
import Brat.Compiler (compileFile)
import Brat.Error (Error)
import Brat.Graph (Graph)
import Brat.Naming (root)
import Test.Checking (expectedCheckingFails)
import Test.Parsing (expectedParsingFails, expectFailForPaths)
import Test.Util (parseAndCheck)

import qualified Data.ByteString.Lazy as BS
import Data.List (partition)
import Data.Traversable (for)
import System.Directory (createDirectoryIfMissing)
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

prefix = "test/compilation"
examplesPrefix = "examples"
outputDir = prefix </> "output"

-- examples that we expect to compile, but then to fail validation
invalidExamples :: [FilePath]
invalidExamples = map ((++ ".brat") . ("examples" </>)) ["vector", "pass", "thunks"]

-- examples that we expect not to compile
-- Note this includes those with remaining holes; it would be better
-- to detect those automatically (as this is not a bug, they *shouldn't* compile)
noncompilingExamples = (expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>)) [
  "alias", "app", "arith", "bell", "composition", "cons", "cqcconf",
  "dollar_kind", "first", "fzbz", "graph", "holes", "imports", "into",
  "kernel", "kernel-syntax", "kinds", "klet",
  "let", "lib/kernel", "list", "listpair", "one",
  "patterns", "portpulling", "qft", "repeated_app", "second",
  "test", "tups", "teleportation", "unified", "vec_check", "vector", "vlup_covering"])

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCase (show file) $ do
  -- for non-compiling examples we end up writing out an empty file so that's invalid too
  let isValid = not (file `elem` noncompilingExamples || file `elem` invalidExamples)
  let outputExt = if isValid  then "json" else "json.invalid"
  let outFile = outputDir </> replaceExtension (takeFileName file) outputExt
  bs <- compileFile [] file
  BS.writeFile outFile bs

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = compileToOutput <$> tests
  let examplesTests = testGroup "examples" $ expectFailForPaths noncompilingExamples compileToOutput <$> examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
