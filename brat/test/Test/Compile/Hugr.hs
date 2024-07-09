module Test.Compile.Hugr where

import Brat.Checker (run)
import Brat.Checker.Monad (Checking)
import Brat.Checker.Types (TypedHole)
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
invalidExamples = map ((++ ".brat") . ("examples" </>))
  ["adder"
  ,"app"
  ,"dollar_kind"
  ,"portpulling"
  ,"repeated_app" -- missing coercions, https://github.com/CQCL-DEV/brat/issues/413
  ,"thunks"]

-- examples that we expect not to compile
-- Note this includes those with remaining holes; it would be better
-- to detect those automatically (as this is not a bug, they *shouldn't* compile)
nonCompilingExamples = (expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>))
  ["fzbz"
  ,"full"
  ,"graph"
  ,"holes"
  ,"ising"
  ,"kernel"
  ,"kernel-syntax"
  ,"kinds"
  ,"let"
  ,"list"
  ,"listpair"
  ,"one"
  ,"patterns"
  ,"qft"
  ,"test"
  ,"vector"
  -- Conjecture: These examples don't compile because number patterns in type
  -- signatures causes `kindCheck` to call `abstract`, creating "Selector"
  -- nodes, which we don't attempt to compile because we want to get rid of them
  ,"vec-pats"
  -- Victims of #389
  ,"arith"
  ,"bell"
  ,"cqcconf"
  ,"imports"
  ,"ising"
  ,"klet"
  ,"rus"
  ,"teleportation"
  ,"vlup_covering"
  ])

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCase (show file) $ do
  -- for non-compiling examples we end up writing out an empty file so that's invalid too
  let isValid = not (file `elem` nonCompilingExamples || file `elem` invalidExamples)
  let outputExt = if isValid  then "json" else "json.invalid"
  let outFile = outputDir </> replaceExtension (takeFileName file) outputExt
  compileFile [] file >>= \case
    Right bs -> BS.writeFile outFile bs
    Left err -> assertFailure err

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = compileToOutput <$> tests
  let examplesTests = testGroup "examples" $ expectFailForPaths nonCompilingExamples compileToOutput <$> examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
