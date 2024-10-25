module Test.Compile.Hugr where

import Brat.Checker (run)
import Brat.Checker.Monad (Checking)
import Brat.Checker.Types (TypedHole)
import Brat.Compiler (compileFile, CompilingHoles(..))
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

-- examples that we expect not to compile.
-- Note this does not include those with remaining holes; these are automatically skipped.
-- ()
nonCompilingExamples = (expectedCheckingFails ++ expectedParsingFails ++
  map ((++ ".brat") . ("examples" </>))
  ["fzbz"
  ,"ising"
  ,"let"
  ,"patterns"
  ,"qft"
  ,"test"
  ,"fanout" -- Contains Selectors
  -- Conjecture: These examples don't compile because number patterns in type
  -- signatures causes `kindCheck` to call `abstract`, creating "Selector"
  -- nodes, which we don't attempt to compile because we want to get rid of them
  ,"vec-pats"
  -- Victims of #13
  ,"arith"
  ,"cqcconf"
  ,"imports"
  ,"ising"
  ,"klet"
  ,"magic-state-distillation" -- also makes selectors
  ,"rus"
  ,"teleportation"
  ,"vlup_covering"
  ])

compileToOutput :: FilePath -> TestTree
compileToOutput file = testCase (show file) $ compileFile [] file >>= \case
    Right bs -> do
      -- for non-compiling examples we end up writing out an empty file so that's invalid too
      let isValid = not (file `elem` nonCompilingExamples || file `elem` invalidExamples)
      let outputExt = if isValid  then "json" else "json.invalid"
      let outFile = outputDir </> replaceExtension (takeFileName file) outputExt
      BS.writeFile outFile bs
    Left (CompilingHoles _) -> pure () -- pass, don't write out anything

setupCompilationTests :: IO TestTree
setupCompilationTests = do
  tests <- findByExtension [".brat"] prefix
  examples <- findByExtension [".brat"] examplesPrefix
  createDirectoryIfMissing False outputDir
  let compileTests = compileToOutput <$> tests
  let examplesTests = testGroup "examples" $ expectFailForPaths nonCompilingExamples compileToOutput <$> examples

  pure $ testGroup "compilation" (examplesTests:compileTests)
