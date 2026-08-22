module Test.Examples (getExamplesTests) where

import Test.Checking (parseAndCheckNamed)
import Test.Compile.Hugr (compileToOutput, ValidationTest(..))
import Brat.Load (parseFile)
import Brat.Machine (runInterpreter)

import Data.Char (isAlphaNum)
import Data.List (isPrefixOf)
import Data.Maybe (fromJust)
import qualified Data.Text.Lazy as T
import System.Exit (ExitCode(..))
import System.FilePath
import System.Process (readCreateProcessWithExitCode, shell)
import Test.Tasty
import Test.Tasty.Providers
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

--import Debug.Trace

outputDir :: FilePath
outputDir = "test" </> "examples"

execTestPrefix :: T.Text
execTestPrefix = T.pack "--!exec"

interpreterOutputPrefix :: String
interpreterOutputPrefix = "Finished "

getExamplesTests :: IO TestTree
getExamplesTests =  do
  validatorAvailable <- checkValidatorInPath
  paths <- findByExtension [".brat"] "examples"
  testGroup "examples" <$> mapM (mkTest validatorAvailable) paths
 where
  mkTest :: Bool -> FilePath -> IO TestTree
  mkTest interpreterInPath path = readFile path >>= \cts ->
    let parseTest = testCase "parsing" $ do
          case parseFile path cts of
            Left err -> assertFailure (show err)
            Right _ -> return () -- OK
        checkTest = parseAndCheckNamed "checking" [] path
    in if isPrefixOf "--!xfail-parsing" cts then
         pure $ testGroup (show path) [expectFail parseTest]
       else if isPrefixOf "--!xfail-checking" cts then
         pure $ testGroup (show path) [parseTest, expectFail checkTest]
       else do
        let execStrings = snd <$> T.breakOnAll execTestPrefix (T.pack cts)
            interpreterTests = concat $ interpreterTestsForExample interpreterInPath path <$> execStrings
        compileTest <- compileToOutput "compilation" path
        let checkAndCompile = if isPrefixOf "--!xfail-compilation" cts
              then [checkTest, expectFail compileTest] else [compileTest]
        pure $ case interpreterTests of
          [] -> testGroup (show path) checkAndCompile
          intTests -> sequentialTestGroup path AllSucceed
              (checkAndCompile ++ [testGroup "execution" intTests])


interpreterTestsForExample :: Bool -> FilePath -> T.Text -> [TestTree]
interpreterTestsForExample interpreterInPath path start =
  let (testLine, newlineDefn) = T.breakOn (T.pack "\n") start
      -- this repeats/roughly duplicates the logic for "identifiers" in the parser
      func_name = T.unpack $ T.takeWhile (\c -> isAlphaNum c || c == '_' || c == '\'') (T.drop 1 newlineDefn)
      -- testLine begins with execTestPrefix, then either
      -- " " and the expected result
      -- "-xfail " and the (un-)expected result
      -- "-hugr\n" (checks no splices, outputs hugr for validation)
      restLine = fromJust $ T.stripPrefix execTestPrefix testLine
  in if (T.pack "-hugr") == restLine
     then let outFile = outputDir </> dropExtension (takeFileName path) ++ "_" ++ func_name <.> "json"
              makeHugr = do
                -- this completely recompiles the file for each test, which is pretty bad
                hugr <- runInterpreter [] path func_name >>= \case
                  Left s -> assertFailure $ "Expected hugr, got " ++ T.unpack s
                  Right hugr -> pure hugr
                pure (hugr, []) --Expect no hole ops as spliced by interpreter
          in [singleTest func_name (VTest makeHugr outFile)]
     else let (is_xfail, eOut) = case T.stripPrefix (T.pack "-xfail ") restLine of
                Just out -> (True, out)
                Nothing | Just out <- T.stripPrefix (T.pack " ") restLine -> (False, out)
                        | otherwise -> error $ "Invalid exec test line: " ++ T.unpack testLine
              expectedOutput = interpreterOutputPrefix ++ T.unpack (T.strip eOut)
          in (:[]) . (if is_xfail then expectFail else id) . testCase func_name $ do
            -- this completely recompiles the file for each test, which is pretty bad
            runInterpreter [] path func_name >>= \case
              Left t -> T.unpack t @?= expectedOutput
              Right _ -> assertFailure $ "Expected output: '" ++ expectedOutput ++ "' but got a hugr!"

checkValidatorInPath :: IO Bool
checkValidatorInPath = do
  (exitCode, output, _) <- readCreateProcessWithExitCode (shell "hugr_validator --version") ""
  pure (exitCode == ExitSuccess && "hugr_validator 0." `isPrefixOf` output)

validateTest :: FilePath -> Assertion
validateTest file = do
  (exitCode, stdout, stderr) <- readCreateProcessWithExitCode (shell $ "cat " ++ file ++ " | hugr_validator") "" -- TODO: Put hugr output there
  case exitCode of
    ExitSuccess -> pure () --  "Validated hugr" -- TODO: Can we give a msg?
    _ -> assertFailure stderr
