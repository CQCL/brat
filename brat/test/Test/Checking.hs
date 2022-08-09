module Test.Checking (getCheckingTests) where

import Brat.Load
import Test.Parsing (expectedParsingFails, expectFailForPaths)

import Control.Monad.Except
import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

parseAndCheck :: FilePath -> TestTree
parseAndCheck file = testCase (show file) $ do
  env <- runExceptT $ loadFilename file
  case env of
    Left err -> assertFailure (show err)
    Right (venv, nouns, holes, _) ->
      ((length venv) + (length nouns) + (length holes) > 0) @? "Should produce something"

expectedCheckingFails = ["examples/nested-abstractors.brat"]

parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF = expectFailForPaths (expectedParsingFails ++ expectedCheckingFails) parseAndCheck

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"
