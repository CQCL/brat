module Test.Checking (getCheckingTests, runEmpty) where

import Brat.Checker (run, emptyEnv, Checking, TypedHole)
import Brat.Error (Error)
import Brat.FC
import Brat.Graph (Graph)
import Brat.Load
import Brat.Naming (root)
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

runEmpty :: Checking v -> Either Error (v,([TypedHole],Graph))
runEmpty m = (\(a,b,_) -> (a,b)) <$> run (emptyEnv, [], FC (Pos 0 0) (Pos 0 0)) root m