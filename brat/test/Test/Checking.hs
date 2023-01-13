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

expectedCheckingFails = map ("examples" </>) ["nested-abstractors.brat"
                        ,"karlheinz_alias.brat" -- ALAN should probably fix this
                        -- The next two are regressions in dependent types,
                        -- expected to be fixed by upcoming work on pattern refinement
                        ,"vector.brat"
                        ,"kinds.brat"
                        ]

parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF = expectFailForPaths (expectedParsingFails ++ expectedCheckingFails) parseAndCheck

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"

runEmpty :: Checking v -> Either Error (v,([TypedHole],Graph))
runEmpty m = run emptyEnv root m
