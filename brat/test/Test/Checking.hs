module Test.Checking (getCheckingTests, runEmpty) where

import Brat.Checker (run, emptyEnv, Checking, TypedHole)
import Brat.Error (Error)
import Brat.Graph (Graph)
import Brat.Naming (root)
import Test.Parsing (expectedParsingFails, expectFailForPaths)
import Test.Util (parseAndCheck)

import System.FilePath
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Silver
import Test.Tasty.ExpectedFailure

expectedCheckingFails = map ("examples" </>) ["nested-abstractors.brat"
                                             ,"karlheinz_alias.brat"
                                             -- The next is a regression in dependent types,
                                             -- expected to be fixed by upcoming work on pattern refinement
                                             ,"kinds.brat"
                                             ]

parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF = expectFailForPaths (expectedParsingFails ++ expectedCheckingFails) (parseAndCheck [])

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"

runEmpty :: Checking v -> Either Error (v,([TypedHole],Graph))
runEmpty m = run emptyEnv root m
