module Test.Checking (getCheckingTests, expectedCheckingFails) where

import Test.Parsing (expectedParsingFails, expectFailForPaths)
import Test.Util (parseAndCheck)

import System.FilePath
import Test.Tasty
import Test.Tasty.Silver

expectedCheckingFails = map ("examples" </>) ["nested-abstractors.brat"
                                             ,"karlheinz_alias.brat"
                                             ,"hea.brat"
                                             ]

parseAndCheckXF :: FilePath -> TestTree
parseAndCheckXF = expectFailForPaths (expectedParsingFails ++ expectedCheckingFails) (parseAndCheck [])

getCheckingTests :: IO TestTree
getCheckingTests = testGroup "checking" . fmap parseAndCheckXF <$> findByExtension [".brat"] "examples"
