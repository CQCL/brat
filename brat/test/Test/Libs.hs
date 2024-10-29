module Test.Libs where

import Test.Checking (parseAndCheck)

import Test.Tasty

libDirTests :: TestTree
libDirTests = testGroup "libDir"
  [parseAndCheck libs1 "test/should_pass/inner/test.brat"
  ,parseAndCheck libs2 "test/should_pass/inner/deeper/test.brat"
  ]
 where
  libs1 = ["test/should_pass"]
  libs2 = ["test/should_pass","test/should_pass/inner"]
