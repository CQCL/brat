import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Checking
import Test.Circuit.Gen
import Test.Circuit.Graph
import Test.Combine
import Test.Compile.RemoveNode
import Test.Constructors
import Test.Failure
import Test.Naming
import Test.Parsing
import Test.Search
import Test.Syntax.Let

main = do
  failureTests  <- getFailureTests
  checkingTests <- getCheckingTests
  parsingTests <- getParsingTests
  defaultMain $ testGroup "All" [graphTests
                                ,failureTests
                                ,checkingTests
                                ,letTests
                                 -- ,circuitTests
                                ,nameTests
                                ,parsingTests
                                ,searchTests
                                ,combineTests
                                ,constructorTests
                                ,removeNodeTests
                                ]
