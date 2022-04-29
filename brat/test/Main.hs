import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Checking
import Test.Circuit.Gen
import Test.Circuit.Graph
import Test.Failure
import Test.Naming
import Test.Search
import Test.Syntax.Let

main = do
  failureTests  <- getFailureTests
  checkingTests <- getCheckingTests
  defaultMain $ testGroup "All" [graphTests
                                ,failureTests
                                ,checkingTests
                                ,letTests
                                 -- ,circuitTests
                                ,nameTests
                                ,searchTests
                                ]
