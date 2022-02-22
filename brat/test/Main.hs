import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Checking
import Test.Circuit.Gen
import Test.Circuit.Graph
import Test.Import.Cycle
import Test.Syntax.Let

main = do
  cycleTests <- getCycleTests
  checkingTests <- getCheckingTests
  defaultMain $ testGroup "All" [graphTests
                                ,cycleTests
                                ,checkingTests
                                ,letTests
                                 -- ,circuitTests
                                ]
