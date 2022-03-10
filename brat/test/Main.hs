import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Circuit.Gen
import Test.Circuit.Graph
import Test.Import.Cycle

main = do
  cycleTests <- getCycleTests
  defaultMain $ testGroup "All" [graphTests
                                ,cycleTests
                                 -- ,circuitTests
                                ]
