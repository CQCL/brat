import Test.Tasty
import Test.Tasty.HUnit

import Test.Circuit.Gen
import Test.Circuit.Graph

main = defaultMain $ testGroup "All" [graphTests
                                     -- ,circuitTests
                                     ]
