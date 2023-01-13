import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Checking
import Test.Circuit.Gen
import Test.Circuit.Graph
import Test.Compile.RemoveNode
import Test.Constructors
import Test.Elaboration
import Test.Failure
import Test.Naming
import Test.Parsing
import Test.Search
import Test.Substitution
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
                                ,constructorTests
                                ,removeNodeTests
                                ,elaborationTests
                                ,substitutionTests
                                ]
