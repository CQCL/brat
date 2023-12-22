import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Abstractor
import Test.Checking
import Test.Circuit.Graph
import Test.Compile.RemoveNode
import Test.Constructors
import Test.Elaboration
import Test.Equality
import Test.Failure
import Test.Libs
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
                                ,libDirTests
                                ,nameTests
                                ,parsingTests
                                ,searchTests
                                ,constructorTests
                                ,removeNodeTests
                                ,elaborationTests
                                ,substitutionTests
                                ,abstractorTests
                                ,eqTests
                                ]
