import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Abstractor
import Test.Checking
import Test.Circuit.Graph
import Test.Compile.Hugr
import Test.Constructors
import Test.Elaboration
import Test.Failure
import Test.Libs
import Test.Naming
import Test.Parsing
import Test.Search
import Test.Substitution
import Test.Syntax.Let
import Test.TypeArith

main = do
  failureTests  <- getFailureTests
  checkingTests <- getCheckingTests
  parsingTests <- getParsingTests
  compilationTests <- setupCompilationTests
  defaultMain $ testGroup "All" [graphTests
                                ,failureTests
                                ,checkingTests
                                ,letTests
                                ,libDirTests
                                ,nameTests
                                ,parsingTests
                                ,searchTests
                                ,constructorTests
                                ,elaborationTests
                                ,substitutionTests
                                ,abstractorTests
                                ,compilationTests
                                ,typeArithTests
                                ]
