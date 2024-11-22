module Test.Abstractor where

import Data.Functor

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Brat.Syntax.Abstractor
import Brat.Syntax.Simple
import Util

abstractor :: Int -> Gen Abstractor
abstractor 0 = pure AEmpty
abstractor n = oneof
  [pure AEmpty
  ,APat <$> resize (n - 1) arbitrary
  ,APull <$> listOf portname <*> abstractor (max 0 (n - 1))
  ,chooseInt (0,n) >>= \m -> (:||:) <$> abstractor m <*> abstractor (n - m)
  ]
 where
  portname = arbitrary <&> \n -> names !! abs n

instance Arbitrary Abstractor where
  arbitrary = sized abstractor

instance Arbitrary SimpleTerm where
  arbitrary = oneof [Num <$> arbitrary
                    ,Text <$> arbitrary
                    ,Float <$> arbitrary
                    ,pure Unit
                    ]

instance Arbitrary Pattern where
  arbitrary = sized pat
   where
    pat 0 = oneof [Bind <$> arbitrary
                  ,Lit <$> arbitrary
                  ,pure DontCare
                  ]
    pat n = oneof [Bind <$> arbitrary
                  ,Lit <$> arbitrary
                  ,pure DontCare
                  ,con (n - 1)
                  ]

    con 0 = oneof [pure PNone
                  ,pure PNil
                  ]
    con n = oneof [pure PNone
                  ,pure PNil
                  ,PSome <$> pat (n - 1)
                  ,POnePlus <$> pat (n - 1)
                  ,PTwoTimes <$> pat (n - 1)
                  ,PCons <$> pat (n `div` 2) <*> pat (n `div` 2)
                  ]

idempotency :: Abstractor -> Bool
idempotency abs = let NA abs' = normaliseAbstractor abs
                      NA abs'' = normaliseAbstractor abs'
                  in abs' == abs''

monoidalUnitCancelled :: Abstractor -> Bool
monoidalUnitCancelled abs = let NA abs' = normaliseAbstractor abs in aux abs'
 where
  -- The empty abstractor is allowed only if it's the _whole_ abstractor
  aux AEmpty = True
  aux (a :||: b)
    | AEmpty <- a = False
    | AEmpty <- b = False
    | otherwise = aux a && aux a
  aux (APat p)
    | PCon _ abs <- p = aux abs
    | otherwise = True
  aux (APull _ abs) = aux abs

leftToRight = let NA act = normaliseAbstractor left in
                right @?= act
  where
    left = ((APat (Bind "a") :||: APat (Bind "b")) :||: APat (Bind "c")) :||: APat (Bind "d")
    right = APat (Bind "a") :||: (APat (Bind "b") :||: (APat (Bind "c") :||: APat (Bind "d")))

abstractorTests = testGroup "Abstractor" [testProperty "Idempotency" idempotency
                                         ,testProperty "Unit" monoidalUnitCancelled
                                         ,testCase "LeftToRight" leftToRight
                                         ]
