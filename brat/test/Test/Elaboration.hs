module Test.Elaboration (elaborationTests) where

import Brat.Elaborator
import Brat.Error (showError)
import Brat.UserName (plain)
import Brat.Syntax.Concrete
import Brat.Syntax.Common
import Brat.Syntax.Raw (kind, dir)
import Brat.Syntax.Simple (SimpleTerm(..))
import Brat.FC

import Data.Functor ((<&>))
import qualified Data.PartialOrd as PO
import qualified Data.Set as S
import Test.Tasty
import Test.Tasty.HUnit

data DirAndKind = DK Dir Kind deriving (Show, Eq)

data FlatTest = FT DirAndKind Flat

chkUVerb :: Flat
chkUVerb = FLambda (dummyFC $ APat (Bind "x")) (dummyFC $ FSimple $ Num 5)
flats :: [FlatTest]
flats = [FT (DK Syn Noun) $ FVar $ plain "x"
        ,FT (DK Syn UVerb) $
            FLambda (dummyFC $ APat (Bind "x")) (dummyFC $ FVar $ plain "x")
        ,FT (DK Syn KVerb) $
            FCompose (dummyFC $ FVar $ plain "f") (dummyFC $ FVar $ plain "g")
        ,FT (DK Chk Noun) $ FSimple (Num 5)
        ,FT (DK Chk UVerb) chkUVerb
        ,FT (DK Chk KVerb) $
            FCompose (dummyFC $ FVar $ plain "f") (dummyFC chkUVerb)
        ]

ydir :: Diry d -> Dir
ydir Syny = Syn
ydir Chky = Chk

ykind :: Kindy k -> Kind
ykind Nouny = Noun
ykind KVerby = KVerb
ykind UVerby = UVerb

elabTest :: String -> DirAndKind -> Flat -> Assertion
elabTest s dk f = case elaborate (dummyFC f) of
  Left err -> assertFailure (showError err)
  Right (SomeRaw (WC _ r)) -> let actual = DK (ydir $ dir r) (ykind $ kind r)
    in if actual == dk then pure ()
       else assertFailure $ s ++ " should have been " ++ show dk
                  ++ " but got " ++ show actual ++ " from: " ++ show r

elabFails :: String -> Flat -> Assertion
elabFails s f | Right (SomeRaw (WC _ r)) <- elaborate (dummyFC f) =
  assertFailure $ s ++ " should have failed elaboration, but produced " ++ show r
elabFails _ _ = pure ()

instance PO.PartialOrd DirAndKind where
  (DK Syn Noun) <= _ = True -- Force (+Emb/Forget)
  (DK Chk _) <= (DK Syn _) = False -- any other Dirs possible w/ Emb
  (DK _ KVerb) <= (DK _ UVerb) = True -- Forget
  (DK _ k1) <= (DK _ k2) = k1 == k2

allDKs = [Noun, KVerb, UVerb] >>= \k -> [DK Syn k, DK Chk k]

juxt_tests :: FlatTest -> TestTree
juxt_tests (FT dk1 f1) = let s1 = show dk1 in testCase ("juxt w/" ++ s1) $ sequence_ $ flats <&>
  \(FT dk2 f2) -> let
      s = s1 ++ "-" ++ (show dk2)
      f = (FJuxt (dummyFC f1) (dummyFC f2))
      dks = [dk | dk <- allDKs, dk1 PO.<= dk, dk2 PO.<= dk]
    in case PO.minima dks of
      [] -> elabFails s f
      [dk] -> elabTest s dk f

elaborationTests :: TestTree
elaborationTests = testGroup "elaboration" (
    [testCase "base cases" $ sequence_ (map (\(FT dk f) -> elabTest (show dk) dk f) flats)]
    ++ (map juxt_tests flats)
  )
