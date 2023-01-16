module Brat.Syntax.Concrete where

import Data.List.NonEmpty

import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Raw
import Brat.Syntax.Simple
import Brat.UserName

type FlatCType = CType' (RawIO' (WC (KindOr Flat)))
type FlatKType = CType' (RawIO' (SType' (WC Flat)))

data FBody
  = FClauses (NonEmpty (WC Abstractor, WC Flat))
  | FNoLhs (WC Flat)
  | FUndefined
 deriving Show

type FDecl = Decl' RawIO FBody
deriving instance Show FDecl
type FEnv = ([FDecl], [RawAlias])


data Flat
 = FVar UserName
 | FApp (WC Flat) (WC Flat)
 | FJuxt (WC Flat) (WC Flat)
 | FThunk (WC Flat)
 | FCompose (WC Flat) (WC Flat)
-- Keep |> distinct from application to keep track of user's syntax choice.
-- Note that it's turned into an application during elaboration
 | FInto (WC Flat) (WC Flat)
 | FLambda (WC Abstractor) (WC Flat)
 | FAnnotation (WC Flat) [RawIO]
 | FLetIn (WC Abstractor) (WC Flat) (WC Flat)
 | FSimple SimpleTerm
 | FHole String
 | FCon UserName (WC Flat)
 | FEmpty
 | FPull [PortName] (WC Flat)
 -- We can get away with not elaborating type signatures in the short term
 | FFn RawCType
 | FKernel RawKType
 | FUnderscore
 deriving Show