module Brat.Syntax.Concrete where

import Data.List.NonEmpty

import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Raw
import Brat.Syntax.Simple
import Brat.UserName


data FClause
  = FClauses (NonEmpty (WC Abstractor, WC Flat))
  | FNoLhs (WC Flat)
  | FUndefined

type FDecl = Decl' RawIO FClause
type FEnv = ([FDecl], [(UserName, TypeAlias)])


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
 | FUnderscore
 deriving Show
