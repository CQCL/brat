{-# LANGUAGE FlexibleContexts #-}

module Brat.Checker.Clauses where

import Brat.Checker
import Brat.Checker.Monad (err)
import Brat.Error
import Brat.FC
import qualified Brat.FC as FC
import Brat.Syntax.Common
import Brat.Syntax.Core (Term(..))
import Brat.Syntax.Value (BinderType, Value(..))
import Bwd

import Data.Functor (($>))
import Data.Traversable (for)

checkBody :: (?my :: Modey m, CheckConstraints m UVerb)
          => String
          -> FunBody Term UVerb
          -> (Bwd Value, [(PortName, BinderType m)], [(PortName, BinderType m)])
          -> Checking ()
checkBody _ Undefined _ = err (InternalError "Checking undefined clause")
checkBody name (NoLhs verb) (ctx, ss, ts) = checkThunk name ctx ss ts verb $> ()
checkBody name (Clauses cs) (ctx, ss, ts) = pure () <* (for cs $ \(lhs, rhs) -> 
  let clauseFC = FC (FC.start $ fcOf lhs) (FC.end $ fcOf rhs)
  in  checkThunk name ctx ss ts (WC clauseFC (lhs :\: rhs)))
