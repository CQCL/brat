{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}

module Brat.Syntax.FuncDecl where

import Brat.FC (FC, WC)
import Brat.Syntax.Abstractor (Abstractor)
import Brat.Syntax.Common (Dir(..), Kind(..))

import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)

data Locality = Extern (String, String) | Local deriving (Eq, Show)

data FuncDecl (io :: Type) (body :: Type) = FuncDecl
  { fnName :: String
  , fnSig  :: io
  , fnBody :: body
  , fnLoc  :: FC
  , fnLocality :: Locality
  }

deriving instance
  forall tm io.
  (forall d k. Eq (tm d k), Eq io
  ,Eq (FunBody tm Noun)
  ,Eq (FunBody tm UVerb)
  ) => Eq (FuncDecl io (FunBody tm Noun))


instance (Show io, Show (FunBody tm Noun))
 => Show (FuncDecl io (FunBody tm Noun)) where
  show FuncDecl{..} = unlines [fnName ++ " :: " ++ show fnSig
                              ,fnName ++ " = " ++ show fnBody]

data FunBody (tm :: Dir -> Kind -> Type) (k :: Kind) where
  -- lhs and rhs
  ThunkOf   :: WC (FunBody tm UVerb) -> FunBody tm Noun
  Clauses   :: NonEmpty (WC Abstractor, WC (tm Chk Noun)) -> FunBody tm UVerb
  NoLhs     :: (WC (tm Chk k)) -> FunBody tm k
  Undefined :: FunBody tm k

deriving instance (forall d k. Show (tm d k)) => Show (FunBody tm k)
deriving instance (forall d k. Eq (tm d k)) => Eq (FunBody tm k)
