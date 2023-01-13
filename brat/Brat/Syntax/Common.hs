{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE RankNTypes, QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Brat.Syntax.Common (PortName,
                           Row,
                           -- constructors for Quantum (type could be exported if required):
                           pattern Qubit, pattern Money,
                           -- constructor for Row (do not export Row'):
                           pattern R,
                           SType',
                           -- constructors for SType' (do not export SType''):
                           pattern Q, pattern Bit, pattern Of, pattern Rho,
                           copyable,
                           smap,
                           Dir(..),
                           Kind(..),
                           Diry(..),
                           Kindy(..),
                           CType'(..),
                           pattern Extern, pattern Local, -- No reason not to export Locality if required
                           Decl'(..),
                           Runtime(RtLocal), -- No reason not to export others if required
                           Pattern(..),
                           Abstractor(..), occursInAbstractor,
                           FunBody(..),
                           showSig,
                           TypeKind(..), KindOr,
                           showRow,
                           NamedPort(..),
                           Src, Tgt,
                           OutPort(..), InPort(..),
                           pattern PNone,
                           pattern PSome,
                           pattern POnePlus,
                           pattern PTwoTimes,
                           pattern PNil,
                           pattern PCons,
                           Mode(..),
                           Modey(..),
                           End(..)
                          ) where

import Brat.FC
import Brat.Syntax.Abstractor
import Brat.Syntax.Port

import Data.Bifunctor (second)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Kind (Type)

data Mode = Brat | Kernel

data Modey :: Mode -> Type where
  Braty :: Modey Brat
  Kerny :: Modey Kernel

data Quantum = Qubit | Money deriving (Eq, Show)
newtype Row' tm q = R [(PortName, SType'' tm q)] deriving (Functor, Foldable, Traversable)

type Row tm = Row' tm Quantum

deriving instance Show (SType'' tm q) => Show (Row' tm q)

instance Eq (SType'' tm q) => Eq (Row' tm q) where
  (R r) == (R r') = (snd <$> r) == (snd <$> r')

type SType' tm = SType'' tm Quantum

-- N.B. Functor, Foldable, Traversable instances are definined for mapping the
-- type of qubits, not the type of subterms
data SType'' tm q
 = Q q
 | Bit
 | Of (SType'' tm q) tm
 | Rho (Row' tm q)
 deriving (Functor, Foldable, Traversable)

smap :: (tm -> tm') -> SType'' tm q -> SType'' tm' q
smap f (Of ty n) = Of (smap f ty) (f n)
smap f (Rho (R xs)) = Rho (R (second (smap f) <$> xs))
-- Boring cases
smap _ (Q q) = Q q
smap _ Bit = Bit

deriving instance Eq tm => Eq (SType' tm)

instance (Show q, Show tm) => Show (SType'' tm q) where
  show (Q q) = show q
  show Bit = "Bool"
  show (Of ty n) = "Vec(" ++ show ty ++ ", " ++ show n ++ ")"
  show (Rho (R row)) = '(' : (intercalate ", " ((\(p, tm) -> p ++ " :: " ++ show tm) <$> row)) ++ ")"

copyable :: SType'' tm q -> Bool
copyable = null

data TypeKind = Star [(PortName, TypeKind)] | Nat
  deriving (Eq, Show)

type KindOr = Either TypeKind

instance {-# OVERLAPPING #-} Show a => Show (KindOr a) where
  show (Left k) = show k
  show (Right ty) = show ty

-- How to typecheck the *outputs* of a term
data Dir = Syn -- the node synthesizes (tells us) its outputs
         | Chk -- the node must be told the type of its outputs
   deriving (Eq, Show)

data Diry :: Dir -> Type where
  Syny :: Diry Syn
  Chky :: Diry Chk
deriving instance Show (Diry d)


-- How to typecheck the *inputs* of a term
data Kind = Noun -- there are no inputs
          | UVerb -- a verb with unknown inputs, i.e. it must be told the type of its inputs (it knows how many to take)
          | KVerb -- a verb with known inputs, i.e. it synthesizes (tells us) the number and type of inputs it needs
   deriving (Eq, Show)

data Kindy :: Kind -> Type where
  Nouny :: Kindy Noun
  UVerby :: Kindy UVerb
  KVerby :: Kindy KVerb
deriving instance Show (Kindy k)

data CType' io = [io] :-> [io] deriving (Foldable, Functor, Traversable)

instance Show io => Show (CType' io) where
  show (ss :-> ts) = unwords [show ss, "->", show ts]

deriving instance Eq io => Eq (CType' io)

instance Semigroup (CType' (PortName, ty)) where
  (ss :-> ts) <> (us :-> vs) = (ss <> us) :-> (ts <> vs)

instance Semigroup (Row' tm q) where
  R ss <> R ts = R (ss <> ts)

data Locality = Extern String | Local deriving (Eq, Show)

data Decl' (io :: Type) (body :: Type)
  = Decl { fnName :: String
         , fnSig  :: [io]
         , fnBody :: body
         , fnLoc  :: FC
         , fnRT   :: Runtime
         , fnLocality :: Locality
         }

deriving instance
  forall tm io.
  (forall d k. Eq (tm d k), Eq io
  ,Eq (FunBody tm Noun)
  ,Eq (FunBody tm UVerb)
  ) => Eq (Decl' io (FunBody tm Noun))

instance (Show io, Show (FunBody tm Noun))
 => Show (Decl' io (FunBody tm Noun)) where
  show Decl{..} = unlines [fnName ++ " :: " ++ show fnSig
                          ,fnName ++ " = " ++ show fnBody]

-- TODO: allow combinations thereof
-- default to local
data Runtime = RtTierkreis | RtLocal | RtKernel deriving (Eq, Show)

data FunBody (tm :: Dir -> Kind -> Type) (k :: Kind) where
  -- lhs and rhs
  ThunkOf   :: WC (FunBody tm UVerb) -> FunBody tm Noun
  Clauses   :: NonEmpty (WC Abstractor, WC (tm Chk Noun)) -> FunBody tm UVerb
  NoLhs     :: (WC (tm Chk k)) -> FunBody tm k
  Undefined :: FunBody tm k

deriving instance (forall d k. Show (tm d k)) => Show (FunBody tm k)
deriving instance (forall d k. Eq (tm d k)) => Eq (FunBody tm k)

showSig :: Show ty => [(String, ty)] -> String
showSig [] = "()"
showSig (x:xs) = showSig1 (x :| xs)
 where
  showSig1 :: Show ty => NonEmpty (String, ty) -> String
  showSig1 (x :| xs) = intercalate ", "
                       [ '(':p ++ " :: " ++ show ty ++ ")"
                       | (p, ty) <- x:xs ]

showRow :: Show ty => [(NamedPort e, ty)] -> String
showRow [] = "()"
showRow (x:xs) = intercalate ", " [ '(':(portName p) ++ " :: " ++ show ty ++ ")"
                                  | (p, ty) <- x:xs]
