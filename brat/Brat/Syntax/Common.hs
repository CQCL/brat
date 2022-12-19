{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE RankNTypes, QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

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
                           VType'(..),
                           Dir(..),
                           Kind(..),
                           Diry(..),
                           Kindy(..),
                           CType'(..),
                           pattern Extern, pattern Local, -- No reason not to export Locality if required
                           Decl'(..),
                           Runtime(RtLocal), -- No reason not to export others if required
                           Pattern(..),
                           Abstractor(..),
                           Clause(..),
                           showRow,
                           pattern PSome,
                           NamedPort(..),
                           Src, Tgt,
                           OutPort(..), InPort(..),
                           pattern PNone,
                           pattern POnePlus,
                           pattern PTwoTimes,
                           pattern PNil,
                           pattern PCons,

                          ) where

import Brat.FC
import Brat.Syntax.Abstractor
import Brat.Syntax.Simple (SimpleType)
import Brat.Syntax.Port

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Kind (Type)

data Quantum = Qubit | Money deriving (Eq, Show)
newtype Row' tm q = R [(PortName, SType'' tm q)] deriving (Functor, Foldable, Traversable)
type Row tm = Row' tm Quantum

deriving instance Show (SType'' tm q) => Show (Row' tm q)

instance Eq (SType'' tm q) => Eq (Row' tm q) where
  (R r) == (R r') = (snd <$> r) == (snd <$> r')

type SType' tm = SType'' tm Quantum

data SType'' tm q
 = Q q
 | Bit
 | Of (SType'' tm q) (tm Chk Noun)
 | Rho (Row' tm q)
 deriving (Functor, Foldable, Traversable)

deriving instance Eq (tm Chk Noun) => Eq (SType' tm)

instance (Show q, Show (tm Chk Noun)) => Show (SType'' tm q) where
  show (Q q) = show q
  show Bit = "Bool"
  show (Of ty n) = "Vec(" ++ show ty ++ ", " ++ show n ++ ")"
  show (Rho (R row)) = '(' : (intercalate ", " ((\(p, tm) -> p ++ " :: " ++ show tm) <$> row)) ++ ")"

copyable :: SType'' tm q -> Bool
copyable = null

data VType' tm
  = C (CType' (PortName, VType' tm))
  | SimpleTy SimpleType
  | List (VType' tm)
  | Product (VType' tm) (VType' tm)
  | Vector (VType' tm) (tm Chk Noun)
  | K (Row tm) (Row tm)
  | Option (VType' tm)

deriving instance Eq (tm Chk Noun) => Eq (VType' tm)

instance Show (tm Chk Noun) => Show (VType' tm) where
  show (C cty) = '{' : show cty ++ "}"
  show (SimpleTy ty) = show ty
  show (List ty) = "List(" ++ show ty ++ ")"
  show (Product s t) = "Pair(" ++ show s ++ ", " ++ show t ++ ")"
  show (Vector ty n) = "Vec(" ++ show ty ++ ", " ++ show n ++ ")"
  show (K ins outs) = '{' : show ins ++ " -o " ++ show outs ++ "}"
  show (Option ty) = "Option(" ++ show ty ++ ")"

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

data CType' io = [io] :-> [io] deriving Functor

instance Show io => Show (CType' io) where
  show (ss :-> ts) = unwords [show ss, "->", show ts]

deriving instance Eq (VType' tm) => Eq (CType' (PortName, VType' tm))

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
  ,Eq (Clause tm Noun)
  ,Eq (Clause tm UVerb)
  ) => Eq (Decl' io (Clause tm Noun))

instance (Show io, Show (Clause tm Noun))
 => Show (Decl' io (Clause tm Noun)) where
  show Decl{..} = unlines [fnName ++ " :: " ++ show fnSig
                          ,fnName ++ " = " ++ show fnBody]

-- TODO: allow combinations thereof
-- default to local
data Runtime = RtTierkreis | RtLocal | RtKernel deriving (Eq, Show)

data Clause (tm :: Dir -> Kind -> Type) (k :: Kind) where
  -- lhs and rhs
  ThunkOf   :: WC (Clause tm UVerb) -> Clause tm Noun
  Clauses   :: NonEmpty (WC Abstractor, WC (tm Chk Noun)) -> Clause tm UVerb
  NoLhs     :: (WC (tm Chk k)) -> Clause tm k
  Undefined :: Clause tm k

deriving instance (forall d k. Show (tm d k)) => Show (Clause tm k)
deriving instance (forall d k. Eq (tm d k)) => Eq (Clause tm k)

showRow :: Show ty => NonEmpty (NamedPort e, ty) -> String
showRow (x :| xs) = intercalate ", " [ '(':(portName p) ++ " :: " ++ show ty ++ ")"
                                     | (p, ty) <- x:xs]
