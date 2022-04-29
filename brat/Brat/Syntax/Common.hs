{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE RankNTypes, QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module Brat.Syntax.Common (Port,
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
                           SimpleTerm(..),
                           SimpleType(..),
                           CType'(..),
                           pattern Extern, pattern Local, -- No reason not to export Locality if required
                           Decl'(..),
                           Slice(..),
                           Runtime(RtLocal), -- No reason not to export others if required
                           Pattern(..),
                           Abstractor(..),
                           Clause(..)) where

import Brat.FC

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty)
import Data.Kind (Type)

type Port = String

data Quantum = Qubit | Money deriving (Eq, Show)
newtype Row' tm q = R [(Port, SType'' tm q)] deriving (Functor, Foldable, Traversable)
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
  show (Rho (R row)) = intercalate ", " ((\(p, tm) -> p ++ " :: " ++ show tm) <$> row)

copyable :: SType'' tm q -> Bool
copyable = null

data VType' tm
  = C (CType' (Port, VType' tm))
  | SimpleTy SimpleType
  | List (VType' tm)
  | Product (VType' tm) (VType' tm)
  | Vector (VType' tm) (tm Chk Noun)
  -- Thinning from wee end to big end
  | tm Chk Noun :<<<: tm Chk Noun
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
  show (s :<<<: t) = "(" ++ show s ++ " <<< " ++ show t ++ ")"

data SimpleType
  = Natural
  | IntTy
  | Boolean
  | FloatTy
  | TextType
  | UnitTy
  | Star
  deriving Eq

instance Show SimpleType where
  show Natural = "Nat"
  show IntTy = "Int"
  show Boolean = "Bool"
  show FloatTy = "Float"
  show TextType = "String"
  show UnitTy = "Unit"
  show Star = "Type"

data Dir = Syn | Chk deriving (Eq, Show)
data Kind = Noun | Verb deriving (Eq, Show)

data SimpleTerm
  = Num Int
  | Bool Bool
  | Text String
  | Float Double
  | Unit
  deriving Eq
instance Show SimpleTerm where
  show (Num i) = show i
  show (Bool True) = "true"
  show (Bool False) = "false"
  show (Text txt) = show txt
  show (Float f) = show f
  show Unit = "<>"

data CType' io = [io] :-> [io] deriving Functor

instance Show io => Show (CType' io) where
  show (ss :-> ts) = unwords [show ss, "->", show ts]

deriving instance Eq (VType' tm) => Eq (CType' (Port, VType' tm))

instance Semigroup (CType' a) where
  (ss :-> ts) <> (us :-> vs) = (ss ++ us) :-> (ts ++ vs)

data Locality = Extern String | Local deriving (Eq, Show)

data Decl' (io :: Type) (raw :: Dir -> Kind -> Type)
  = Decl { fnName :: String
         , fnSig  :: [io]
         , fnBody :: Clause raw Noun
         , fnLoc  :: FC
         , fnRT   :: Runtime
         , fnLocality :: Locality
         }

deriving instance
  forall raw io.
  (forall d k. Eq (raw d k), Eq io, Eq (Clause raw Noun)) => Eq (Decl' io raw)
--deriving instance (Eq (raw d k), Eq io, Eq (Clause raw k)) => Eq (Decl io raw)

instance (Show io, Show (Clause raw Noun)) => Show (Decl' io raw) where
  show Decl{..} = unlines [fnName ++ " :: " ++ show fnSig
                          ,fnName ++ " = " ++ show fnBody]

-- The extra int is the size of the big end of the thinning
data Slice t = These [t] | From t deriving (Eq, Foldable, Functor, Traversable)

instance Show t => Show (Slice t) where
  show (These xs) = intercalate "," (show <$> xs)
  show (From t)  = show t ++ ".."

-- TODO: allow combinations thereof
-- default to local
data Runtime = RtTierkreis | RtLocal | RtKernel deriving (Eq, Show)

data Pattern tm
 = POnePlus tm
 | PTwoTimes tm
 | PNil
 | PCons tm
 | PSome tm
 | PNone
 deriving (Eq, Foldable, Functor, Traversable)

instance Show tm => Show (Pattern tm) where
  show (POnePlus x) = "succ(" ++ show x ++ ")"
  show (PTwoTimes x) = "doub(" ++ show x ++ ")"
  show PNil = "nil"
  show (PCons x) = "cons(" ++ show x ++ ")"
  show (PSome x) = "some(" ++ show x ++ ")"
  show PNone = "none"

data Abstractor
 = Bind String
 | Abstractor :||: Abstractor
 | APull [Port] (Abstractor)
 | Pat (Pattern Abstractor)
 | Lit SimpleTerm
 | VecLit [Abstractor]
 deriving Eq

instance Show (Abstractor) where
  show (Bind x) = x
  show (x :||: y) = show x ++ ", " ++ show y
  show (APull ps abs) = concat ((++":") <$> ps) ++ show abs
  show (Pat p) = show p
  show (Lit tm) = show tm
  show (VecLit abst) = show abst

data Clause (tm :: Dir -> Kind -> Type) (k :: Kind) where
  -- lhs and rhs
  ThunkOf   :: WC (Clause tm Verb) -> Clause tm Noun
  Clauses   :: NonEmpty (WC Abstractor, WC (tm Chk Noun)) -> Clause tm Verb
  NoLhs     :: (WC (tm Chk k)) -> Clause tm k
  Undefined :: Clause tm k

deriving instance (forall d k. Show (tm d k)) => Show (Clause tm k)
deriving instance (forall d k. Eq (tm d k)) => Eq (Clause tm k)
