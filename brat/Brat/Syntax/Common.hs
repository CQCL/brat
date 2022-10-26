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
                           Runtime(RtLocal), -- No reason not to export others if required
                           Pattern(..),
                           Abstractor(..),
                           Clause(..),
                           mergeSigs, showRow,
                           pattern PSome,
                           pattern PNone,
                           pattern POnePlus,
                           pattern PTwoTimes,
                           pattern PNil,
                           pattern PCons,

                          ) where

import Brat.FC

import Data.Char (isDigit)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.Reverse.StrictSpine as Rev (span)
import Data.Kind (Type)
import qualified Data.Set as Set

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
  show (Rho (R row)) = '(' : (intercalate ", " ((\(p, tm) -> p ++ " :: " ++ show tm) <$> row)) ++ ")"

copyable :: SType'' tm q -> Bool
copyable = null

data VType' tm
  = C (CType' (Port, VType' tm))
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

instance Semigroup (CType' (Port, ty)) where
  (ss :-> ts) <> (us :-> vs) = (mergeSigs ss us) :-> (mergeSigs ts vs)

instance Semigroup (Row' tm q) where
  R ss <> R ts = R (mergeSigs ss ts)

-- For use in semigroup instances of `CType` and `Row`
mergeSigs :: [(Port, a)] -> [(Port, a)] -> [(Port, a)]
mergeSigs xs ys = aux Set.empty (xs ++ ys)
 where
  aux :: Set.Set Port -> [(Port, a)] -> [(Port, a)]
  aux _ [] = []
  aux seen ((p,ty):rest)
   | Set.member p seen
   = let p' = head $ filter (\x -> Set.notMember x seen) (names p) in
       (p', ty) : aux (Set.insert p' seen) rest
   | otherwise = (p, ty) : aux (Set.insert p seen) rest

  names :: Port -> [String]
  names port
    = let (prefix, xs) = Rev.span isDigit port
          ixs = case xs of
                  [] -> [(1 :: Int)..]
                  n  -> [(read n :: Int) + 1..]
      in addIndex prefix <$> ixs

  addIndex :: String -> Int -> String
  addIndex s n = s ++ show n

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

-- TODO: allow combinations thereof
-- default to local
data Runtime = RtTierkreis | RtLocal | RtKernel deriving (Eq, Show)

-- Ways to bind one thing
data Pattern
 = Bind String
 | PCon String Abstractor
 | Lit SimpleTerm
 | DontCare
 deriving Eq

instance Show Pattern where
  show (Bind x) = x
  show (PCon c AEmpty) = c
  show (PCon c arg) = case prettyPat (PCon c arg) of
    Just xs -> show xs
    Nothing -> c ++ "(" ++ show arg ++ ")"
  show (Lit tm) = show tm
  show DontCare = "_"

prettyPat :: Pattern -> Maybe [Pattern]
prettyPat PNil = Just []
prettyPat (PCons x xs) = (x:) <$> prettyPat xs
prettyPat _ = Nothing

pattern PNone, PNil :: Pattern
pattern PNone = PCon "none" AEmpty
pattern PNil = PCon "nil" AEmpty

pattern PSome, POnePlus, PTwoTimes :: Pattern -> Pattern
pattern PSome x = PCon "some" (APat x)
pattern POnePlus x = PCon "succ" (APat x)
pattern PTwoTimes x = PCon "doub" (APat x)

pattern PCons :: Pattern -> Pattern -> Pattern
pattern PCons x xs = PCon "cons" (APat x :||: APat xs)

-- Ways to bind a row of things
data Abstractor
 -- There's nothing and that's how we want it
 = AEmpty
 | Abstractor :||: Abstractor
 -- Pull port name being abstracted to the front
 -- b:x, c:y, z -> ...
 | APull [Port] (Abstractor)
 | APat Pattern
 deriving Eq

instance Show (Abstractor) where
  show AEmpty = "<empty>"
  show (x :||: y) = show x ++ ", " ++ show y
  show (APull ps abs) = concat ((++":") <$> ps) ++ show abs
  show (APat p) = show p

data Clause (tm :: Dir -> Kind -> Type) (k :: Kind) where
  -- lhs and rhs
  ThunkOf   :: WC (Clause tm Verb) -> Clause tm Noun
  Clauses   :: NonEmpty (WC Abstractor, WC (tm Chk Noun)) -> Clause tm Verb
  NoLhs     :: (WC (tm Chk k)) -> Clause tm k
  Undefined :: Clause tm k

deriving instance (forall d k. Show (tm d k)) => Show (Clause tm k)
deriving instance (forall d k. Eq (tm d k)) => Eq (Clause tm k)

showRow :: Show ty => NonEmpty ((a, String), ty) -> String
showRow (x :| xs) = intercalate ", " [ '(':p ++ " :: " ++ show ty ++ ")"
                                     | ((_, p), ty) <- x:xs ]
