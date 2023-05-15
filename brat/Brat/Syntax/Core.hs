{-# LANGUAGE FlexibleContexts #-}

module Brat.Syntax.Core where

import Brat.FC
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.UserName

import Data.Kind (Type)

type SType = SType' (Term Chk Noun)

type Input = InOut
type Output = InOut
type InOut = (PortName, KindOr (Term Chk Noun))

type CType = CType' InOut

type Decl = Decl' InOut (FunBody Term Noun)

data Term :: Dir -> Kind -> Type where
  Simple   :: SimpleTerm -> Term Chk Noun
  Let      :: WC Abstractor -> WC (Term Syn Noun) -> WC (Term d k) -> Term d k
  NHole    :: Name -> Term Chk Noun
  VHole    :: Name -> Term Chk UVerb
  Empty    :: Term Chk Noun -- The empty row (monoidal unit of :|:)
  -- Parallel composition, aka juxtaposition
  (:|:)    :: WC (Term d k) -> WC (Term d k) -> Term d k
  Th       :: WC (Term Chk UVerb) -> Term Chk Noun
  TypedTh  :: WC (Term Syn KVerb) -> Term Syn Noun
  Force    :: WC (Term Syn Noun) -> Term Syn KVerb
  Emb      :: WC (Term Syn k) -> Term Chk k
  Forget   :: WC (Term d KVerb) -> Term d UVerb
  Pull     :: [PortName] -> WC (Term Chk k) -> Term Chk k
  Var      :: UserName -> Term Syn Noun  -- Look up in noun (value) env
  -- Things which are bound in the global context
  Par      :: End -> Term Syn Noun
  -- Things which are bound in a type signature
  Inx      :: Int -> Term Syn Noun
  -- Type annotations (annotating a term with its outputs)
  -- TODO: Make it possible for Output to be (PortName, SType) when using this in kernels
  (:::)    :: WC (Term Chk Noun) -> [Output] -> Term Syn Noun
  -- Composition: values fed from source (first) into dest (second),
  -- of number/type determined by the source
  (:-:)    :: WC (Term Syn k) -> WC (Term d UVerb) -> Term d k
  -- Application of function (first) to values coming from argument (second)
  -- of number/type determined by the function. (aka, Reverse Composition)
  (:$:) :: WC (Term d KVerb) -> WC (Term Chk k) -> Term d k
  (:\:)    :: WC Abstractor -> WC (Term d Noun) -> Term d UVerb
  -- Type constructors
  Con      :: UserName -> WC (Term Chk Noun) -> Term Chk Noun
  -- Brat function types
  C        :: CType' (PortName, KindOr (Term Chk Noun)) -> Term Chk Noun
  -- Kernel types
  K        :: Row (Term Chk Noun) -> Row (Term Chk Noun) -> Term Chk Noun

deriving instance Eq (Term d k)

instance Show (Term d k) where
  show (Simple tm) = show tm
  show (Let abs xs body)
    = unwords ["let", show abs, "=", show xs, "in", show body]
  show (NHole (MkName (name:_))) = '?' : show (MkName [name])
  show (NHole (MkName [])) = "?<root>"
  show (VHole (MkName (name:_))) = '?' : show (MkName [name])
  show (VHole (MkName [])) = "?<root>"
  show Empty = "()"
  show (a :|: b) = show a ++ ", " ++ show b
  show (Th comp) = '{' : show comp ++ "}"
  show (TypedTh comp) = "{:" ++ show comp ++ ":}"
  show (Force th) = show th ++ "()"
  show (Forget kv) = "(Forget " ++ show kv ++ ")"
  show (Emb x) = '「' : show x ++ "」"
  show (Pull [] x) = "[]:" ++ show x
  show (Pull ps x) = concat ((++":") <$> ps) ++ show x
  show (Var x) = show x
  show (Par nm) = "Par " ++ show nm
  show (Inx n)  = '^' : show n
  show (fun :$: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::: ty) = show tm ++ " :: " ++ show ty
  show (a :-: b) = show a ++ "; " ++ show b
  show (xs :\: bod) = show xs ++ " => " ++ show bod
  show p@(Con c arg) = case prettyPat p of
    Just ps -> show ps
    Nothing -> {-case unWC arg of
      Empty -> show c
      _ -> -}show c ++ "(" ++ show arg ++ ")"
   where
    prettyPat :: Term Chk Noun -> Maybe [Term Chk Noun]
    prettyPat (Con (PrefixName [] "nil") (WC _ Empty)) = Just []
    prettyPat (Con (PrefixName [] "cons") (WC _ (x :|: xs))) = ((unWC x) :) <$> prettyPat (unWC xs)
    prettyPat _ = Nothing

  show (C f) = "{" ++ show f ++ "}"
  show (K (R ss) (R ts)) = showSig ss ++ " -o " ++ showSig ts
