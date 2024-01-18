{-# LANGUAGE FlexibleContexts #-}

module Brat.Syntax.Core (Term(..)
                        ,SType
                        ,Input
                        ,Output
                        ,InOut
                        ,CType
                        ,Decl
                        ) where

import Brat.FC
import Brat.Naming
import Brat.Syntax.Common
import Brat.Syntax.Simple
import Brat.UserName

import Data.Kind (Type)
import Data.Maybe (fromJust)

type SType = SType' (Term Chk Noun)

type Input = InOut
type Output = InOut
type InOut = (PortName, KindOr (Term Chk Noun))

type CType = CType' InOut

type Decl = Decl' [InOut] (FunBody Term Noun)

data Term :: Dir -> Kind -> Type where
  Simple   :: SimpleTerm -> Term Chk Noun
  Let      :: WC Abstractor -> WC (Term Syn Noun) -> WC (Term d k) -> Term d k
  NHole    :: Name -> Term Chk Noun
  VHole    :: Name -> Term Chk UVerb
  Pass     :: Term Syn UVerb
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
  Arith    :: ArithOp -> WC (Term Chk Noun) -> WC (Term Chk Noun) -> Term Chk Noun
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
  show (a :|: b) = bracket 2 a ++ ", " ++ bracket 2 b
  show Pass = "pass"
  show (Th comp) = '{' : show comp ++ "}"
  show (TypedTh comp) = "{:" ++ show comp ++ ":}"
  show (Force th) = show th ++ "()"
  show (Forget kv) = "(Forget " ++ show kv ++ ")"
  show (Emb x) = '「' : show x ++ "」"
  show tm@(Arith op lhs rhs) = let prec = fromJust (precedence tm) in
                                 unwords [bracket prec lhs
                                         ,showOp op
                                         -- Arith ops are left nested, so call
                                         -- the rhs with `prec + 1`
                                         ,bracket (prec + 1) rhs
                                         ]
   where
    showOp = \case
      Add -> "+"
      Mul -> "*"
      Pow -> "^"
      Sub -> "-"
      Div -> "/"
  show (Pull ps x) = showList ps ++ bracket 1 x
   where
    showList [] = "[]:"
    showList ps = concatMap (++":") ps

  show (Var x) = show x
  -- Nested applications should be bracketed too, hence 4 instead of 3
  show (fun :$: arg) = bracket 4 fun ++ ('(' : show arg ++ ")")
  show (tm ::: ty) = bracket 4 tm ++ " :: " ++ show ty
  show (a :-: b) = bracket 2 a ++ "; " ++ bracket 3 b
  show (xs :\: bod) = show xs ++ " => " ++ bracket 1 bod
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

-- Wrap a term in brackets if its `precedence` is looser than `n`
bracket :: Int -> WC (Term d k) -> String
bracket n (WC _ tm) = case precedence tm of
  Just m | m < n -> '(' : show tm ++ ")"
  _ -> show tm

-- Report tightness of binding, or `Nothing` if not a binary op
precedence :: Term d k -> Maybe Int
precedence (Let _ _ _) = Just 0
precedence (_ :\: _) = Just 1
precedence (_ :-: _) = Just 2
precedence (Pull _ _) = Just 3
precedence (_ :|: _) = Just 4
precedence (_ :$: _) = Just 5
precedence (_ ::: _) = Just 6
precedence (Arith op _ _) = case op of
  Add -> Just 7
  Sub -> Just 7
  Div -> Just 8
  Mul -> Just 8
  Pow -> Just 9
precedence _ = Nothing
