{-# LANGUAGE FlexibleContexts #-}

module Brat.Syntax.Core where

import Brat.FC
import Brat.Naming
import Brat.Syntax.Common
import Brat.UserName

import Data.Kind (Type)

type VType = VType' Term
type SType = SType' Term

type Input = InOut
type Output = InOut
type InOut = (Port, VType)

type CType = CType' InOut

-- instance Eq VType => Eq CType where
--   xs == ys = (snd <$> xs) == (snd <$> ys)

type Decl = Decl' InOut Term

data Term :: Dir -> Kind -> Type where
  Simple   :: SimpleTerm -> Term Chk Noun
  Let      :: WC Abstractor -> WC (Term Syn Noun) -> WC (Term d k) -> Term d k
  NHole    :: Name -> Term Chk Noun
  VHole    :: Name -> Term Chk Verb
  (:|:)    :: WC (Term d k) -> WC (Term d k) -> Term d k
  Th       :: WC (Term Chk Verb) -> Term Chk Noun
  Force    :: WC (Term Syn Noun) -> Term Syn Verb
  Emb      :: WC (Term Syn k) -> Term Chk k
  Pull     :: [Port] -> WC (Term Chk k) -> Term Chk k
  Var      :: UserName -> Term Syn Noun  -- Look up in noun (value) env
  (:$:)    :: WC (Term Syn Noun) -> WC (Term Chk Noun) -> Term Syn Noun
  -- TODO: Make it possible for Output to be (Port, SType) when using this in kernels
  (:::)    :: WC (Term Chk k) -> [Output] -> Term Syn k
  -- vertical juxtaposition (diagrammatic composition)
  (:-:)    :: WC (Term Syn k) -> WC (Term d Verb) -> Term d k
  (:\:)    :: WC Abstractor -> WC (Term d Noun) -> Term d Verb
  Pattern  :: WC (Pattern (WC (Term Chk Noun))) -> Term Chk Noun

deriving instance Eq (Term d k)

instance Show (Term d k) where
  show (Let abs xs body)
    = unwords ["let", show abs, "=", show xs, "in", show body]
  show (Simple tm) = show tm
  show (NHole (MkName (name:_))) = '?' : show (MkName [name])
  show (NHole (MkName [])) = "?<root>"
  show (VHole (MkName (name:_))) = '?' : show (MkName [name])
  show (VHole (MkName [])) = "?<root>"
  show (a :|: b) = show a ++ ", " ++ show b
  show (Th comp) = '{' : show comp ++ "}"
  show (Force th) = show th ++ "()"
  show (Emb x) = '「' : show x ++ "」"
  show (Pull ps (WC _ (Emb (WC _ (fun :$: arg)))))
    = unwords [show fun
              ,"(" ++ concat ((++":") <$> ps)
              ,show arg ++ ")"
              ]
  show (Pull ps x) = concat ((++":") <$> ps) ++ show x
  show (Var x) = show x
  show (fun :$: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::: ty) = show tm ++ " :: " ++ show ty
  show (a :-: b) = show a ++ "; " ++ show b
  show (xs :\: bod) = show xs ++ " => " ++ show bod
  show (Pattern p) = prettyVec (unWC p)

prettyVec p = case patList p of
  Just xs -> show xs
  Nothing -> show p
 where
  patList :: Pattern (WC (Term Chk Noun)) -> Maybe [Term Chk Noun]
  patList PNil = Just []
  patList (PCons (WC _ (a :|: (WC _ (Pattern (WC _ p)))))) = ((unWC a):) <$> patList p
  patList _ = Nothing

expandDecls :: [Decl] -> Term d k -> Term d k
expandDecls _ tm = expand tm
 where
  expand :: Term d k -> Term d k
  expand (Simple tm) = Simple tm
  expand x@(NHole _) = x
  expand x@(VHole _) = x
  expand (a :|: b) = (expand <$> a) :|: (expand <$> b)
  expand (Th v) = Th (expand <$> v)
  expand (Force v) = Force (expand <$> v)
  expand (Emb syn) = Emb (expand <$> syn)
  expand (Pull ps t) = Pull ps (expand <$> t)
--  expand (Var x) = lookupBy ((==x) . fnName) fnBody
  expand (fun :$: arg) = (expand <$> fun) :$: (expand <$> arg)
  expand (tm ::: ty) = (expand <$> tm) ::: ty
  expand (a :-: b) = (expand <$> a) :-: (expand <$> b)
  expand (abst :\: body) = abst :\: (expand <$> body)
  expand (Pattern tm) = Pattern $ fmap (fmap expand) <$> tm
  expand tm = error $ "Unimplemented: expand " ++ show tm
