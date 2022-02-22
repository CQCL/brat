{-# LANGUAGE FlexibleContexts #-}

module Brat.Syntax.Core where

import Brat.FC
import Brat.Graph
import Brat.Naming
import Brat.Syntax.Common
import Brat.UserName
import Util

import Control.Arrow ((&&&))
import Data.Kind (Type)
import Data.List (intercalate)
import Data.Maybe (fromJust, isJust)

type VType = VType' Term

type Input = Input' Term
type Output = Output' Term

type InOut = (Port, VType)

merge :: [InOut] -> [InOut]
merge ((_, C (ss :-> ts))
      :(_, C (us :-> vs))
      :xs) = merge $ ("thunk", C $ (ss <> us) :-> (ts <> vs)):xs
merge ((_, K (R ss) (R ts))
      :(_, K (R us) (R vs))
      :xs) = merge $ ("thunk", K (R (ss <> us)) (R (ts <> vs))):xs
merge (x:xs) = x : merge xs
merge [] = []


type CType = CType' InOut

-- instance Eq VType => Eq CType where
--   xs == ys = (snd <$> xs) == (snd <$> ys)

type Decl = Decl' InOut Term

data Term :: Dir -> Kind -> Type where
  Simple   :: SimpleTerm -> Term Chk Noun
  Let      :: WC Abstractor -> WC (Term Syn Noun) -> WC (Term d k) -> Term d k
  Pair     :: WC (Term Chk Noun) -> WC (Term Chk Noun) -> Term Chk Noun
  NHole    :: Name -> Term Chk Noun
  VHole    :: Name -> Term Chk Verb
  (:|:)    :: WC (Term d k) -> WC (Term d k) -> Term d k
  Th       :: WC (Term Chk Verb) -> Term Chk Noun
  Emb      :: WC (Term Syn k) -> Term Chk k
  Pull     :: [Port] -> WC (Term Chk k) -> Term Chk k
  Var      :: UserName -> Term Syn Noun  -- Look up in noun (value) env
  Bound    :: Int -> Term Syn Noun  -- Look up in noun (value) env
  (:$:)    :: WC (Term Syn Noun) -> WC (Term Chk Noun) -> Term Syn Noun
  -- TODO: Make it possible for Output to be (Port, SType) when using this in kernels
  (:::)    :: WC (Term Chk k) -> [Output] -> Term Syn k
  Do       :: WC (Term Syn Noun) -> Term Syn Verb
  -- vertical juxtaposition (diagrammatic composition)
  (:-:)    :: WC (Term Syn k) -> WC (Term d Verb) -> Term d k
  (:\:)    :: WC Abstractor -> WC (Term d Noun) -> Term d Verb
  Vec      :: [WC (Term Chk Noun)] -> Term Chk Noun
  Slice    :: WC (Term Chk Noun) -> Slice (WC (Term Chk Noun)) -> Term Chk Noun
  Select   :: WC (Term Syn Noun) -> WC (Term Chk Noun) -> Term Chk Noun
  Thin     :: WC (Term Chk Noun) -> Term Syn Noun
  Pattern  :: WC (Pattern (WC (Term Chk Noun))) -> Term Chk Noun

deriving instance Eq (Term d k)

instance Show (Term d k) where
  show (Simple tm) = show tm
  show (Pair a b) = '[' : show a ++ ", " ++ show b ++ "]"
  show (NHole (MkName (name:_))) = '?' : show (MkName [name])
  show (NHole (MkName [])) = "?<root>"
  show (VHole (MkName (name:_))) = '?' : show (MkName [name])
  show (VHole (MkName [])) = "?<root>"
  show (a :|: b) = show a ++ ", " ++ show b
  show (Th comp) = '{' : show comp ++ "}"
  show (Emb x) = '「' : show x ++ "」"
  show (Pull ps (WC _ (Emb (WC _ (fun :$: arg)))))
    = unwords [show fun
              ,"(" ++ concat ((++":") <$> ps)
              ,show arg ++ ")"
              ]
  show (Pull ps x) = concat ((++":") <$> ps) ++ show x
  show (Var x) = show x
  show (Bound i) = '^':show i
  show (fun :$: arg) = show fun ++ ('(' : show arg ++ ")")
  show (tm ::: ty) = show tm ++ " :: " ++ show ty
  show (Do f) = show f ++ "!"
  show (a :-: b) = show a ++ "; " ++ show b
  show (xs :\: bod) = show xs ++ " -> " ++ show bod
  show (Vec xs) = '[' : intercalate ", " (show <$> xs) ++ "]"
  show (Slice _ slice) = show slice
  show (Select vec th) = show vec ++ "{" ++ show th ++ "}"
  show (Pattern p) = show p

expandDecls :: [Decl] -> Term d k -> Term d k
expandDecls env tm = expand tm
 where
  expand :: Term d k -> Term d k
  expand (Simple tm) = Simple tm
  expand (Pair a b)  = Pair (expand <$> a) (expand <$> b)
  expand x@(NHole _) = x
  expand x@(VHole _) = x
  expand (a :|: b) = (expand <$> a) :|: (expand <$> b)
  expand (Th v) = Th (expand <$> v)
  expand (Emb syn) = Emb (expand <$> syn)
  expand (Pull ps t) = Pull ps (expand <$> t)
--  expand (Var x) = lookupBy ((==x) . fnName) fnBody
  expand (fun :$: arg) = (expand <$> fun) :$: (expand <$> arg)
  expand (tm ::: ty) = (expand <$> tm) ::: ty
  expand (Do f) = Do (expand <$> f)
  expand (a :-: b) = (expand <$> a) :-: (expand <$> b)
  expand (abst :\: body) = abst :\: (expand <$> body)
  expand (Vec xs) = Vec (fmap expand <$> xs)
  expand (Pattern tm) = Pattern $ fmap (fmap expand) <$> tm
  expand tm = error $ "Unimplemented: expand " ++ show tm
