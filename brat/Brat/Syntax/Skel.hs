module Brat.Syntax.Skel where

import Brat.FC
import Brat.Syntax.Common
import Brat.Syntax.Core
import Brat.UserName

-- A version of `Term` which doesn't include directions or kinds for easy
-- manipulation in the LSP mode (for now). This should be produced by forgetting
-- this info, when looking at `Term`s which have already been checked.

subTerms :: Skel -> [WC Skel]
subTerms (SJuxtNoun a b)    = [a,b]
subTerms (SJuxtVerb a b)    = [a,b]
subTerms (STh a)        = [a]
subTerms (SForce a)     = [a]
subTerms (SPull _ x)    = [x]
subTerms (SApp f a)     = [f, a]
subTerms (SAnn x _)     = [x]
subTerms (SComp a b)    = [a, b]
subTerms (SLam _ body)  = [body]
subTerms _ = []

class Juxt k where
  stripJuxt :: Term d k -> Skel

instance Juxt Noun where
  stripJuxt (a :|: b) = SJuxtNoun (stripInfo <$> a) (stripInfo <$> b)

instance Juxt Verb where
  stripJuxt (a :|: b) = SJuxtVerb (stripInfo <$> a) (stripInfo <$> b)

stripInfo :: Juxt k => Term d k -> Skel
stripInfo (Simple tm) = SSimple tm
stripInfo (NHole x) = SHole (show x)
stripInfo (VHole x) = SHole (show x)
stripInfo x@(_ :|: _) = stripJuxt x
stripInfo (Th comp) = STh (stripInfo <$> comp)
stripInfo (Force comp) = SForce (stripInfo <$> comp)
stripInfo (Emb x) = stripInfo (unWC x)
stripInfo (Pull ps x) = SPull ps (stripInfo <$> x)
stripInfo (Var x) = SVar x
stripInfo (fun :$: arg) = SApp (stripInfo <$> fun) (stripInfo <$> arg)
stripInfo (tm ::: ty) = SAnn (stripInfo <$> tm) ty
stripInfo (a :-: b) = SComp (stripInfo <$> a) (stripInfo <$> b)
stripInfo (xs :\: bod) = SLam xs (stripInfo <$> bod)
stripInfo (Let abs x y) = SLet abs (stripInfo <$> x) (stripInfo <$> y)
stripInfo (Con c arg) = SCon c (stripInfo <$> arg)

data Skel where
  SSimple   :: SimpleTerm -> Skel
  SHole     :: String -> Skel
  SJuxtVerb :: WC Skel -> WC Skel -> Skel
  SJuxtNoun :: WC Skel -> WC Skel -> Skel
  STh       :: WC Skel -> Skel
  SForce    :: WC Skel -> Skel
  SPull     :: [Port] -> WC Skel -> Skel
  SVar      :: UserName -> Skel
  SBound    :: Int -> Skel
  SApp      :: WC Skel -> WC Skel -> Skel
  SAnn      :: WC Skel -> [Output] -> Skel
  SComp     :: WC Skel -> WC Skel -> Skel
  SLam      :: WC Abstractor -> WC Skel -> Skel
  SLet      :: WC Abstractor -> WC Skel -> WC Skel -> Skel
  SCon      :: UserName -> WC Skel -> Skel

deriving instance Show Skel
deriving instance Eq Skel
