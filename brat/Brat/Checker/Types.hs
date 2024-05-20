{-# LANGUAGE UndecidableInstances #-}

module Brat.Checker.Types (Overs, Unders
                          ,Outputs, Inputs
                          ,ChkConnectors, SynConnectors
                          ,Mode(..), Modey(..)
                          ,Env, VEnv, KEnv, EnvData
                          ,Store(..), EndType(..)
                          ,TypedHole(..)
                          ,initStore
                          ) where

import Brat.Checker.Quantity
import Brat.FC (FC)
import Brat.Naming (Name)
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.UserName (UserName)
import Hasochism (N(..))

import Data.Kind (Type)
import qualified Data.Map as M

-- Inputs against which a term is checked
type family Overs (m :: Mode) (k :: Kind) :: Type where
  Overs m Noun = ()
  Overs m UVerb = [(Src, BinderType m)]
  Overs m KVerb = ()

-- Inputs synthesized by the term
type family Inputs (m:: Mode) (k :: Kind) :: Type where
  Inputs m Noun = ()
  Inputs m UVerb = ()
  Inputs m KVerb = [(Tgt, BinderType m)]

-- Outputs against which a term is checked
type family Unders (m :: Mode) (d :: Dir) :: Type where
  Unders m Syn = ()
  Unders m Chk = [(Tgt, BinderType m)]

-- Outputs synthesized by the term
type family Outputs (m :: Mode) (d :: Dir) :: Type where
  Outputs m Syn = [(Src, BinderType m)]
  Outputs m Chk = ()

type ChkConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Overs m k, Unders m d)
type SynConnectors (m :: Mode) (d :: Dir) (k :: Kind) = (Inputs m k, Outputs m d)

type family EnvData (m :: Mode) where
  -- Brat variables can stand for rows when referring to a top level
  -- binding. Most of the time, this will be a singleton list
  EnvData Brat = [(Src, BinderType Brat)]
  EnvData Kernel = (Quantity, (Src, BinderType Kernel))

type Env e = M.Map UserName e
type VEnv = Env (EnvData Brat)
type KEnv = Env (EnvData Kernel)

data TypedHole
  = NBHole Name FC [String] (ChkConnectors Brat Chk Noun)
  | VBHole Name FC (ChkConnectors Brat Chk UVerb)
  | NKHole Name FC (ChkConnectors Kernel Chk Noun)
  | VKHole Name FC (ChkConnectors Kernel Chk UVerb)
 deriving Show

data EndType where
  EndType :: Modey m -> BinderType m -> EndType

instance Show EndType where
  show (EndType Kerny ty) = show ty
  show (EndType Braty (Left k)) = show k
  show (EndType Braty (Right ty)) = show ty

data Store = Store
  { typeMap  :: M.Map End EndType
  , valueMap :: M.Map End (Val Z)
  }

instance Show Store where
  show (Store km vm) = unlines $
                       ("Kinds:":(showKind <$> M.toList km))
                       ++ ("\nValues:":(showVal <$> M.toList vm))
   where
    showKind (key, kind) = show key ++ " :: " ++ show kind
    showVal (key, val) = show key ++ " = " ++ show val

initStore :: Store
initStore = Store M.empty M.empty

instance Semigroup Store where
  (Store ks vs) <> (Store ks' vs') = Store (ks <> ks') (vs <> vs')
