{-# LANGUAGE DeriveGeneric, DuplicateRecordFields #-}

-- Data structures corresponding to those in hugr, for compilation
module Data.Hugr where

import GHC.Generics ()
-- import Data.Aeson ()

-- The discriminator that's used to refer to a given hugr "thing"
-- in the serialised format
{-
class Tag t where
  tag :: String

data ExtensionVal

data HugrValue
  = {-HVExtension ExtensionVal
  | -}HVFunction FunctionType
--  | HVTuple HugrTuple
--  | HVSum HugrSum
-}
