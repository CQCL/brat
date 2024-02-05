{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr.Ops where

import Data.Aeson
import Data.Text (Text)

import Data.Hugr.Types

data FuncDefn = FuncDefn
 { parent :: Int
 , name :: String
 , signature_ :: PolyFuncType
 }

instance ToJSON FuncDefn where
  toJSON (FuncDefn { .. }) = object ["parent" .= parent
                                    ,"op" .= ("FuncDefn" :: Text)
                                    ,"name" .= name
                                    ,"signature" .= signature_
                                    ]

data InputNode = InputNode
 { parent :: Int
 , types  :: [HugrType]
 }

instance ToJSON InputNode where
  toJSON (InputNode parent types) = object ["parent" .= parent
                                           ,"op" .= ("Input" :: Text)
                                           ,"types" .= types
                                           ]

data OutputNode = OutputNode
 { parent :: Int
 , types  :: [HugrType]
 }

instance ToJSON OutputNode where
  toJSON (OutputNode parent types) = object ["parent" .= parent
                                            ,"op" .= ("Output" :: Text)
                                            ,"types" .= types
                                            ]

data Conditional = Conditional
 { parent :: Int
 , tuple_sum_rows :: [[HugrType]]
 , other_inputs :: [HugrType]
 }

{-
data Const = Const
 { parent :: Int
 , value :: HugrValue
 , typ :: HugrType
 }
-}

data DFG = DFG
 { parent :: Int
 , signature_ :: FunctionType
 }

data CallOp = CallOp
  { parent :: Int
  , signature_ :: FunctionType
  }

-- data Op
--  = Call {
