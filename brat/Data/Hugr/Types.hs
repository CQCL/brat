{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr.Types where

import Data.Aeson
import Data.Text (Text)

data UnitSum = UnitSum { size :: Int }
data GeneralSum = GeneralSum { row :: [HugrType] }

data SumType = SU UnitSum | SG GeneralSum

data HugrType
  = HTQubit
  | HTUSize
  | HTArray
  | HTTuple { inner :: [HugrType] }
  | HTSum SumType
  | HTOpaque

instance ToJSON HugrType where
  toJSON HTQubit = object ["t" .= ("Q" :: Text)]
  toJSON _ = error "todo"

data PolyFuncType = PolyFuncType
 { params :: [TypeParam]
 , body   :: FunctionType
 }

instance ToJSON PolyFuncType where
  toJSON (PolyFuncType params body) = object ["t" .= ("G" :: Text)
                                             ,"params" .= params
                                             ,"body" .= body
                                             ]

data TypeParam
instance ToJSON TypeParam where
  toJSON = undefined

data FunctionType = FunctionType
 { input :: [HugrType]
 , output :: [HugrType]
 }

instance ToJSON FunctionType where
  toJSON (FunctionType ins outs) = object ["input" .= ins
                                          ,"output" .= outs
                                          ,"extension_reqs" .= ([] :: [TypeParam])
                                          ]

data Array = Array
 { ty :: HugrType
 , len :: Int
 }
