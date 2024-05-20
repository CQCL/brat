{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr.Types where

import Data.Aeson
import Data.Text (Text, pack)

data UnitSum = UnitSum { size :: Int }
 deriving (Eq, Show)
data GeneralSum = GeneralSum { row :: [HugrType] }
 deriving (Eq, Show)

data SumType = SU UnitSum | SG GeneralSum
 deriving (Eq, Show)

newtype SumOfRows = SoR [[HugrType]] deriving Show

-- Convert from a hugr sum of tuples to a SumOfRows
sumOfRows :: HugrType -> SumOfRows
sumOfRows (HTSum (SG (GeneralSum rows))) = SoR (unpackTuple <$> rows)
 where
  unpackTuple :: HugrType -> [HugrType]
  unpackTuple (HTTuple row) = row
  unpackTuple _ = error "sumOfRows expects a sum of row tuples"
sumOfRows ty = error $ show ty ++ " isn't a sum of row tuples"

compileSumOfRows :: SumOfRows -> HugrType
compileSumOfRows (SoR rows) = HTSum (SG (GeneralSum (HTTuple <$> rows)))

data HugrType
  = HTQubit
  | HTUSize
  | HTArray
  | HTTuple [HugrType]
  | HTSum SumType
  | HTOpaque {-extension :: -}String {-type id :: -}String [TypeArg] TypeBound
  | HTFunc PolyFuncType
 deriving (Eq, Show)

instance ToJSON HugrType where
  toJSON HTQubit = object ["t" .= ("Q" :: Text)]
  toJSON (HTSum (SU (UnitSum size))) = object ["t" .= ("Sum" :: Text)
                                              ,"s" .= ("Unit" :: Text)
                                              ,"size" .= size
                                              ]
  toJSON (HTSum (SG (GeneralSum row))) = object ["t" .= ("Sum" :: Text)
                                                ,"s" .= ("General" :: Text)
                                                ,"row" .= row
                                                ]
  toJSON (HTTuple inner) = object ["t" .= ("Tuple" :: Text)
                                  ,"inner" .= inner
                                  ]
  toJSON HTUSize = object ["t" .= ("I" :: Text)]
  toJSON (HTOpaque ext id args bound) = object ["t" .= ("Opaque" :: Text)
                                               ,"extension" .= pack ext
                                               ,"id" .= pack id
                                               ,"args" .= args
                                               ,"bound" .= bound
                                               ]
  toJSON (HTFunc sig) = object ["t" .= ("G" :: Text)
                               ,"params" .= params sig
                               ,"body" .= body sig
                               ]
  toJSON ty = error $ "todo: json of " ++ show ty

data PolyFuncType = PolyFuncType
 { params :: [TypeParam]
 , body   :: FunctionType
 } deriving (Eq, Show)

instance ToJSON PolyFuncType where
  toJSON (PolyFuncType params body) = object ["t" .= ("G" :: Text)
                                             ,"params" .= params
                                             ,"body" .= body
                                             ]

data CustomTypeArg = CustomTypeArg
 { typ :: CustomType
 , value :: HugrValue
 } deriving (Eq, Show)

data HugrValue deriving (Eq, Show)
data CustomType deriving (Eq, Show)
data ExtensionId deriving (Eq, Show)
instance ToJSON ExtensionId where
  toJSON = undefined

data TypeBound = TBEq | TBCopy | TBAny deriving (Eq, Ord, Show)

instance ToJSON TypeBound where
  toJSON TBEq = "E"
  toJSON TBCopy = "C"
  toJSON TBAny = "A"

data TypeArgVariable = TypeArgVariable
 { idx :: Int
 , cached_decl :: TypeParam
 }
 deriving (Eq, Show)

data TypeArg
 = TAType HugrType
 | TANat Int
 | TAOpaque CustomTypeArg
 | TASequence [TypeArg]
 | TAVariable TypeArgVariable
 deriving (Eq, Show)

instance ToJSON TypeArg where
  toJSON (TAType ty) = object ["tya" .= ("Type" :: Text)
                              ,"ty" .= ty
                              ]
  toJSON (TANat n) = object ["tya" .= ("BoundedNat" :: Text)
                            ,"n" .= n
                            ]
  toJSON (TASequence args) = object ["tya" .= ("Sequence" :: Text)
                                    ,"elems" .= args
                                    ]

data TypeParam = TypeParam deriving (Eq, Show)
instance ToJSON TypeParam where
  toJSON = undefined

data FunctionType = FunctionType
 { input :: [HugrType]
 , output :: [HugrType]
 } deriving (Eq, Show)

instance ToJSON FunctionType where
  toJSON (FunctionType ins outs) = object ["input" .= ins
                                          ,"output" .= outs
                                          ,"extension_reqs" .= ([] :: [Text])
                                          ]

data Array = Array
 { ty :: HugrType
 , len :: Int
 } deriving Show

boundOf :: HugrType -> TypeBound
boundOf HTQubit = TBAny
boundOf (HTOpaque _ _ _ b) = b
boundOf HTUSize = TBEq
boundOf (HTTuple tys) = maximum (TBEq : (boundOf <$> tys))
boundOf (HTSum (SU _)) = TBEq
boundOf (HTSum (SG (GeneralSum rows))) = maximum (TBEq : (boundOf <$> rows))
boundOf (HTFunc _) = TBCopy
boundOf _ = error "unimplemented bound"

hugrList :: HugrType -> HugrType
hugrList ty = HTOpaque "Collections" "List" [TAType ty] (boundOf ty)

intWidth :: Int
intWidth = 6  -- 2^6 = 64 bits

hugrInt :: HugrType
hugrInt = HTOpaque "arithmetic.int.types" "int" [TANat intWidth] TBEq

hugrFloat :: HugrType
hugrFloat = HTOpaque "arithmetic.float.types" "float64" [] TBCopy
