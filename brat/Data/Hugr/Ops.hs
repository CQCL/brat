{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Hugr.Ops where

import Data.Aeson
import Data.Text (Text, pack)

import Data.Hugr.Types
import Brat.Syntax.Simple

data ModuleOp node = ModuleOp { parent :: node } deriving (Eq, Functor, Show)

instance Eq a => Ord (ModuleOp a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (ModuleOp node) where
  toJSON (ModuleOp parent) = object ["parent" .= parent
                                    ,"op" .= ("Module" :: Text)
                                    ]

data FuncDefn node = FuncDefn
 { parent :: node
 , name :: String
 , signature_ :: PolyFuncType
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (FuncDefn a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (FuncDefn node) where
  toJSON (FuncDefn { .. }) = object ["parent" .= parent
                                    ,"op" .= ("FuncDefn" :: Text)
                                    ,"name" .= name
                                    ,"signature" .= signature_
                                    ]

data HugrConst
  = HCInt Int
  | HCFloat Double
  | HCUnit
  | HCFunction (Hugr Int)
 deriving (Eq, Show)

instance ToJSON HugrConst where
  toJSON (HCInt x) = object ["v" .= ("Extension" :: Text)
                            ,"c" .= [object ["c" .= ("ConstIntS" :: Text)
                                            ,"log_width" .= (intWidth :: Int)
                                            ,"value" .= x
                                            ]
                                    ]
                            ]
  toJSON (HCFloat x) = object ["v" .= ("Extension" :: Text)
                              ,"c" .= [object ["c" .= ("ConstF64" :: Text)
                                              ,"value" .= x
                                              ]
                                      ]
                              ]
  toJSON HCUnit = object ["v" .= ("Tuple" :: Text)
                         ,"vs" .= ([] :: [()])
                         ]
  toJSON (HCFunction hugr) = object ["v" .= ("Function" :: Text)
                                    ,"hugr" .= hugr
                                    ]

constFromSimple :: SimpleTerm -> HugrConst
constFromSimple (Num x) = HCInt x
constFromSimple (Float x) = HCFloat x
constFromSimple (Text _) = error "todo"
constFromSimple Unit = HCUnit

data ConstOp node = ConstOp
 { parent :: node
 , const :: HugrConst
 , typ :: HugrType
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (ConstOp a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (ConstOp node) where
  toJSON (ConstOp {..}) = object ["parent" .= parent
                                 ,"op" .= ("Const" :: Text)
                                 ,"value" .= const
                                 ,"typ" .= typ
                                 ]



data InputNode node = InputNode
 { parent :: node
 , types  :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (InputNode a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (InputNode node) where
  toJSON (InputNode parent types) = object ["parent" .= parent
                                           ,"op" .= ("Input" :: Text)
                                           ,"types" .= types
                                           ]

data OutputNode node = OutputNode
 { parent :: node
 , types  :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (OutputNode a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (OutputNode node) where
  toJSON (OutputNode parent types) = object ["parent" .= parent
                                            ,"op" .= ("Output" :: Text)
                                            ,"types" .= types
                                            ]

data Conditional node = Conditional
 { parent :: node
 , tuple_sum_rows :: [[HugrType]]
 , other_inputs :: [HugrType]
 , outputs :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq a => Ord (Conditional a) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (Conditional node) where
  toJSON (Conditional { .. })
   = object ["op" .= ("Conditional" :: Text)
            ,"parent" .= parent
            ,"tuple_sum_rows" .= tuple_sum_rows
            ,"other_inputs" .= other_inputs
            ,"outputs" .= outputs
            ,"extension_delta" .= ([] :: [Text])
            ]

data Case node = Case
  { parent :: node
  , signature_ :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (Case node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (Case node) where
  toJSON (Case { .. }) = object ["op" .= ("Case" :: Text)
                                ,"parent" .= parent
                                ,"signature" .= signature_
                                ]

{-
data Const = Const
 { parent :: Int
 , value :: HugrValue
 , typ :: HugrType
 }
-}

data DFG node = DFG
 { parent :: node
 , signature_ :: FunctionType
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (DFG node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (DFG node) where
  toJSON (DFG { .. }) = object ["op" .= ("DFG" :: Text)
                               ,"parent" .= parent
                               ,"signature" .= signature_
                               ]

data TagOp node = TagOp
 { parent :: node
 , tag :: Int
 , variants :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (TagOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (TagOp node) where
  toJSON (TagOp parent tag variants)
   = object ["parent" .= parent
            ,"op" .= ("LeafOp" :: Text)
            ,"lop" .= ("Tag" :: Text)
            ,"tag" .= tag
            ,"variants" .= variants
            ]

data MakeTupleOp node = MakeTupleOp
 { parent :: node
 , tys :: [HugrType]
 } deriving (Eq, Functor, Show)

instance Eq node => Ord (MakeTupleOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (MakeTupleOp node) where
  toJSON (MakeTupleOp parent tys)
   = object ["parent" .= parent
            ,"op" .= ("LeafOp" :: Text)
            ,"lop" .= ("MakeTuple" :: Text)
            ,"tys" .= tys
            ]

data CustomOp node = CustomOp
  { parent :: node
  , extension :: String
  , op_name :: String
  , signature_ :: FunctionType
  , args :: [TypeArg]
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CustomOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CustomOp node) where
  toJSON (CustomOp { .. }) = object ["parent" .= parent
                                    ,"op" .= ("LeafOp" :: Text)
                                    ,"lop" .= ("CustomOp" :: Text)
                                    ,"description" .= ("" :: Text)
                                    ,"extension" .= pack extension
                                    ,"args" .= args
                                    ,"op_name" .= pack op_name
                                    ,"signature" .= signature_
                                    ]

data CallOp node = CallOp
  { parent :: node
  , signature_ :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CallOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CallOp node) where
  toJSON (CallOp parent signature_) = object ["parent" .= parent
                                             ,"signature" .= signature_
                                             ,"op" .= ("Call" :: Text)
                                             ]

intOp :: node -> String -> FunctionType -> [TypeArg] -> CustomOp node
intOp parent = CustomOp parent "arithmetic.int"

binaryIntOp :: node -> String -> CustomOp node
binaryIntOp parent name = intOp parent name (FunctionType [hugrInt, hugrInt] [hugrInt]) [TANat intWidth]

floatOp :: node -> String -> FunctionType -> [TypeArg] -> CustomOp node
floatOp parent = CustomOp parent "arithmetic.float"

binaryFloatOp :: node -> String -> CustomOp node
binaryFloatOp parent name = floatOp parent name (FunctionType [hugrFloat, hugrFloat] [hugrFloat]) []

data CallIndirectOp node = CallIndirectOp
  { parent :: node
  , signature_ :: FunctionType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (CallIndirectOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (CallIndirectOp node) where
  toJSON (CallIndirectOp parent signature_) = object ["parent" .= parent
                                                     ,"signature" .= signature_
                                                     ,"op" .= ("CallIndirect" :: Text)
                                                     ]

holeOp :: node -> Int -> FunctionType -> CustomOp node
holeOp parent idx sig = CustomOp parent "BRAT" "Hole" sig [TANat idx]

-- TYPE ARGS:
--  * A length-2 sequence comprising:
--    * A sequence of types (the inputs of outerSig)
--    * A sequence of types (the outputs of outerSig)
--  * A sequence of such length-2 sequences of the input and output types for each innerSig
-- INPUTS:
--  * A graph (of type outerSig)
--  * Many graphs with types given by innerSigs (to go in the holes)
-- OUTPUT:
--  * A single graph whose signature is the same as outerSig
substOp :: node
        -> {- outerSig :: -}FunctionType
        -> {- innerSigs :: -}[FunctionType]{- length n -}
        -> CustomOp node
substOp parent outerSig innerSigs
  = CustomOp parent "Brat" "Substitute" sig args
 where
  sig = FunctionType (toFunc <$> (outerSig : innerSigs)) [toFunc outerSig]
  args = [funcToSeq outerSig, TASequence (funcToSeq <$> innerSigs)]

  funcToSeq (FunctionType ins outs) = TASequence [toSeq ins, toSeq outs]

toFunc :: FunctionType -> HugrType
toFunc = HTFunc . PolyFuncType []

toSeq :: [HugrType] -> TypeArg
toSeq tys = TASequence (TAType <$> tys)

partialOp :: node  -- Parent
          -> FunctionType  -- Signature of the function that is partially evaluated
          -> Int  -- Number of arguments that are evaluated
          -> CustomOp node
partialOp parent funcSig numSupplied = CustomOp parent "Brat" "Partial" sig args
 where
  sig = FunctionType (toFunc funcSig : partialInputs) [toFunc $ FunctionType otherInputs (output funcSig)]
  args = [toSeq partialInputs, toSeq otherInputs, toSeq (output funcSig)]

  partialInputs = take numSupplied (input funcSig)
  otherInputs = drop numSupplied (input funcSig)


data LoadConstantOp node = LoadConstantOp
  { parent :: node
  , datatype :: HugrType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (LoadConstantOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (LoadConstantOp node) where
  toJSON (LoadConstantOp {..}) = object ["parent" .= parent
                                        ,"op" .= ("LoadConstant" :: Text)
                                        ,"datatype" .= datatype
                                        ,"op" .= ("LoadConstant" :: Text)
                                        ]

data NoopOp node = NoopOp
  { parent :: node
  , ty :: HugrType
  } deriving (Eq, Functor, Show)

instance Eq node => Ord (NoopOp node) where
  compare _ _ = EQ

instance ToJSON node => ToJSON (NoopOp node) where
  toJSON (NoopOp {..}) = object ["parent" .= parent
                                ,"op" .= ("LeafOp" :: Text)
                                ,"lop" .= ("Noop" :: Text)
                                ,"ty" .= ty
                                ]

-- In the order they must be printed in - roots, inputs, outputs
data HugrOp node
  -- OpConditional should be compiled last so we can sort out its parent
  = OpMod (ModuleOp node)
  | OpIn (InputNode node)
  | OpOut (OutputNode node)
  -- the rest
  | OpDefn (FuncDefn node)
  | OpDFG (DFG node)
  | OpConst (ConstOp node)
  | OpConditional (Conditional node)
  -- Make sure that the cases are printed out in the correct order
  | OpCase (Int, Case node)
  | OpTag (TagOp node)
  | OpMakeTuple (MakeTupleOp node)
  | OpCustom (CustomOp node)
  | OpCall (CallOp node)
  | OpCallIndirect (CallIndirectOp node)
  | OpLoadConstant (LoadConstantOp node)
  | OpNoop (NoopOp node)
 deriving (Eq, Functor, Ord, Show)

instance ToJSON node => ToJSON (HugrOp node) where
  toJSON (OpMod op) = toJSON op
  toJSON (OpDefn op) = toJSON op
  toJSON (OpConst op) = toJSON op
  toJSON (OpDFG op) = toJSON op
  toJSON (OpIn op) = toJSON op
  toJSON (OpOut op) = toJSON op
  toJSON (OpCase (_, op)) = toJSON op
  toJSON (OpConditional op) = toJSON op
  toJSON (OpTag op) = toJSON op
  toJSON (OpMakeTuple op) = toJSON op
  toJSON (OpCustom op) = toJSON op
  toJSON (OpCall op) = toJSON op
  toJSON (OpCallIndirect op) = toJSON op
  toJSON (OpLoadConstant op) = toJSON op
  toJSON (OpNoop op) = toJSON op

getParent :: HugrOp node -> node
getParent (OpMod (ModuleOp { parent = parent })) = parent
getParent (OpDefn (FuncDefn { parent = parent })) = parent
getParent (OpConst (ConstOp { parent = parent })) = parent
getParent (OpDFG (DFG { parent = parent })) = parent
getParent (OpConditional (Conditional { parent = parent })) = parent
getParent (OpCase (_, (Case { parent = parent }))) = parent
getParent (OpIn (InputNode { parent = parent })) = parent
getParent (OpOut (OutputNode { parent = parent })) = parent
getParent (OpTag (TagOp { parent = parent })) = parent
getParent (OpMakeTuple (MakeTupleOp { parent = parent })) = parent
getParent (OpCustom (CustomOp { parent = parent })) = parent
getParent (OpCall (CallOp { parent = parent })) = parent
getParent (OpCallIndirect (CallIndirectOp { parent = parent })) = parent
getParent (OpLoadConstant (LoadConstantOp { parent = parent })) = parent
getParent (OpNoop (NoopOp { parent = parent })) = parent

data Hugr node = Hugr [HugrOp node] [(PortId node, PortId node)]
  deriving (Eq, Functor, Show)

instance ToJSON node => ToJSON (Hugr node) where
  toJSON (Hugr ns es) = object ["version" .= ("v0" :: Text)
                               ,"nodes" .= ns
                               ,"edges" .= es
                               ]

orderEdgeOffset :: Int
orderEdgeOffset = -1

data PortId node = Port
  { nodeId :: node
  , offset :: Int
  }
 deriving (Eq, Functor, Show)

instance ToJSON node => ToJSON (PortId node) where
  toJSON (Port node offset) = toJSON (node, offset')
    where offset' = if offset == orderEdgeOffset then Nothing else Just offset
