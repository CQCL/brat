use std::str::FromStr;

use crate::ctor::BratCtor;
use enum_iterator::Sequence;
use hugr::{
    extension::{
        simple_op::{MakeOpDef, OpLoadError},
        OpDef, SignatureError, SignatureFromArgs, SignatureFunc,
    },
    ops::OpName,
    std_extensions::arithmetic::int_types::INT_TYPES,
    types::{type_param::TypeParam, FunctionType, PolyFuncType, Type, TypeArg, TypeBound},
};

use lazy_static::lazy_static;

use smol_str::{format_smolstr, SmolStr};
use strum::ParseError;

use crate::ctor::Ctor;

lazy_static! {
    static ref U64: Type = INT_TYPES[6].clone();
}

/// Brat extension operation definitions.
#[derive(Clone, Copy, Debug, Hash, Sequence, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum BratOpDef {
    Hole,
    Substitute,
    Partial,
    Panic,
    Ctor(BratCtor),
    PrimCtorTest(BratCtor),
    Lluf,
}

impl OpName for BratOpDef {
    fn name(&self) -> SmolStr {
        use BratOpDef::*;
        match self {
            Hole => "Hole".into(),
            Substitute => "Substitute".into(),
            Partial => "Partial".into(),
            Panic => "Panic".into(),
            Ctor(ctor) => format_smolstr!("Ctor::{}", ctor.name()),
            PrimCtorTest(ctor) => format_smolstr!("PrimCtorTest::{}", ctor.name()),
            Lluf => "Lluf".into()
        }
    }
}

impl FromStr for BratOpDef {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v: Vec<_> = s.splitn(2, "::").collect();
        match v.as_slice() {
            ["Hole"] => Ok(BratOpDef::Hole),
            ["Substitute"] => Ok(BratOpDef::Substitute),
            ["Partial"] => Ok(BratOpDef::Partial),
            ["Panic"] => Ok(BratOpDef::Panic),
            ["Ctor", ctor] => Ok(BratOpDef::Ctor(BratCtor::from_str(ctor)?)),
            ["PrimCtorTest", ctor] => Ok(BratOpDef::PrimCtorTest(BratCtor::from_str(ctor)?)),
            ["Lluf"] => Ok(BratOpDef::Lluf),
            _ => Err(ParseError::VariantNotFound),
        }
    }
}

impl MakeOpDef for BratOpDef {
    fn from_def(op_def: &OpDef) -> Result<Self, OpLoadError> {
        hugr::extension::simple_op::try_from_name(op_def.name())
    }

    fn signature(&self) -> SignatureFunc {
        use BratOpDef::*;
        match self {
            Hole => SignatureFunc::CustomFunc(Box::new(HoleSigFun())),
            Substitute => SignatureFunc::CustomFunc(Box::new(SubstituteSigFun())),
            Partial => SignatureFunc::CustomFunc(Box::new(PartialSigFun())),
            Panic => SignatureFunc::CustomFunc(Box::new(PanicSigFun())),
            Ctor(ctor) => ctor.signature().into(),
            PrimCtorTest(ctor) => {
                let sig = ctor.signature();
                let input = sig.body().output(); // Ctor output is input for the test
                let output = Type::new_tuple_sum(vec![input.clone(), sig.body().input().clone()]);
                PolyFuncType::new(sig.params(), FunctionType::new(input.clone(), vec![output]))
                    .into()
            },
            Lluf => FunctionType::new(vec![U64.clone()], vec![U64.clone()]).into()
        }
    }
}

/// Binary compute_signature function for the `Hole` op
struct HoleSigFun();
impl SignatureFromArgs for HoleSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncType, SignatureError> {
        // The Hole op expects a nat identifier and two type sequences specifiying
        // the signature of the hole
        match arg_values {
            [TypeArg::BoundedNat { n: _ }, input, output] => {
                Ok(FunctionType::new(row_from_arg(input)?, row_from_arg(output)?).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 3] =
                [TypeParam::max_nat(), list_of_type(), list_of_type()];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Substitute` op
struct SubstituteSigFun();
impl SignatureFromArgs for SubstituteSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncType, SignatureError> {
        // The Substitute op expects a function signature and a list of hole signatures
        match arg_values {
            [fun_sig, TypeArg::Sequence { elems: hole_sigs }] => {
                let fun_ty = Type::new_function(sig_from_arg(fun_sig)?);
                let mut inputs = vec![fun_ty.clone()];
                for sig in hole_sigs {
                    inputs.push(Type::new_function(sig_from_arg(sig)?))
                }
                Ok(FunctionType::new(inputs, vec![fun_ty]).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] = [
                tuple_of_list_of_type(),
                TypeParam::List {
                    param: Box::new(tuple_of_list_of_type())
                },
            ];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Partial` op
struct PartialSigFun();
impl SignatureFromArgs for PartialSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncType, SignatureError> {
        // The Partial op expects a type sequence specifying the supplied partial inputs, a type
        // sequence specifiying the remaining inputs and a type sequence for the function outputs.
        match arg_values {
            [partial_inputs, other_inputs, outputs] => {
                let partial_inputs = row_from_arg(partial_inputs)?;
                let other_inputs = row_from_arg(other_inputs)?;
                let outputs = row_from_arg(outputs)?;
                let res_func =
                    Type::new_function(FunctionType::new(other_inputs.clone(), outputs.clone()));
                let mut inputs = vec![Type::new_function(FunctionType::new(
                    [partial_inputs.clone(), other_inputs].concat(),
                    outputs,
                ))];
                inputs.extend(partial_inputs);
                Ok(FunctionType::new(inputs, vec![res_func]).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 3] = [list_of_type(), list_of_type(), list_of_type()];
        }
        PARAMS.as_slice()
    }
}

/// Binary compute_signature function for the `Panic` op
struct PanicSigFun();
impl SignatureFromArgs for PanicSigFun {
    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncType, SignatureError> {
        // The Panic op expects two type sequences specifiying the signature of the op
        match arg_values {
            [input, output] => {
                Ok(FunctionType::new(row_from_arg(input)?, row_from_arg(output)?).into())
            }
            _ => Err(SignatureError::InvalidTypeArgs),
        }
    }

    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] = [
                TypeParam::List {
                    param: Box::new(TypeParam::Type { b: TypeBound::Any })
                },
                TypeParam::List {
                    param: Box::new(TypeParam::Type { b: TypeBound::Any })
                },
            ];
        }
        PARAMS.as_slice()
    }
}

fn row_from_arg(arg: &TypeArg) -> Result<Vec<Type>, SignatureError> {
    match arg {
        TypeArg::Sequence { elems } => elems
            .iter()
            .map(|arg| match arg {
                TypeArg::Type { ty } => Ok(ty.clone()),
                _ => Err(SignatureError::InvalidTypeArgs),
            })
            .collect(),
        _ => Err(SignatureError::InvalidTypeArgs),
    }
}

fn sig_from_arg(arg: &TypeArg) -> Result<FunctionType, SignatureError> {
    match arg {
        TypeArg::Sequence { elems } if elems.len() == 2 => Ok(FunctionType::new(
            row_from_arg(&elems[0])?,
            row_from_arg(&elems[1])?,
        )),
        _ => Err(SignatureError::InvalidTypeArgs),
    }
}

fn list_of_type() -> TypeParam {
    TypeParam::List {
        param: Box::new(TypeParam::Type { b: TypeBound::Any }),
    }
}

fn tuple_of_list_of_type() -> TypeParam {
    TypeParam::Tuple {
        params: vec![list_of_type(), list_of_type()],
    }
}
