use enum_iterator::Sequence;
use hugr::{
    extension::{SignatureError::{self, InvalidTypeArgs}, SignatureFromArgs},
    ops::NamedOp,
    std_extensions::{arithmetic::int_types, collections},
    types::{type_param::TypeParam, CustomType, FuncValueType, PolyFuncType, PolyFuncTypeRV, Signature, SumType, Type, TypeArg, TypeBound, TypeEnum, TypeRV},
};
use lazy_static::lazy_static;
use smol_str::{format_smolstr, SmolStr};
use std::str::FromStr;
use strum::ParseError;
use strum_macros::{EnumString, IntoStaticStr};

#[derive(Clone, Copy, Debug, Hash, Sequence, PartialEq, Eq)]
pub enum BratCtor {
    Nat(NatCtor),
    Vec(VecCtor),
    Tup(TupleCtor),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Sequence, IntoStaticStr, EnumString)]
#[allow(non_camel_case_types)]
pub enum NatCtor {
    zero,
    succ,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Sequence, IntoStaticStr, EnumString)]
#[allow(non_camel_case_types)]
pub enum VecCtor {
    nil,
    cons,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Sequence, IntoStaticStr, EnumString)]
#[allow(non_camel_case_types)]
pub enum TupleCtor {
    nil,
    cons,
}

impl NamedOp for BratCtor {
    fn name(&self) -> SmolStr {
        match self {
            BratCtor::Nat(ctor) => format_smolstr!("Nat::{}", ctor.name()),
            BratCtor::Vec(ctor) => format_smolstr!("Vec::{}", ctor.name()),
            BratCtor::Tup(ctor) => format_smolstr!("cons::{}", ctor.name()),
        }
    }
}

impl FromStr for BratCtor {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let v: Vec<_> = s.split("::").collect();
        match v.as_slice() {
            ["Nat", ctor] => Ok(BratCtor::Nat(NatCtor::from_str(ctor)?)),
            ["Vec", ctor] => Ok(BratCtor::Vec(VecCtor::from_str(ctor)?)),
            ["List", ctor] => Ok(BratCtor::Vec(VecCtor::from_str(ctor)?)),
            ["cons", ctor] => Ok(BratCtor::Tup(TupleCtor::from_str(ctor)?)),
            _ => Err(ParseError::VariantNotFound),
        }
    }
}

// BRAT constructors should take as type args a list of the types of their inputs
// and a list of the types of their outputs.
impl SignatureFromArgs for BratCtor {
    fn static_params(&self) -> &[TypeParam] {
        lazy_static! {
            static ref PARAMS: [TypeParam; 2] =
                [TypeParam::List { param: Box::new(TypeParam::Type { b: TypeBound::Any }) },
                 TypeParam::Type { b: TypeBound::Any },
                ];
        }
        PARAMS.as_slice()
    }

    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        let [TypeArg::Sequence { elems: ctor_arg_tyargs }, TypeArg::Type { ty: out_ty }] = arg_values else {
            return Err(InvalidTypeArgs)
        };
        let Some(ctor_arg_tys): Option<Vec<TypeRV>> = ctor_arg_tyargs.into_iter().map(move |a| match a {
            TypeArg::Type { ty } => Some(ty.clone().into()),
            _ => None,
        }).collect() else {
            return Err(InvalidTypeArgs);
        };

        let out_tys: Vec<TypeRV> = vec![out_ty.clone().into()];

        Ok(PolyFuncTypeRV::new([], FuncValueType::new(ctor_arg_tys, out_tys)))
/*
        match self {
            BratCtor::Nat(ctor) => ctor.compute_signature().map(|a| a.into()),
            BratCtor::Vec(ctor) => ctor.compute_signature(ctor_arg_tys, out_ty).map(|a| a.into()),
            BratCtor::Tup(ctor) => ctor.compute_signature(ctor_arg_tys, out_ty).map(|a| a.into()),
        }
*/
    }
}

pub(crate) struct CtorTest(pub BratCtor);

impl SignatureFromArgs for CtorTest {
    fn static_params(&self) -> &[TypeParam] {
        self.0.static_params()
    }

    fn compute_signature(&self, arg_values: &[TypeArg]) -> Result<PolyFuncTypeRV, SignatureError> {
        let sig = self.0.compute_signature(arg_values)?;
        let input = sig.body().output.clone();
        let output = sig.body().input.clone();
        Ok(PolyFuncTypeRV::new(sig.params(), FuncValueType::new(input, output)))
    }
}

impl From<NatCtor> for BratCtor {
    fn from(val: NatCtor) -> Self {
        BratCtor::Nat(val)
    }
}

impl From<VecCtor> for BratCtor {
    fn from(val: VecCtor) -> Self {
        BratCtor::Vec(val)
    }
}

impl From<TupleCtor> for BratCtor {
    fn from(val: TupleCtor) -> Self {
        BratCtor::Tup(val)
    }
}

/*
impl NatCtor {
    fn compute_signature(&self) -> Result<PolyFuncType, SignatureError> {
        match self {
            NatCtor::zero => Ok(Signature::new(vec![], vec![nat_type()]).into()),
            NatCtor::succ => Ok(Signature::new(vec![nat_type()], vec![nat_type()]).into()),
        }
    }
}

impl VecCtor {
    fn compute_signature(&self, ctor_arg_tys: &[Type], out_ty: &Type) -> Result<PolyFuncType, SignatureError> {
        match self {
            VecCtor::nil => {
                Ok(Signature::new(vec![], vec![list_type(&elem_ty)]).into())
            },
            VecCtor::cons =>
                Ok(Signature::new(vec![elem_ty.clone(), list_type(&elem_ty)], vec![list_type(&elem_ty)]).into()),
        }
    }
}

impl TupleCtor {
    fn compute_signature(self, arg_values: &[TypeArg]) -> Result<PolyFuncType, SignatureError> {
        todo!();
/*
        let tpl = TypeParam::Type { b: TypeBound::Any };
        let tpr = TypeParam::Type { b: TypeBound::Any };
        match self {
            TupleCtor::nil => {
                PolyFuncType::new(vec![],
                                  Signature::new(vec![], vec![SumType::new([])])
                )
            },
/*
            TupleCtor::cons => {
                PolyFuncType::new(vec![head, tail],
                                  Signature::new(vec![head, tail], vec![])
                )
            },
*/
        };
        todo!()
*/
    }
}
*/

/// The Hugr representation of Brat nats.
fn nat_type() -> Type {
    const WIDTH: u64 = 6; // 2^6 = 64 bits
    Type::new_extension(CustomType::new(
        int_types::INT_TYPE_ID,
        [TypeArg::BoundedNat { n: WIDTH }],
        int_types::EXTENSION_ID,
        TypeBound::Copyable,
    ))
}

/// The Hugr representation of Brat vectors.
fn list_type(elem: &Type) -> Type {
    Type::new_extension(CustomType::new(
        collections::LIST_TYPENAME,
        [TypeArg::Type { ty: elem.clone() }],
        collections::EXTENSION_ID,
        elem.least_upper_bound(),
    ))
}

#[cfg(test)]
mod test {

    use super::*;
    use hugr::extension::prelude::USIZE_T;

    #[test]
    fn is_list_type() {
        let act = collections::list_type(USIZE_T);

        let TypeEnum::Extension(custom) = act.as_type_enum() else {
            panic!("pee");
        };

        assert_eq!(*custom.name(), collections::LIST_TYPENAME);
        assert_eq!(*custom.extension(), collections::EXTENSION_ID);
    }
}
