use enum_iterator::Sequence;
use hugr::{
    ops::NamedOp,
    std_extensions::{arithmetic::int_types, collections},
    types::{
        type_param::TypeParam, CustomType, PolyFuncType, Signature, Type, TypeArg,
        TypeBound,
    },
};
use smol_str::{format_smolstr, SmolStr};
use std::str::FromStr;
use strum::ParseError;
use strum_macros::{EnumString, IntoStaticStr};

#[derive(Clone, Copy, Debug, Hash, Sequence, PartialEq, Eq)]
pub enum BratCtor {
    Nat(NatCtor),
    Vec(VecCtor),
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

impl NamedOp for BratCtor {
    fn name(&self) -> SmolStr {
        match self {
            BratCtor::Nat(ctor) => format_smolstr!("Nat::{}", ctor.name()),
            BratCtor::Vec(ctor) => format_smolstr!("Vec::{}", ctor.name()),
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
            _ => Err(ParseError::VariantNotFound),
        }
    }
}

pub trait Ctor: Into<BratCtor> {
    /// The signature of the constructor
    fn signature(self) -> PolyFuncType;
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

impl Ctor for BratCtor {
    fn signature(self) -> PolyFuncType {
        match self {
            BratCtor::Nat(ctor) => ctor.signature(),
            BratCtor::Vec(ctor) => ctor.signature(),
        }
    }
}

impl Ctor for NatCtor {
    fn signature(self) -> PolyFuncType {
        match self {
            NatCtor::zero => Signature::new(vec![], vec![nat_type()]).into(),
            NatCtor::succ => Signature::new(vec![nat_type()], vec![nat_type()]).into(),
        }
    }
}

impl Ctor for VecCtor {
    fn signature(self) -> PolyFuncType {
        let tp = TypeParam::Type { b: TypeBound::Any };
        let ta = Type::new_var_use(0, TypeBound::Any);
        match self {
            VecCtor::nil => {
                PolyFuncType::new(vec![tp], Signature::new(vec![], vec![vec_type(&ta)]))
            }
            VecCtor::cons => PolyFuncType::new(
                vec![tp],
                Signature::new(vec![ta.clone(), vec_type(&ta)], vec![vec_type(&ta)]),
            ),
        }
    }
}

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
fn vec_type(elem: &Type) -> Type {
    Type::new_extension(CustomType::new(
        collections::LIST_TYPENAME,
        [TypeArg::Type { ty: elem.clone() }],
        collections::EXTENSION_NAME,
        elem.least_upper_bound(),
    ))
}
