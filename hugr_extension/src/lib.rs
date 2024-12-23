pub mod ctor;
pub mod defs;
pub mod ops;

use enum_iterator::all;
use hugr::{
    extension::{
        prelude::PRELUDE,
        simple_op::{MakeOpDef, MakeRegisteredOp},
        ExtensionId, ExtensionRegistry, ExtensionSet, Version,
        SignatureFromArgs,
    },
    std_extensions::{arithmetic::{float_ops, float_types, int_ops, int_types}, collections},
    Extension,
};

use lazy_static::lazy_static;

use crate::defs::BratOpDef;

/// Reported unique name of the Brat extension
pub const EXTENSION_ID: ExtensionId = ExtensionId::new_unchecked("BRAT");
pub const EXTENSION_VERSION: Version = Version::new(0, 0, 0);

lazy_static! {
    /// Extension for Brat operations.
    pub static ref EXTENSION: Extension = {
        let reqs = ExtensionSet::from_iter([int_types::EXTENSION_ID, collections::EXTENSION_ID]);

        let mut extension = Extension::new(EXTENSION_ID, EXTENSION_VERSION).with_reqs(reqs);

        for op in all::<BratOpDef>() {
            op.add_to_extension(&mut extension).unwrap();
        }

        extension
    };

    /// Registry of extensions required to validate Brat operations.
    pub static ref BRAT_OPS_REGISTRY: ExtensionRegistry  = ExtensionRegistry::try_new([
        collections::EXTENSION.to_owned(),
        int_ops::EXTENSION.to_owned(),
        int_types::EXTENSION.to_owned(),
        float_ops::EXTENSION.to_owned(),
        float_types::EXTENSION.to_owned(),
        PRELUDE.to_owned(),
        EXTENSION.to_owned(),
    ])
    .unwrap();
}

impl MakeRegisteredOp for BratOpDef {
    fn extension_id(&self) -> ExtensionId {
        EXTENSION_ID.to_owned()
    }

    fn registry<'s, 'r: 's>(&'s self) -> &'r ExtensionRegistry {
        &BRAT_OPS_REGISTRY
    }
}

#[cfg(test)]
mod test {
    use hugr::{
        extension::simple_op::MakeExtensionOp,
        ops::{custom::ExtensionOp, NamedOp},
        types::{Signature, type_param::TypeParam, Type, TypeArg},
    };

    use crate::{
        ctor::BratCtor,
        ops::BratOp,
    };

    use super::*;

    #[test]
    fn test_round_trip() {
        fn round_trip(op: &BratOp) -> BratOp {
            BratOp::from_extension_op(
                &ExtensionOp::new(
                    EXTENSION.get_op(&op.name()).unwrap().clone(),
                    op.type_args(),
                    &BRAT_OPS_REGISTRY,
                )
                .unwrap(),
            )
            .unwrap()
        }

        let sig1 = Signature::new(vec![Type::UNIT, Type::UNIT], vec![Type::UNIT]);
        let sig2 = Signature::new(vec![Type::UNIT], vec![Type::UNIT, Type::UNIT]);
        let sig3 = Signature::new_endo(vec![Type::UNIT]);

        let hole = BratOp::Hole {
            idx: 0,
            sig: sig1.clone(),
        };
        assert_eq!(round_trip(&hole), hole);

        let substitute = BratOp::Substitute {
            func_sig: sig1.clone(),
            hole_sigs: vec![sig1.clone(), sig2.clone(), sig3.clone()],
        };
        assert_eq!(round_trip(&substitute), substitute);

        let partial = BratOp::Partial {
            inputs: vec![Type::UNIT].into(),
            output_sig: sig1.clone(),
        };
        assert_eq!(round_trip(&partial), partial);

        let panic = BratOp::Panic { sig: sig1.clone() };
        assert_eq!(round_trip(&panic), panic);

        for ctor in all::<BratCtor>() {
            // Make dummy args for constructor params
            let args: Vec<TypeArg> = ctor
                .compute_signature(&[]).unwrap()
                .params()
                .iter()
                .map(|p| match p {
                    TypeParam::Type { .. } => TypeArg::Type { ty: Type::UNIT },
                    _ => panic!("Unexpected ctor parameter"),
                })
                .collect();

            let ctor_op = BratOp::Ctor {
                ctor,
                args: args.clone(),
            };
            assert_eq!(round_trip(&ctor_op), ctor_op);

            let prim_test = BratOp::PrimCtorTest { ctor, args };
            assert_eq!(round_trip(&prim_test), prim_test);
        }
    }
}

/*
#[cfg(test)]
mod test {
    use super::*;
    use hugr::std_extensions::arithmetic::{float_ops, float_types, int_ops, int_types};
    use hugr::std_extensions::{collections, logic};
    use hugr::extension::prelude::PRELUDE;
    use hugr::ops::custom::resolve_extension_ops;
    use hugr::Hugr;

    #[test]
    fn test_resolve_op() {
        let registry = ExtensionRegistry::try_new([
            PRELUDE.to_owned(),
            logic::EXTENSION.to_owned(),
            int_types::extension(),
            int_ops::EXTENSION.to_owned(),
            float_types::EXTENSION.to_owned(),
            float_ops::EXTENSION.to_owned(),
            collections::EXTENSION.to_owned(),
            super::EXTENSION.to_owned(),
        ])
        .unwrap();

        let opqaue = OpaqueOp::new(
            "BRAT",


        let hugr = Hugr::default();
        hugr.dfg

        resolve_extension_ops
    }
}
*/
