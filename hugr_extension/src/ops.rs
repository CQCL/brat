use hugr::{
    extension::{
        simple_op::{MakeExtensionOp, MakeOpDef, OpLoadError},
        SignatureError,
    },
    ops::{custom::ExtensionOp, OpName, OpTrait},
    types::{FunctionType, TypeArg, TypeEnum, TypeRow},
};
use smol_str::{format_smolstr, SmolStr};

use crate::{ctor::BratCtor, defs::BratOpDef};

/// Brat extension ops.
#[derive(Clone, Debug, PartialEq)]
#[allow(missing_docs)]
pub enum BratOp {
    Hole {
        idx: u64,
        sig: FunctionType,
    },
    Substitute {
        func_sig: FunctionType,
        hole_sigs: Vec<FunctionType>,
    },
    Partial {
        inputs: TypeRow,
        output_sig: FunctionType,
    },
    Panic {
        sig: FunctionType,
    },
    Ctor {
        ctor: BratCtor,
        args: Vec<TypeArg>,
    },
    PrimCtorTest {
        ctor: BratCtor,
        args: Vec<TypeArg>,
    },
}

impl OpName for BratOp {
    fn name(&self) -> SmolStr {
        use BratOp::*;
        match self {
            Hole { .. } => "Hole".into(),
            Substitute { .. } => "Substitute".into(),
            Partial { .. } => "Partial".into(),
            Panic { .. } => "Panic".into(),
            Ctor { ctor, .. } => format_smolstr!("Ctor::{}", ctor.name()),
            PrimCtorTest { ctor, .. } => format_smolstr!("PrimCtorTest::{}", ctor.name()),
        }
    }
}

impl MakeExtensionOp for BratOp {
    fn from_extension_op(ext_op: &ExtensionOp) -> Result<Self, OpLoadError> {
        let def = BratOpDef::from_def(ext_op.def())?;
        let sig = ext_op
            .dataflow_signature()
            .ok_or(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs))?;
        match def {
            BratOpDef::Hole => match *ext_op.args() {
                [TypeArg::BoundedNat { n: idx }, ..] => Ok(BratOp::Hole { idx, sig }),
                _ => Err(SignatureError::InvalidTypeArgs.into()),
            },
            BratOpDef::Substitute => match sig.input().as_ref() {
                [func_sig, hole_sigs @ ..] => {
                    let TypeEnum::Function(func_sig) = func_sig.as_type_enum() else {
                        return Err(SignatureError::InvalidTypeArgs.into());
                    };
                    let hole_sigs: Result<Vec<_>, OpLoadError> = hole_sigs
                        .iter()
                        .map(|ty| match ty.as_type_enum() {
                            TypeEnum::Function(f) => Ok(f.body().clone()),
                            _ => Err(SignatureError::InvalidTypeArgs.into()),
                        })
                        .collect();
                    Ok(BratOp::Substitute {
                        func_sig: func_sig.body().clone(),
                        hole_sigs: hole_sigs?,
                    })
                }
                _ => Err(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs)),
            },
            BratOpDef::Partial => match (sig.input().as_ref(), sig.output().as_ref()) {
                ([_, partial_inputs @ ..], [output_sig]) => {
                    let TypeEnum::Function(output_sig) = output_sig.as_type_enum() else {
                        return Err(SignatureError::InvalidTypeArgs.into());
                    };
                    Ok(BratOp::Partial {
                        inputs: partial_inputs.to_vec().into(),
                        output_sig: output_sig.body().clone(),
                    })
                }
                _ => Err(OpLoadError::InvalidArgs(SignatureError::InvalidTypeArgs)),
            },
            BratOpDef::Panic => Ok(BratOp::Panic { sig }),
            BratOpDef::Ctor(ctor) => Ok(BratOp::Ctor {
                ctor,
                args: ext_op.args().to_vec(),
            }),
            BratOpDef::PrimCtorTest(ctor) => Ok(BratOp::PrimCtorTest {
                ctor,
                args: ext_op.args().to_vec(),
            }),
        }
    }

    fn type_args(&self) -> Vec<TypeArg> {
        match self {
            BratOp::Hole { idx, sig } => vec![
                TypeArg::BoundedNat { n: *idx },
                arg_from_row(sig.input()),
                arg_from_row(sig.output()),
            ],
            BratOp::Substitute {
                func_sig,
                hole_sigs,
            } => vec![
                TypeArg::Sequence {
                    elems: vec![
                        arg_from_row(func_sig.input()),
                        arg_from_row(func_sig.output()),
                    ],
                },
                TypeArg::Sequence {
                    elems: hole_sigs
                        .iter()
                        .map(|sig| TypeArg::Sequence {
                            elems: vec![arg_from_row(sig.input()), arg_from_row(sig.output())],
                        })
                        .collect(),
                },
            ],
            BratOp::Partial { inputs, output_sig } => vec![
                arg_from_row(inputs),
                arg_from_row(output_sig.input()),
                arg_from_row(output_sig.output()),
            ],
            BratOp::Panic { sig } => vec![arg_from_row(sig.input()), arg_from_row(sig.output())],
            BratOp::Ctor { args, .. } => args.clone(),
            BratOp::PrimCtorTest { args, .. } => args.clone(),
        }
    }
}

fn arg_from_row(row: &TypeRow) -> TypeArg {
    TypeArg::Sequence {
        elems: row
            .iter()
            .map(|ty| TypeArg::Type { ty: ty.clone() })
            .collect(),
    }
}
