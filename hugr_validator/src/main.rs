use brat_extension;
use hugr::extension::{ExtensionRegistry, PRELUDE};
use hugr::ops::custom::resolve_extension_ops;
use hugr::std_extensions::arithmetic::{float_ops, float_types, int_ops, int_types};
use hugr::std_extensions::{collections, logic};
use hugr::{hugr::ValidationError, Hugr};
use serde_json;
use std::io::{stdin, Read};
use std::process::exit;

fn parse_and_validate() -> Result<(), ValidationError> {
    let mut buffer = String::new();
    let mut stdin = stdin();
    stdin.read_to_string(&mut buffer).unwrap();
    let mut hugr: Hugr = serde_json::from_str(&buffer).unwrap();

    let registry = ExtensionRegistry::try_new([
        PRELUDE.to_owned(),
        logic::EXTENSION.to_owned(),
        int_types::extension(),
        int_ops::EXTENSION.to_owned(),
        float_types::EXTENSION.to_owned(),
        float_ops::EXTENSION.to_owned(),
        collections::EXTENSION.to_owned(),
        brat_extension::EXTENSION.to_owned(),
    ])
    .unwrap();

    resolve_extension_ops(&mut hugr, &registry)?;
    hugr.validate(&registry)?;
    println!("hugr parsed & validated successfully!");
    Ok(())
}

fn main() {
    match parse_and_validate() {
        Ok(()) => (),
        Err(err) => {
            println!("{}", err);
            exit(1);
        }
    }
}
