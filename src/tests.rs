use std::str::FromStr;

use crate::{Typing, RustIdent, AsciiIdent, nz, UniversalType, ExtensionType, Error};

type AsciiTy = Typing<AsciiIdent>;
type RustTy = Typing<RustIdent>;

#[test]
fn test_parsing() {
    let s = "";
    assert!(RustTy::from_str(s) == Err(Error::Empty));

    let s = "foöbár";
    assert!(RustTy::from_str(s) == Ok(RustTy::Named(s.to_owned())));
    assert!(AsciiTy::from_str(s) == Err(Error::ValidationFailed));

    let s = "int";
    assert!(RustTy::from_str(s) == Ok(RustTy::Common(UniversalType::ISize)));

    let s = "uint32";
    assert!(RustTy::from_str(s) == Ok(RustTy::Common(UniversalType::UInt(nz!(4)))));

    let s = "decimal";
    assert!(RustTy::from_str(s) == Ok(RustTy::Extension(ExtensionType::Decimal)));

    let s = "[]vec2";
    assert!(RustTy::from_str(s) == Ok(RustTy::Vec(RustTy::Named("vec2".to_owned()).boxed())));

    let s = "[42]?string";
    assert!(RustTy::from_str(s) == Ok(RustTy::Array(
        42,
        RustTy::Option(
            RustTy::Common(UniversalType::String).boxed()
        ).boxed()
    )));

    let s = "[[[datetime]]]";
    assert_eq!(RustTy::from_str(s), Ok(RustTy::Set(
        RustTy::Set(
            RustTy::Set(
                RustTy::Extension(ExtensionType::DateTime).boxed()
            ).boxed()
        ).boxed()
    )));

    let s = "[(Hello,World)]?(uint8,@smartstring)";
    assert_eq!(RustTy::from_str(s),
        Ok(RustTy::Map(
            RustTy::Tuple(vec![
                RustTy::Named("Hello".to_owned()),
                RustTy::Named("World".to_owned()),
            ]).boxed(),
            RustTy::Option(
                RustTy::Tuple(vec![
                    RustTy::Common(UniversalType::UInt(nz!(1))),
                    RustTy::Foreign(RustTy::Named("smartstring".to_owned()).boxed())
                ]).boxed())
            .boxed())
        )
    );

}
