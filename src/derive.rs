use std::collections::{HashMap, BTreeMap, HashSet, BTreeSet};

use crate::{RustIdent, Typing, UniversalType};

#[doc(hidden)]
#[macro_export]
macro_rules! nz {
    ($i: literal) => {
        match ::core::num::NonZeroUsize::new($i) {
            Some(x) => x,
            None => unreachable!(),
        }
    };
}

macro_rules! impl_common {
    ($ty: ty, $branch: ident) => {
        impl ToTypeProtocol for $ty {
            fn type_protocol() -> Typing<RustIdent> {
                Typing::Common(UniversalType::$branch)
            }
        }
    };
    ($ty: ty, $branch: ident, $len: literal) => {
        impl ToTypeProtocol for $ty {
            fn type_protocol() -> Typing<RustIdent> {
                Typing::Common(UniversalType::$branch(nz!($len)))
            }
        }
    };
}

pub trait ToTypeProtocol {
    fn type_protocol() -> Typing<RustIdent>;
}

impl_common!(bool, Bool);
impl_common!(u8, UInt, 1);
impl_common!(u16, UInt, 2);
impl_common!(u32, UInt, 4);
impl_common!(u64, UInt, 8);
impl_common!(u128, UInt, 16);
impl_common!(i8, Int, 1);
impl_common!(i16, Int, 2);
impl_common!(i32, Int, 4);
impl_common!(i64, Int, 8);
impl_common!(i128, Int, 16);
impl_common!(f32, Float, 4);
impl_common!(f64, Float, 8);
impl_common!(usize, USize);
impl_common!(isize, ISize);
impl_common!(char, Char);
impl_common!(String, String);

impl<T: ToTypeProtocol> ToTypeProtocol for Option<T> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Option(T::type_protocol().boxed())
    }
}

impl<T: ToTypeProtocol, const N: usize> ToTypeProtocol for [T; N] {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Array(N, T::type_protocol().boxed())
    }
}

impl<T: ToTypeProtocol> ToTypeProtocol for Vec<T> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Vec(T::type_protocol().boxed())
    }
}

impl<T: ToTypeProtocol> ToTypeProtocol for HashSet<T> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Set(T::type_protocol().boxed())
    }
}

impl<T: ToTypeProtocol> ToTypeProtocol for BTreeSet<T> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Set(T::type_protocol().boxed())
    }
}

impl<A: ToTypeProtocol, B: ToTypeProtocol> ToTypeProtocol for HashMap<A, B> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Map(A::type_protocol().boxed(), B::type_protocol().boxed())
    }
}

impl<A: ToTypeProtocol, B: ToTypeProtocol> ToTypeProtocol for BTreeMap<A, B> {
    fn type_protocol() -> Typing<RustIdent> {
        Typing::Map(A::type_protocol().boxed(), B::type_protocol().boxed())
    }
}
