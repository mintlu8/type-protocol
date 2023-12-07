//! A crate providing a simple syntax inspired by the go programming language
//! for conveying types.
//!
//! # Universal Types
//!
//! These are common datatypes found in most languages.
//!
//! * Boolean Types: `bool`
//! * Signed Integer Types: `int` or `isize`, `int8`, `int16`, `int32`, `int64`, `int128`
//! * Unsigned Integer Types: `uint` or `usize`, `uint8`, `uint16`, `uint32`, `uint64`, `uint128`
//! * Floating Point Types: `float16`, `float32`, `float64`
//! * Char and String types: `char`, `string`
//!
//! # Extension Types
//!
//! These are common special datatypes, prefixed with +.
//!
//! * `bytes`
//! * `date_time`, `date`, `time`, `duration`
//! * `decimal`
//! * `uuid`
//! * `rgb`, `rgba`
//!
//! # Types and Paths
//!
//! Any string segment not starting with an reserved symbol is a **Type** or a **Path** if
//! it is not a **Builtin Type**.
//! Builtin types use **snake_case** so you should use **PascalCase** to avoid collision.
//!
//! * Named Types
//!
//! `MyType`, `Foöbár`, `Hello World`, `2022`
//!
//! A validator can be provided to validate idents based on the user's needs.
//!
//! The [`RustIdent`] validator will fail `Hello World` and `2022`,
//! while the [`AsciiIdent`] validator will fail `Foöbár` additionally.
//!
//! Note type-protocol grammar treat whitespaces like normal characters,
//! the user is responsible for stripping them if needed.
//!
//! * Paths
//!
//! `path::to::Type`
//!
//! * Absolute Paths
//!
//! `::path::to::Type`
//!
//! # Optional Types
//!
//! `?T` represents a optional type like [`Option<T>`] or a nullable pointer.
//!
//! e.g. `?string`
//!
//! # Array Types
//!
//! `[N]T` represents a fix sized array type like [`[T;N]`].
//! N has to be an integer.
//!
//! e.g. `[4]int`
//!
//! # Vec Types
//!
//! `[]T` represents a dynamic sized array type like [`Vec<T>`].
//!
//! e.g. `[]int`
//!
//! # Set Types
//!
//! `[T]` represents a collection of unique keys like [`HashSet<T>`](std::collections::HashSet).
//!
//! e.g. `[string]`
//!
//! # Map Types
//!
//! `[TKey]TValue` represents a collection of keys and values like [`HashMap<T>`](std::collections::HashMap).
//!
//! e.g. `[string]int`
//!
//! # Hint Types
//!
//! * Foreign Hint
//!
//! `@T` hints that T is a foreign type.






mod derive;
pub use derive::ToTypeProtocol;

#[cfg(test)]
mod tests;

use std::{
    str::FromStr,
    marker::PhantomData,
    num::{NonZeroUsize, ParseIntError},
    fmt::{Display, Pointer}
};

pub trait IdentValidation {
    fn validate(s: &str) -> bool;
}

#[derive(Debug, PartialEq, Eq)]
pub struct AlwaysValid;
#[derive(Debug, PartialEq, Eq)]
pub struct UnicodeXID;
#[derive(Debug, PartialEq, Eq)]
pub struct RustIdent;
#[derive(Debug, PartialEq, Eq)]
pub struct AsciiIdent;

impl IdentValidation for AlwaysValid {
    fn validate(_: &str) -> bool {
        true
    }
}

impl IdentValidation for UnicodeXID {
    fn validate(s: &str) -> bool {
        let mut chars = s.chars();
        if let Some(c) = chars.next() {
            if unicode_ident::is_xid_start(c) {
                chars.all(|c| unicode_ident::is_xid_continue(c))
            } else {
                false
            }
        } else {
            false
        }
    }
}

impl IdentValidation for RustIdent {
    fn validate(s: &str) -> bool {
        let mut chars = s.chars();
        if let Some(c) = chars.next() {
            if unicode_ident::is_xid_start(c) || c == '_' {
                chars.all(|c| unicode_ident::is_xid_continue(c))
            } else {
                false
            }
        } else {
            false
        }
    }
}

impl IdentValidation for AsciiIdent {
    fn validate(s: &str) -> bool {
        let mut chars = s.chars();
        if let Some(c) = chars.next() {
            if matches!(c, 'a'..='z'|'A'..='Z'|'_') {
                chars.all(|c| matches!(c, '0'..='9'|'a'..='z'|'A'..='Z'|'_'))
            } else {
                false
            }
        } else {
            false
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Never {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UniversalType {
    Bool,
    USize,
    ISize,
    Int(NonZeroUsize),
    UInt(NonZeroUsize),
    Float(NonZeroUsize),
    Char,
    String,
}

impl FromStr for UniversalType {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "bool" => Self::Bool,
            "int"|"isize" => Self::ISize,
            "uint"|"usize" => Self::USize,
            "int8" => Self::Int(nz!(1)),
            "int16" => Self::Int(nz!(2)),
            "int32" => Self::Int(nz!(4)),
            "int64" => Self::Int(nz!(8)),
            "int128" => Self::Int(nz!(16)),
            "uint8" => Self::UInt(nz!(1)),
            "uint16" => Self::UInt(nz!(2)),
            "uint32" => Self::UInt(nz!(4)),
            "uint64" => Self::UInt(nz!(8)),
            "uint128" => Self::UInt(nz!(16)),
            "float16"|"half" => Self::Float(nz!(2)),
            "float"|"float32"|"single" => Self::Float(nz!(4)),
            "float64"|"double" => Self::Float(nz!(8)),
            "char" => Self::Char,
            "string" => Self::String,
            _ => return Err(())
        })
    }
}

impl Display for UniversalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UniversalType::Bool => f.write_str("bool"),
            UniversalType::USize => f.write_str("uint"),
            UniversalType::ISize => f.write_str("int"),
            UniversalType::Int(n) => {
                f.write_str("int")?;
                n.checked_mul(nz!(8)).unwrap().fmt(f)
            },
            UniversalType::UInt(n) => {
                f.write_str("uint")?;
                n.checked_mul(nz!(8)).unwrap().fmt(f)
            },
            UniversalType::Float(n) => {
                f.write_str("float")?;
                n.checked_mul(nz!(8)).unwrap().fmt(f)
            },
            UniversalType::Char => f.write_str("char"),
            UniversalType::String => f.write_str("string"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, strum::IntoStaticStr, strum::EnumString)]
#[non_exhaustive]
pub enum ExtensionType {
    #[strum(serialize="decimal")]
    Decimal,
    #[strum(serialize="datetime")]
    DateTime,
    #[strum(serialize="date")]
    Date,
    #[strum(serialize="time")]
    Time,
    #[strum(serialize="duration")]
    Duration,
    #[strum(serialize="rgb")]
    Rgb,
    #[strum(serialize="rgba")]
    Rgba,
    #[strum(serialize="uuid")]
    Uuid,
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Typing<Validation = AlwaysValid> {
    /// The `none` type.
    None,
    /// Universal types in almost every language.
    ///
    /// See [`UniversalType`]
    Common(UniversalType),
    /// Common types hard to describe with normal data structures.
    /// Prefixed with `+`.
    ///
    /// i.e. `+datetime`, `+rgba`, `+uuid`
    ///
    /// See [`ExtensionType`]
    Extension(ExtensionType),
    /// A named type, with its contents defined elsewhere.
    Named(String),
    /// A type with a path.
    Path{
        /// if true, indicate this is an absolute path i.e.`::path`
        absolute: bool,
        /// path to name i.e `[path::to]::name`
        path: Vec<String>,
        /// last item in the path i.e `path::to::[name]`
        name: String,
    },
    /// An optional or nullable type.
    Option(Box<Self>),
    /// A nameless product type delimited with comma.
    ///
    /// i.e. `(int,string,char)`
    Tuple(Vec<Self>),
    /// A fix sized array.
    ///
    /// i.e. `[10]int`
    Array(usize, Box<Self>),
    /// A variable sized array.
    ///
    /// i.e. `[]int`
    Vec(Box<Self>),
    /// A set of keys.
    ///
    /// i.e. `[int]`
    Set(Box<Self>),
    /// A set of key value pairs.
    ///
    /// i.e. `[string]int`
    Map(Box<Self>,Box<Self>),
    /// A hint that the type is foreign.
    ///
    /// i.e. `@path::to::struct`
    Foreign(Box<Self>),
    #[doc(hidden)]
    _Invalid(PhantomData<Validation>, Never)
}

impl<V> Typing<V> {
    fn boxed(self) -> Box<Self> {
        Box::new(self)
    }
}

impl<V> Display for Typing<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Typing::None => f.write_str("none"),
            Typing::Common(t) => t.fmt(f),
            Typing::Extension(e) => {
                f.write_str("+")?;
                e.fmt(f)
            },
            Typing::Named(n) => f.write_str(&n),
            Typing::Path { absolute, path, name } => {
                if *absolute { f.write_str("::")?; }
                for s in path {
                    f.write_str(&s)?;
                    f.write_str("::")?;
                }
                f.write_str(&name)
            },
            Typing::Option(t) => {
                f.write_str("?")?;
                t.as_ref().fmt(f)
            },
            Typing::Tuple(items) => {
                f.write_str("(")?;
                let mut iter = items.iter();
                if let Some(first) = iter.next() {
                    first.fmt(f)?;
                }
                for item in iter {
                    f.write_str(",")?;
                    item.fmt(f)?;
                }
                f.write_str(")")
            },
            Typing::Array(len, item) => {
                f.write_str("[")?;
                len.fmt(f)?;
                f.write_str("]")?;
                item.as_ref().fmt(f)
            },
            Typing::Vec(item) => {
                f.write_str("[]")?;
                item.as_ref().fmt(f)
            },
            Typing::Set(item) => {
                f.write_str("[")?;
                item.as_ref().fmt(f)?;
                f.write_str("]")
            },
            Typing::Map(key, value) => {
                f.write_str("[")?;
                key.as_ref().fmt(f)?;
                f.write_str("]")?;
                value.as_ref().fmt(f)
            },
            Typing::Foreign(item) => {
                f.write_str("@")?;
                item.as_ref().fmt(f)
            },
            Typing::_Invalid(..) => unreachable!(),
        }
    }
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum Error {
    #[error("Empty string as a type is not allowed, use 'none' instead.")]
    Empty,
    #[error("Parenthesis () mismatch.")]
    ParenthesisMismatch,
    #[error("Brackets [] mismatch.")]
    BracketsMismatch,
    #[error("Unknown extension type.")]
    UnknownExtensionType,
    #[error("Invalid ident found.")]
    ValidationFailed,
    #[error("{}", 0)]
    ParseIntError(#[from]ParseIntError)
}

impl<V: IdentValidation> FromStr for Typing<V> {
    type Err = Error;

    /// type-protocol assumes compact whitespace-less strings.
    /// This function does not identify whitespaces in any way
    /// and will keep them in the resulting ident.
    /// Remove them before calling this function if you need to.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "none" {
            return Ok(Self::None);
        }
        let mut chars = s.chars();
        Ok(match chars.next() {
            None => return Err(Error::Empty),
            Some(')'|']'|'}') => return Err(Error::BracketsMismatch),
            Some('(') => {
                if chars.next_back() != Some(')') {
                    return Err(Error::BracketsMismatch);
                }
                let mut paren = 0;
                let mut bracket = 0;
                let result = Self::Tuple(chars.as_str()
                    .split(|c| {
                        match c {
                            '[' => bracket += 1,
                            ']' => bracket -= 1,
                            '(' => paren += 1,
                            ')' => paren -= 1,
                            ',' if paren == 0 && bracket == 0 => return true,
                            _ => (),
                        }
                        return false;
                    })
                    .map(|x| Self::from_str(x))
                    .collect::<Result<Vec<_>, _>>()?);
                if paren != 0 {
                    return Err(Error::ParenthesisMismatch)
                } else if bracket != 0 {
                    return Err(Error::BracketsMismatch)
                } else {
                    result
                }
            },
            Some('[') => {
                let mut paren = 0;
                let mut bracket = 1;
                let (key, value) = match chars.as_str().split_once(|c| {
                    match c {
                        '[' => bracket += 1,
                        ']' => {
                            bracket -= 1;
                            if bracket == 0 {
                                return true;
                            }
                        },
                        _ => (),
                    }
                    return false;
                }) {
                    Some((k, v)) => (k, v),
                    None => return Err(Error::BracketsMismatch),
                };
                if key.len() == 0 {
                    Self::Vec(Self::from_str(value)?.boxed())
                } else if value.len() == 0 {
                    Self::Set(Self::from_str(key)?.boxed())
                } else if key.chars().all(|x| matches!(x, '0'..='9')) {
                    Self::Array(key.parse()?, Self::from_str(value)?.boxed())
                } else {
                    Self::Map(Self::from_str(key)?.boxed(), Self::from_str(value)?.boxed())
                }
            },
            Some('?') => Self::Option(Self::from_str(chars.as_str())?.boxed()),
            Some('@') => Self::Foreign(Self::from_str(chars.as_str())?.boxed()),
            _ => {
                if let Ok(t) = UniversalType::from_str(s) {
                    Self::Common(t)
                } else if let Ok(t) = ExtensionType::from_str(s) {
                    Self::Extension(t)
                } else if s.contains("::") {
                    let absolute = s.starts_with("::");
                    let s = s.trim_start_matches("::");
                    let mut path: Vec<String> = s.split("::").map(|x| x.to_owned()).collect();
                    if path.iter().any(|x| !V::validate(x)) {
                        return Err(Error::ValidationFailed);
                    }
                    let name = path.pop().ok_or(Error::Empty)?;
                    Self::Path { absolute, path, name }
                } else if V::validate(s) {
                    Self::Named(s.to_owned())
                } else {
                    return Err(Error::ValidationFailed);
                }
            }
        })
    }
}

#[cfg(feature = "serde")]
const _: () = {
    use serde::{Serialize, Deserialize};

    impl<V> Serialize for Typing<V> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: serde::Serializer {
            self.to_string().serialize(serializer)
        }
    }

    impl<'de, V: IdentValidation> Deserialize<'de> for Typing<V> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: serde::Deserializer<'de> {
            Self::from_str(<&str>::deserialize(deserializer)?)
                .map_err(|e| serde::de::Error::custom(e.to_string()))
        }
    }
};
