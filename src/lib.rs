//! This crate provides a simple macro that can take multiple const-expr values as an input and
//! merge them all together into a continuous byte array at compile-time.
//! Supports all primitive types and is #\[no_std\] compatible.
//!
//! ```rust
//! use bytify::bytify;
//!
//! const CAKE: char = '🎂';
//!
//! assert_eq!(bytify!("The ", CAKE, " is a lie!"), [
//!     b'T', b'h', b'e',
//!     b' ',
//!     0xF0, 0x9F, 0x8E, 0x82,
//!     b' ',
//!     b'i', b's',
//!     b' ',
//!     b'a',
//!     b' ',
//!     b'l', b'i', b'e',
//!     b'!',
//! ]);
//! ```
//!
//! ### Supported types
//!
//! All primitive types (as literals or any other const-expr values) as well as `[u8; N]` and `&[u8]` values.
//!
//! * Unsuffixed numbers are inferred to be `i32` for integers and `f64` for floats.
//! * `bool` values are cast to `u8`.
//! * UTF-8 encoding is used to write `str` and `char` values.
//!
//! ### Endianness
//!
//! [`bytify!`] always writes data using current target's native endianness.
//! To switch to little/big endianness use [`bytify_le!`] or [`bytify_be!`] respectively.
//!
//! ```rust
//! use bytify::{bytify_be, bytify_le};
//!
//! assert_eq!(bytify_le!(1), [0x01, 0x00, 0x00, 0x00]);
//! assert_eq!(bytify_be!(1), [0x00, 0x00, 0x00, 0x01]);
//! ```
//!
//! ### Constants and statics
//!
//! ```rust
//! use bytify::bytify;
//!
//! bytify!(const NO_EVIL: '🙈', '🙉', '🙊');
//! assert_eq!(NO_EVIL, [0xF0, 0x9F, 0x99, 0x88, 0xF0, 0x9F, 0x99, 0x89, 0xF0, 0x9F, 0x99, 0x8A]);
//! ```

#![no_std]
#![warn(
    absolute_paths_not_starting_with_crate,
    meta_variable_misuse,
    missing_debug_implementations,
    missing_docs,
    noop_method_call,
    pointer_structural_match,
    unreachable_pub,
    unused_crate_dependencies,
    unused_lifetimes,
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::checked_conversions,
    clippy::cognitive_complexity,
    clippy::exhaustive_enums,
    clippy::exhaustive_structs,
    clippy::future_not_send,
    clippy::inconsistent_struct_constructor,
    clippy::inefficient_to_string,
    clippy::use_debug,
    clippy::use_self
)]

use typewit::{HasTypeWitness, MakeTypeWitness, TypeEq, TypeWitnessTypeArg};

#[derive(Debug)]
#[non_exhaustive]
#[doc(hidden)]
pub enum Endianness {
    Native,
    Big,
    Little,
}

/// This macro is a big endianness version of [`bytify!`] macro.
#[macro_export]
macro_rules! bytify_be {
    ($visibility:vis const $name:ident: $($items:expr),* $(,)?) => {
        $visibility const $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Big => $($items),*);
    };
    ($visibility:vis static $name:ident: $($items:expr),* $(,)?) => {
        $visibility static $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Big => $($items),*);
    };
    ($($items:expr),* $(,)?) => {
        $crate::bytify!(priv endianness: Big => $($items),*)
    };
}

/// This macro is a little endianness version of [`bytify!`] macro.
#[macro_export]
macro_rules! bytify_le {
    ($visibility:vis const $name:ident: $($items:expr),* $(,)?) => {
        $visibility const $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Little => $($items),*);
    };
    ($visibility:vis static $name:ident: $($items:expr),* $(,)?) => {
        $visibility static $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Little => $($items),*);
    };
    ($($items:expr),* $(,)?) => {
        $crate::bytify!(priv endianness: Little => $($items),*)
    };
}

/// This macro can take multiple const-expr values as an input and merge them all together into
/// a continuous byte array at compile-time. Supports all primitive types and is #\[no_std\] compatible.
///
/// ```rust
/// use bytify::bytify;
///
/// const CAKE: char = '🎂';
///
/// assert_eq!(bytify!("The ", CAKE, " is a lie!"), [
///     b'T', b'h', b'e',
///     b' ',
///     0xF0, 0x9F, 0x8E, 0x82,
///     b' ',
///     b'i', b's',
///     b' ',
///     b'a',
///     b' ',
///     b'l', b'i', b'e',
///     b'!',
/// ]);
/// ```
///
/// ### Supported types
///
/// All primitive types (as literals or any other const-expr values) as well as `[u8; N]` and `&[u8]` values.
///
/// * Unsuffixed numbers are inferred to be `i32` for integers and `f64` for floats.
/// * `bool` values are cast to `u8`.
/// * UTF-8 encoding is used to write `str` and `char` values.
///
/// ### Endianness
///
/// [`bytify!`] always writes data using current target's native endianness.
/// To switch to little/big endianness use [`bytify_le!`] or [`bytify_be!`] respectively.
///
/// ```rust
/// use bytify::{bytify_be, bytify_le};
///
/// assert_eq!(bytify_le!(1), [0x01, 0x00, 0x00, 0x00]);
/// assert_eq!(bytify_be!(1), [0x00, 0x00, 0x00, 0x01]);
/// ```
///
/// ### Constants and statics
///
/// ```rust
/// use bytify::bytify;
///
/// bytify!(const NO_EVIL: '🙈', '🙉', '🙊');
/// assert_eq!(NO_EVIL, [0xF0, 0x9F, 0x99, 0x88, 0xF0, 0x9F, 0x99, 0x89, 0xF0, 0x9F, 0x99, 0x8A]);
/// ```
#[macro_export]
macro_rules! bytify {
    ($visibility:vis const $name:ident: $($items:expr),* $(,)?) => {
        $visibility const $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Native => $($items),*);
    };
    ($visibility:vis static $name:ident: $($items:expr),* $(,)?) => {
        $visibility static $name: [::core::primitive::u8; $crate::bytify!(priv len: $($items),*)] = $crate::bytify!(priv endianness: Native => $($items),*);
    };
    ($($items:expr),* $(,)?) => {
        $crate::bytify!(priv endianness: Native => $($items),*)
    };
    (priv endianness: $endianness:ident => $($items:expr),*) => {
        $crate::bytify!(priv concat: $(($crate::bytify_len($items), $crate::bytify_one($crate::Endianness::$endianness, $items))),*)
    };
    (priv len: $($items:expr),*) => {
        0 $(+ $crate::bytify_len($items))*
    };
    (priv concat: $(($len:expr, $bytes:expr)),*) => {
        {
            const LEN: ::core::primitive::usize = 0 $(+ $len)*;
            const SUM: [::core::primitive::u8; LEN] = {
                let mut sum: [::core::primitive::u8; LEN] = [0; LEN];
                let mut offset: ::core::primitive::usize = 0;
                $(
                    {
                        const LEN: ::core::primitive::usize = $len;
                        const BYTES: [::core::primitive::u8; $len] = $bytes;
                        let mut i = 0;
                        while i < LEN {
                            sum[offset + i] = BYTES[i];
                            i += 1;
                        }
                        offset += LEN;
                    }
                )*
                sum
            };
            SUM
        }
    };
    (priv $($unhandled:tt)*) => {
        ::core::compile_error!(::core::stringify!(unhandled input: $($unhandled)*))
    };
}

#[doc(hidden)]
pub const fn bytify_len<const X: usize, T>(value: T) -> usize
where
    T: HasTypeWitness<BytifyWitness<X, T>>,
{
    match T::WITNESS {
        BytifyWitness::bool(witness) => bool::len(witness.to_right(value)),
        BytifyWitness::char(witness) => char::len(witness.to_right(value)),
        BytifyWitness::u8(witness) => u8::len(witness.to_right(value)),
        BytifyWitness::i8(witness) => i8::len(witness.to_right(value)),
        BytifyWitness::u16(witness) => u16::len(witness.to_right(value)),
        BytifyWitness::i16(witness) => i16::len(witness.to_right(value)),
        BytifyWitness::u32(witness) => u32::len(witness.to_right(value)),
        BytifyWitness::i32(witness) => i32::len(witness.to_right(value)),
        BytifyWitness::u64(witness) => u64::len(witness.to_right(value)),
        BytifyWitness::i64(witness) => i64::len(witness.to_right(value)),
        BytifyWitness::u128(witness) => u128::len(witness.to_right(value)),
        BytifyWitness::i128(witness) => i128::len(witness.to_right(value)),
        BytifyWitness::usize(witness) => usize::len(witness.to_right(value)),
        BytifyWitness::isize(witness) => isize::len(witness.to_right(value)),
        BytifyWitness::f32(witness) => f32::len(witness.to_right(value)),
        BytifyWitness::f64(witness) => f64::len(witness.to_right(value)),
        BytifyWitness::str(witness) => str::len(witness.to_right(value)),
        BytifyWitness::SliceArray(witness) => slice_array::len(witness.to_right(value)),
        BytifyWitness::Array(witness) => array::len(witness.to_right(value)),
    }
}

#[doc(hidden)]
pub const fn bytify_one<const X: usize, const N: usize, T>(
    endianness: Endianness,
    value: T,
) -> [u8; N]
where
    T: HasTypeWitness<BytifyWitness<X, T>>,
{
    match T::WITNESS {
        BytifyWitness::bool(witness) => bool::copy(endianness, witness.to_right(value)),
        BytifyWitness::char(witness) => char::copy(endianness, witness.to_right(value)),
        BytifyWitness::u8(witness) => u8::copy(endianness, witness.to_right(value)),
        BytifyWitness::i8(witness) => i8::copy(endianness, witness.to_right(value)),
        BytifyWitness::u16(witness) => u16::copy(endianness, witness.to_right(value)),
        BytifyWitness::i16(witness) => i16::copy(endianness, witness.to_right(value)),
        BytifyWitness::u32(witness) => u32::copy(endianness, witness.to_right(value)),
        BytifyWitness::i32(witness) => i32::copy(endianness, witness.to_right(value)),
        BytifyWitness::u64(witness) => u64::copy(endianness, witness.to_right(value)),
        BytifyWitness::i64(witness) => i64::copy(endianness, witness.to_right(value)),
        BytifyWitness::u128(witness) => u128::copy(endianness, witness.to_right(value)),
        BytifyWitness::i128(witness) => i128::copy(endianness, witness.to_right(value)),
        BytifyWitness::usize(witness) => usize::copy(endianness, witness.to_right(value)),
        BytifyWitness::isize(witness) => isize::copy(endianness, witness.to_right(value)),
        BytifyWitness::f32(witness) => f32::copy(endianness, witness.to_right(value)),
        BytifyWitness::f64(witness) => f64::copy(endianness, witness.to_right(value)),
        BytifyWitness::str(witness) => str::copy(endianness, witness.to_right(value)),
        BytifyWitness::SliceArray(witness) => {
            slice_array::copy(endianness, witness.to_right(value))
        },
        BytifyWitness::Array(witness) => array::copy(endianness, witness.to_right(value)),
    }
}

#[derive(Debug)]
#[non_exhaustive]
#[doc(hidden)]
#[allow(non_camel_case_types)]
pub enum BytifyWitness<const X: usize, Witness: ?Sized> {
    bool(TypeEq<Witness, bool>),
    char(TypeEq<Witness, char>),
    u8(TypeEq<Witness, u8>),
    i8(TypeEq<Witness, i8>),
    u16(TypeEq<Witness, u16>),
    i16(TypeEq<Witness, i16>),
    u32(TypeEq<Witness, u32>),
    i32(TypeEq<Witness, i32>),
    u64(TypeEq<Witness, u64>),
    i64(TypeEq<Witness, i64>),
    u128(TypeEq<Witness, u128>),
    i128(TypeEq<Witness, i128>),
    usize(TypeEq<Witness, usize>),
    isize(TypeEq<Witness, isize>),
    f32(TypeEq<Witness, f32>),
    f64(TypeEq<Witness, f64>),
    str(TypeEq<Witness, &'static str>),
    SliceArray(TypeEq<Witness, &'static [u8]>),
    Array(TypeEq<Witness, [u8; X]>),
}

impl<const X: usize, Witness> TypeWitnessTypeArg for BytifyWitness<X, Witness> {
    type Arg = Witness;
}

mod bool {
    use super::*;

    pub(crate) const fn len(value: bool) -> usize {
        u8::len(value as u8)
    }

    pub(crate) const fn copy<const N: usize>(endianness: Endianness, value: bool) -> [u8; N] {
        u8::copy(endianness, value as u8)
    }

    impl MakeTypeWitness for BytifyWitness<0, bool> {
        const MAKE: Self = Self::bool(TypeEq::NEW);
    }
}

mod char {
    use super::*;

    pub(crate) const fn len(value: char) -> usize {
        value.len_utf8()
    }

    pub(crate) const fn copy<const N: usize>(endianness: Endianness, value: char) -> [u8; N] {
        array::copy(endianness, bytes::<N>(value))
    }

    const fn bytes<const N: usize>(char: char) -> [u8; N] {
        const TAG_CONT: u8 = 0b1000_0000;
        const TAG_TWO_B: u8 = 0b1100_0000;
        const TAG_THREE_B: u8 = 0b1110_0000;
        const TAG_FOUR_B: u8 = 0b1111_0000;
        let mut array = [0; N];
        let code = char as u32;
        match code {
            ..= 0x0000007F => {
                array[0] = (code & 0xFF) as u8;
            },
            0x00000080 ..= 0x000007FF => {
                array[0] = (code >> 6 & 0x1F) as u8 | TAG_TWO_B;
                array[1] = (code & 0x3F) as u8 | TAG_CONT;
            },
            0x00000800 ..= 0x0000FFFF => {
                array[0] = (code >> 12 & 0x0F) as u8 | TAG_THREE_B;
                array[1] = (code >> 6 & 0x3F) as u8 | TAG_CONT;
                array[2] = (code & 0x3F) as u8 | TAG_CONT;
            },
            0x00010000 .. => {
                array[0] = (code >> 18 & 0x07) as u8 | TAG_FOUR_B;
                array[1] = (code >> 12 & 0x3F) as u8 | TAG_CONT;
                array[2] = (code >> 6 & 0x3F) as u8 | TAG_CONT;
                array[3] = (code & 0x3F) as u8 | TAG_CONT;
            },
        }
        array
    }

    impl MakeTypeWitness for BytifyWitness<0, char> {
        const MAKE: Self = Self::char(TypeEq::NEW);
    }
}

macro_rules! bytify_integer {
    ($name:ident) => {
        mod $name {
            use super::*;

            pub(crate) const fn len(value: $name) -> usize {
                value.to_ne_bytes().len()
            }

            pub(crate) const fn copy<const N: usize>(
                endianness: Endianness,
                value: $name,
            ) -> [u8; N] {
                let bytes = match endianness {
                    Endianness::Native => value.to_ne_bytes(),
                    Endianness::Big => value.to_be_bytes(),
                    Endianness::Little => value.to_le_bytes(),
                };
                let mut array = [0; N];
                let mut i = 0;
                while i < bytes.len() {
                    array[i] = bytes[i];
                    i += 1;
                }
                array
            }

            impl MakeTypeWitness for BytifyWitness<0, $name> {
                const MAKE: Self = Self::$name(TypeEq::NEW);
            }
        }
    };
}

bytify_integer!(u8);
bytify_integer!(i8);
bytify_integer!(u16);
bytify_integer!(i16);
bytify_integer!(u32);
bytify_integer!(i32);
bytify_integer!(u64);
bytify_integer!(i64);
bytify_integer!(u128);
bytify_integer!(i128);
bytify_integer!(usize);
bytify_integer!(isize);

macro_rules! bytify_float {
    ($name:ident, $bits:ident) => {
        mod $name {
            use super::*;
            use core::mem::transmute;

            pub(crate) const fn len(value: $name) -> usize {
                $bits::len(bits(value))
            }

            pub(crate) const fn copy<const N: usize>(
                endianness: Endianness,
                value: $name,
            ) -> [u8; N] {
                $bits::copy(endianness, bits(value))
            }

            const fn bits(value: $name) -> $bits {
                unsafe { transmute::<$name, $bits>(value) }
            }

            impl MakeTypeWitness for BytifyWitness<0, $name> {
                const MAKE: Self = Self::$name(TypeEq::NEW);
            }
        }
    };
}

bytify_float!(f32, u32);
bytify_float!(f64, u64);

mod str {
    use super::*;

    pub(crate) const fn len(value: &str) -> usize {
        slice_array::len(value.as_bytes())
    }

    pub(crate) const fn copy<const N: usize>(endianness: Endianness, value: &str) -> [u8; N] {
        slice_array::copy(endianness, value.as_bytes())
    }

    impl MakeTypeWitness for BytifyWitness<0, &'static str> {
        const MAKE: Self = Self::str(TypeEq::NEW);
    }
}

mod slice_array {
    use super::*;

    pub(crate) const fn len(value: &[u8]) -> usize {
        value.len()
    }

    pub(crate) const fn copy<const N: usize>(_: Endianness, value: &[u8]) -> [u8; N] {
        let mut array = [0; N];
        let mut i = 0;
        while i < value.len() {
            array[i] = value[i];
            i += 1;
        }
        array
    }

    impl MakeTypeWitness for BytifyWitness<0, &'static [u8]> {
        const MAKE: Self = Self::SliceArray(TypeEq::NEW);
    }
}

mod array {
    use super::*;

    pub(crate) const fn len<const X: usize>(value: [u8; X]) -> usize {
        slice_array::len(&value)
    }

    pub(crate) const fn copy<const X: usize, const N: usize>(
        endianness: Endianness,
        value: [u8; X],
    ) -> [u8; N] {
        slice_array::copy(endianness, &value)
    }

    impl<const X: usize> MakeTypeWitness for BytifyWitness<X, [u8; X]> {
        const MAKE: Self = Self::Array(TypeEq::NEW);
    }
}
