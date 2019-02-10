//! Converts a sequence of arbitrary literal values into a single byte array at the compile time.
//!
//! List of supported literals:
//!
//! * UTF-8 characters (`'?'`) as well as UTF-8 strings (`"こんにちは世界"`).
//! * Integers, also negative and size-suffixed (`-99u32`).
//!     * Non-suffixed integers are written in a form as small as possible.
//!     * The little endian is used as a default endianness but could be changed build-wise by
//!       enabling `default-big-endian` feature.
//!     * It is possible to set endianness for a single literal using the "ascription"
//!       syntax, e.g. `9000: LE` or `0x8u32: be`.
//! * Floats, also negative and size-suffixed (`-3.1415926f64`).
//!     * Non-suffixed floats are written in a form as small as possible.
//!     * The little endian is used as a default endianness but could be changed build-wise by
//!       enabling `default-big-endian` feature.
//!     * It is possible to set endianness for a single literal using the "ascription"
//!       syntax, e.g. `0.2: LE` or `-15.92f64: be`.
//!
//! # Examples
//!
//! ```
//! use bytify::bytify;
//!
//! fn main() {
//!     assert_eq!(&bytify!(
//!         "The 🎂 is a lie!",
//!         2948509150, -559038801: BE,
//!         0.36658e+8, -2583.1f64: le,
//!     )[..], &[
//!         b'T', b'h', b'e', b' ',
//!         0xF0, 0x9F, 0x8E, 0x82,
//!         b' ', b'i', b's', b' ', b'a', b' ', b'l', b'i', b'e', b'!',
//!         0xDE, 0xAD, 0xBE, 0xAF, 0xDE, 0xAD, 0xBE, 0xAF,
//!         0xD4, 0xD6, 0x0B, 0x4C, 0x33, 0x33, 0x33, 0x33, 0x33, 0x2e, 0xa4, 0xc0,
//!     ][..]);
//! }
//! ```

use proc_macro_hack::proc_macro_hack;

/// Converts a sequence of arbitrary literal values into a single byte array at the compile time.
///
/// List of supported literals:
///
/// * UTF-8 characters (`'?'`) as well as UTF-8 strings (`"こんにちは世界"`).
/// * Integers, also negative and size-suffixed (`-99u32`).
///     * Non-suffixed integers are written in a form as small as possible.
///     * The little endian is used as a default endianness but could be changed build-wise by
///       enabling `default-big-endian` feature.
///     * It is possible to set endianness for a single literal using the "ascription"
///       syntax, e.g. `9000: LE` or `0x8u32: be`.
/// * Floats, also negative and size-suffixed (`-3.1415926f64`).
///     * Non-suffixed floats are written in a form as small as possible.
///     * The little endian is used as a default endianness but could be changed build-wise by
///       enabling `default-big-endian` feature.
///     * It is possible to set endianness for a single literal using the "ascription"
///       syntax, e.g. `0.2: LE` or `-15.92f64: be`.
///
/// # Examples
///
/// ```
/// use bytify::bytify;
///
/// fn main() {
///     assert_eq!(&bytify!(
///         "The 🎂 is a lie!",
///         2948509150, -559038801: BE,
///         0.36658e+8, -2583.1f64: le,
///     )[..], &[
///         b'T', b'h', b'e', b' ',
///         0xF0, 0x9F, 0x8E, 0x82,
///         b' ', b'i', b's', b' ', b'a', b' ', b'l', b'i', b'e', b'!',
///         0xDE, 0xAD, 0xBE, 0xAF, 0xDE, 0xAD, 0xBE, 0xAF,
///         0xD4, 0xD6, 0x0B, 0x4C, 0x33, 0x33, 0x33, 0x33, 0x33, 0x2e, 0xa4, 0xc0,
///     ][..]);
/// }
/// ```
#[proc_macro_hack]
pub use bytify_impl::bytify;

/// The same macro as [`bytify`] but returns a slice, instead of array.
///
/// [`bytify`]: macro.bytify.html
#[macro_export]
macro_rules! bytify_ref {
    ($($items:expr ),*) => (&bytify!($($items),*)[..]);
    ($($items:expr,) *) => (&bytify!($($items),*)[..]);
}
