## Bytification utilities
[![Build Status](https://github.com/mahou-shoujo/bytify-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/mahou-shoujo/bytify-rs/actions/workflows/rust.yml)

This crate provides a simple macro that can take multiple const-expr values as an input and
merge them all together into a continuous byte array at compile-time.
Supports all primitive types and is #[no_std] compatible.

```rust
use bytify::bytify;

const CAKE: char = '🎂';

assert_eq!(bytify!("The ", CAKE, " is a lie!"), [
    b'T', b'h', b'e',
    b' ',
    0xF0, 0x9F, 0x8E, 0x82,
    b' ',
    b'i', b's',
    b' ',
    b'a',
    b' ',
    b'l', b'i', b'e',
    b'!',
]);
```

### Supported types

All primitive types (as literals or any other const-expr values) as well as `[u8; N]` and `&[u8]` values.

* Unsuffixed numbers are inferred to be `i32` for integers and `f64` for floats.
* `bool` values are cast to `u8`.
* UTF-8 encoding is used to write `str` and `char` values.

### Endianness

`bytify!` always writes data using current target's native endianness.
To switch to little/big endianness use `bytify_le!` or `bytify_be!` respectively.

```rust
use bytify::{bytify_be, bytify_le};

assert_eq!(bytify_le!(1), [0x01, 0x00, 0x00, 0x00]);
assert_eq!(bytify_be!(1), [0x00, 0x00, 0x00, 0x01]);
```

### Constants and statics

```rust
use bytify::bytify;

bytify!(const NO_EVIL: '🙈', '🙉', '🙊');
assert_eq!(NO_EVIL, [0xF0, 0x9F, 0x99, 0x88, 0xF0, 0x9F, 0x99, 0x89, 0xF0, 0x9F, 0x99, 0x8A]);
```
