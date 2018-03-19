#![cfg_attr(feature = "cargo-clippy", allow(explicit_iter_loop, unreadable_literal))]

#[macro_use]
extern crate bytify;
extern crate byteorder;

use std::io::Cursor;
use byteorder::{ReadBytesExt, LE};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expected {
    U32(u32),
    I32(i32),
    U16(u16),
    I16(i16),
    U8(u8),
    I8(i8),
}

use Expected::*;

macro_rules! assert_bytify_eq {
    ($r:expr, $l:expr) => {
        let r = $r;
        let l = $l;
        let mut reader = Cursor::new(&r[..]);
        for e in l.iter() {
            match *e {
                Expected::U32(v) => {
                    assert_eq!(reader.read_u32::<LE>().unwrap(), v);
                },
                Expected::I32(v) => {
                    assert_eq!(reader.read_i32::<LE>().unwrap(), v);
                },
                Expected::U16(v) => {
                    assert_eq!(reader.read_u16::<LE>().unwrap(), v);
                },
                Expected::I16(v) => {
                    assert_eq!(reader.read_i16::<LE>().unwrap(), v);
                },
                Expected::U8(v) => {
                    assert_eq!(reader.read_u8().unwrap(), v);
                },
                Expected::I8(v) => {
                    assert_eq!(reader.read_i8().unwrap(), v);
                },
            }
        }
    };
}

#[test]
fn u32() {
    assert_bytify_eq!(
        bytify!(
               65536,   1952862,    3593941,    4294967295,
            0x010000, 0x01DCC5E, 0x0036D6D5, 0x000FFFFFFFF,
            0o200000, 0o7346136, 0o15553325, 0o37777777777,
        ),
        [
            U32(65536), U32(1952862), U32(3593941), U32(4294967295),
            U32(65536), U32(1952862), U32(3593941), U32(4294967295),
            U32(65536), U32(1952862), U32(3593941), U32(4294967295),
        ]
    );
}

#[test]
fn u32_suffixed() {
    assert_bytify_eq!(
        bytify!(
              0u32,   59u32,   358u32,   15879u32,    95812u32,
            0x0u32, 0x3Bu32, 0x166u32, 0x03E07u32, 0x017644u32,
            0o0u32, 0o73u32, 0o546u32, 0o37007u32, 0o273104u32,
        ),
        [
            U32(0), U32(59), U32(358), U32(15879), U32(95812),
            U32(0), U32(59), U32(358), U32(15879), U32(95812),
            U32(0), U32(59), U32(358), U32(15879), U32(95812),
        ]
    );
}

#[test]
fn i32() {
    assert_bytify_eq!(
        bytify!(
               -2147483648,   -1853117,   -1000001,
            -0x00080000000, -0x01C46BD, -0x00F4241,
            -0o20000000000, -0o7043275, -0o3641101,
        ),
        [
            I32(-2147483648), I32(-1853117), I32(-1000001),
            I32(-2147483648), I32(-1853117), I32(-1000001),
            I32(-2147483648), I32(-1853117), I32(-1000001),
        ]
    );
}

#[test]
fn i32_suffixed() {
    assert_bytify_eq!(
        bytify!(
               -2147483648i32,   -1853117i32,   -1000001i32,   0i32,   51i32,   491i32,    5177353i32,    2147483647i32,
            -0x00080000000i32, -0x01C46BDi32, -0x00F4241i32, 0x0i32, 0x33i32, 0x1EBi32, 0x004F0009i32, 0x0007FFFFFFFi32,
            -0o20000000000i32, -0o7043275i32, -0o3641101i32, 0o0i32, 0o63i32, 0o753i32, 0o23600011i32, 0o17777777777i32,
        ),
        [
            I32(-2147483648i32), I32(-1853117i32), I32(-1000001i32), I32(0i32), I32(51i32), I32(491i32), I32(5177353i32), I32(2147483647i32),
            I32(-2147483648i32), I32(-1853117i32), I32(-1000001i32), I32(0i32), I32(51i32), I32(491i32), I32(5177353i32), I32(2147483647i32),
            I32(-2147483648i32), I32(-1853117i32), I32(-1000001i32), I32(0i32), I32(51i32), I32(491i32), I32(5177353i32), I32(2147483647i32),
        ]
    );
}

#[test]
fn u16() {
    assert_bytify_eq!(
        bytify!(
              256,   15782,    58391,    65535,
            0x100, 0x03DA6, 0x00E417, 0x00FFFF,
            0o400, 0o36646, 0o162027, 0o177777,
        ),
        [
            U16(256), U16(15782), U16(58391), U16(65535),
            U16(256), U16(15782), U16(58391), U16(65535),
            U16(256), U16(15782), U16(58391), U16(65535),
        ]
    );
}

#[test]
fn u16_suffixed() {
    assert_bytify_eq!(
        bytify!(
              0u16,   35u16,    85u16,   255u16,
            0x0u16, 0x23u16, 0x055u16, 0x0FFu16,
            0o0u16, 0o43u16, 0o125u16, 0o377u16,
        ),
        [
            U16(0), U16(35), U16(85), U16(255),
            U16(0), U16(35), U16(85), U16(255),
            U16(0), U16(35), U16(85), U16(255),
        ]
    );
}

#[test]
fn i16() {
    assert_bytify_eq!(
        bytify!(
               -32768,   -21458,   -14942,
            -0x008000, -0x053D2, -0x03A5E,
            -0o100000, -0o51722, -0o35136,
        ),
        [
            I16(-32768), I16(-21458), I16(-14942),
            I16(-32768), I16(-21458), I16(-14942),
            I16(-32768), I16(-21458), I16(-14942),
        ]
    );
}

#[test]
fn i16_suffixed() {
    assert_bytify_eq!(
        bytify!(
               -32768i16,   -21458i16,   -14942i16,   0i16,   10841i16,   25837i16,   32767i16,
            -0x008000i16, -0x053D2i16, -0x03A5Ei16, 0x0i16, 0x02A59i16, 0x064EDi16, 0x07FFFi16,
            -0o100000i16, -0o51722i16, -0o35136i16, 0o0i16, 0o25131i16, 0o62355i16, 0o77777i16,
        ),
        [
            I16(-32768), I16(-21458), I16(-14942), I16(0), I16(10841), I16(25837), I16(32767),
            I16(-32768), I16(-21458), I16(-14942), I16(0), I16(10841), I16(25837), I16(32767),
            I16(-32768), I16(-21458), I16(-14942), I16(0), I16(10841), I16(25837), I16(32767),
        ]
    );
}

#[test]
fn u8() {
    assert_bytify_eq!(
        bytify!(
              0,   50,   63,   255,
            0x0, 0x32, 0x3F, 0x0FF,
            0o0, 0o62, 0o77, 0o377,
        ),
        [
            U8(0), U8(50), U8(63), U8(255),
            U8(0), U8(50), U8(63), U8(255),
            U8(0), U8(50), U8(63), U8(255),
        ]
    );
}

#[test]
fn i8() {
    assert_bytify_eq!(
        bytify!(
              -128,    -99,   -25,
            -0x080, -0x063, -0x19,
            -0o200, -0o143, -0o31,
        ),
        [
            I8(-128), I8(-99), I8(-25),
            I8(-128), I8(-99), I8(-25),
            I8(-128), I8(-99), I8(-25),
        ]
    );
}

#[test]
fn u8_suffixed() {
    assert_bytify_eq!(
        bytify!(
              0u8,   33u8,    92u8,   255u8,
            0x0u8, 0x21u8, 0x05Cu8, 0x0FFu8,
            0o0u8, 0o41u8, 0o134u8, 0o377u8,
        ),
        [
            U8(0u8), U8(33u8), U8(92u8), U8(255u8),
            U8(0u8), U8(33u8), U8(92u8), U8(255u8),
            U8(0u8), U8(33u8), U8(92u8), U8(255u8),
        ]
    );
}

#[test]
fn i8_suffixed() {
    assert_bytify_eq!(
        bytify!(
              -128i8,    -99i8,   -25i8,   0i8,   53i8,    82i8,   127i8,
            -0x080i8, -0x063i8, -0x19i8, 0x0i8, 0x35i8, 0x052i8, 0x07Fi8,
            -0o200i8, -0o143i8, -0o31i8, 0o0i8, 0o65i8, 0o122i8, 0o177i8,
        ),
        [
            I8(-128i8), I8(-99i8), I8(-25i8), I8(0i8), I8(53i8), I8(82i8), I8(127i8),
            I8(-128i8), I8(-99i8), I8(-25i8), I8(0i8), I8(53i8), I8(82i8), I8(127i8),
            I8(-128i8), I8(-99i8), I8(-25i8), I8(0i8), I8(53i8), I8(82i8), I8(127i8),
        ]
    );
}

#[test]
fn char() {
    assert_bytify_eq!(
        bytify!(
            'A', 'Я', '日', '❤', '\u{2764}',
        ),
        [
            U8(0x41),
            U8(0xD0), U8(0xAF),
            U8(0xE6), U8(0x97), U8(0xA5),
            U8(0xE2), U8(0x9D), U8(0xA4),
            U8(0xE2), U8(0x9D), U8(0xA4),
        ]
    );
}

#[test]
fn string() {
    assert_bytify_eq!(
        bytify!(
            "Hello World!", "こんにちは世界", "😍😀☹", "The 🎂 is a lie!", "\u{1F414} says cock-a-doodle-doo",
        ),
        [
            U8(0x48), U8(0x65), U8(0x6C), U8(0x6C), U8(0x6F), U8(0x20), U8(0x57), U8(0x6F), U8(0x72), U8(0x6C), U8(0x64), U8(0x21),
            U8(0xE3), U8(0x81), U8(0x93), U8(0xE3), U8(0x82), U8(0x93), U8(0xE3), U8(0x81), U8(0xAB), U8(0xE3), U8(0x81), U8(0xA1), U8(0xE3), U8(0x81), U8(0xAF), U8(0xE4), U8(0xB8), U8(0x96), U8(0xE7), U8(0x95), U8(0x8C),
            U8(0xF0), U8(0x9F), U8(0x98), U8(0x8D), U8(0xF0), U8(0x9F), U8(0x98), U8(0x80), U8(0xE2), U8(0x98), U8(0xB9),
            U8(0x54), U8(0x68), U8(0x65), U8(0x20), U8(0xF0), U8(0x9F), U8(0x8E), U8(0x82), U8(0x20), U8(0x69), U8(0x73), U8(0x20), U8(0x61), U8(0x20), U8(0x6C), U8(0x69), U8(0x65), U8(0x21),
            U8(0xF0), U8(0x9F), U8(0x90), U8(0x94), U8(0x20), U8(0x73), U8(0x61), U8(0x79), U8(0x73), U8(0x20), U8(0x63), U8(0x6F), U8(0x63), U8(0x6B), U8(0x2D), U8(0x61), U8(0x2D), U8(0x64), U8(0x6F), U8(0x6F), U8(0x64), U8(0x6C), U8(0x65), U8(0x2D), U8(0x64), U8(0x6F), U8(0x6F),
        ]
    );
}
