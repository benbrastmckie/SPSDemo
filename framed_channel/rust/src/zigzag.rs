// SPDX-License-Identifier: Apache-2.0
//! Zigzag signed varint for `i32`: the codec component's second value type.
//!
//! The protobuf zigzag map interleaves the signed range onto the unsigned one, so that values
//! clustered near zero in either direction encode short; the LEB128 work itself is delegated to
//! `crate::varint` rather than reimplemented. The Lean model (`FramedChannel.Zigzag`) is defined
//! over `FramedChannel.Varint.Leb128` through the same delegation, and retrieves its round trip
//! and its five-byte bound from that codec's own `CodecLaws` instance.

use crate::varint::{decode_u32, encode_u32, VarintError};

/// The protobuf zigzag map: interleave the signed range onto the unsigned one (Lean `zigzag`).
///
/// `n >> 31` is an arithmetic shift, so it is `0` for a non-negative `n` and `-1` otherwise; the
/// Lean model matches that arithmetically rather than as a logical shift.
pub fn zigzag(n: i32) -> u32 {
    ((n << 1) ^ (n >> 31)) as u32
}

/// The inverse of `zigzag` on the whole `u32` range (Lean `unzigzag`).
pub fn unzigzag(m: u32) -> i32 {
    let half = (m >> 1) as i32;
    if m & 1 == 0 {
        half
    } else {
        !half
    }
}

/// Append the zigzag LEB128 encoding of `n` to `out` (Lean `encode`).
pub fn encode_i32(n: i32, out: &mut Vec<u8>) {
    encode_u32(zigzag(n), out);
}

/// Decode one zigzag LEB128 value from the front of `bytes` (Lean `decode`); returns the value
/// and the number of bytes consumed.
///
/// # Errors
///
/// Returns the error `decode_u32` returns, unchanged: `Err(VarintError::Truncated)` if `bytes`
/// ends before a byte without the continuation bit, and `Err(VarintError::Overlong)` if more than
/// five bytes are present, or a fifth byte does not fit in the remaining four bits. The Lean
/// `decode` has no error type, only `.fail`.
pub fn decode_i32(bytes: &[u8]) -> Result<(i32, usize), VarintError> {
    match decode_u32(bytes) {
        Ok((m, k)) => Ok((unzigzag(m), k)),
        Err(e) => Err(e),
    }
}
