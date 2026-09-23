// SPDX-License-Identifier: Apache-2.0
//! LEB128 unsigned varint for `u32`: the codec component.
//!
//! Both loops are bounded to five iterations, the maximum number of 7-bit groups in a `u32`;
//! the Lean model (`FramedChannel.Varint`) makes the same bound explicit as fuel `5`.

/// The error of `decode_u32`. The Lean `decode` has no error type, only `.fail`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarintError {
    /// The input ended before a byte without the continuation bit.
    Truncated,
    /// More than five bytes, or a fifth byte that does not fit in the remaining four bits.
    Overlong,
}

/// Append the LEB128 encoding of `n` to `out` (Lean `encode`).
pub fn encode_u32(mut n: u32, out: &mut Vec<u8>) {
    for _ in 0..5 {
        let group = (n & 0x7F) as u8;
        n >>= 7;
        if n == 0 {
            out.push(group);
            return;
        }
        out.push(group | 0x80);
    }
}

/// Decode one LEB128 value from the front of `bytes` (Lean `decode`); returns the value and
/// the number of bytes consumed.
///
/// # Errors
///
/// Returns `Err(VarintError::Truncated)` if `bytes` ends before a byte without the continuation
/// bit, and `Err(VarintError::Overlong)` if more than five bytes are present, or a fifth byte
/// does not fit in the remaining four bits.
pub fn decode_u32(bytes: &[u8]) -> Result<(u32, usize), VarintError> {
    let mut acc: u32 = 0;
    let mut shift: u32 = 0;
    for i in 0..5 {
        let b = match bytes.get(i) {
            Some(b) => *b,
            None => return Err(VarintError::Truncated),
        };
        let group = u32::from(b & 0x7F);
        if shift == 28 && group > 0x0F {
            return Err(VarintError::Overlong);
        }
        acc |= group << shift;
        if b & 0x80 == 0 {
            return Ok((acc, i + 1));
        }
        shift += 7;
    }
    Err(VarintError::Overlong)
}
