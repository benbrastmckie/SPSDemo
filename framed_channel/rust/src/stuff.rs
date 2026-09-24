// SPDX-License-Identifier: Apache-2.0
//! HDLC-style byte stuffing (RFC 1662 asynchronous framing): the transparency component.
//!
//! `stuff` makes a payload marker-free by escaping the two bytes that cannot appear raw on the
//! wire, `encode_frame` appends the terminating flag, and `unstuff` reads one stuffed frame back.
//! The Lean model (`FramedChannel.Stuff`) proves the marker-free invariant
//! (`stuff_marker_free`), the round trip (`stuff_roundtrip`) and the length bound
//! (`stuff_length_le`) that this module's loops realize.
//!
//! The constants are declared here rather than taken from `channel.rs`: `channel::MARKER` is the
//! composite's own frame boundary and `Channel` does not stuff, so the duplication is intentional
//! and is recorded in `../../certificate/stuff.yaml`.
//!
//! Both loops are bounded by the length of the slice already in hand, and every slice read goes
//! through `get`.

/// The frame boundary byte, the HDLC flag (Lean `Stuff.marker`). Never appears inside a stuffed
/// payload, which is what makes `unstuff`'s scan-to-flag unambiguous.
pub const MARKER: u8 = 0x7E;

/// The escape byte (Lean `Stuff.esc`). Introduces a two-byte escape sequence.
pub const ESC: u8 = 0x7D;

/// The transparency mask (Lean `Stuff.xorMask`): an escaped byte is sent xor `0x20`, so
/// `0x7E -> 0x7D 0x5E` and `0x7D -> 0x7D 0x5D`.
pub const XOR_MASK: u8 = 0x20;

/// The error of `unstuff`. The Lean `unstuff` has no error type, only `.fail`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnstuffError {
    /// The wire ended without a terminating marker, or ended inside an escape sequence.
    Truncated,
    /// An escape byte was followed by something other than `MARKER ^ XOR_MASK` or
    /// `ESC ^ XOR_MASK`.
    BadEscape,
}

/// Append the byte-stuffed form of `payload` to `out` (Lean `stuff`).
///
/// Each `MARKER` or `ESC` byte becomes `ESC` followed by the byte xor `XOR_MASK`; every other
/// byte is copied through. The result never contains `MARKER`, so at most `2 * payload.len()`
/// bytes are appended (Lean `stuff_length_le`).
pub fn stuff(payload: &[u8], out: &mut Vec<u8>) {
    let mut i: usize = 0;
    while i < payload.len() {
        let b = match payload.get(i) {
            Some(b) => *b,
            None => return,
        };
        if b == MARKER || b == ESC {
            out.push(ESC);
            out.push(b ^ XOR_MASK);
        } else {
            out.push(b);
        }
        i += 1;
    }
}

/// Append the stuffed payload followed by the terminating flag to `out` (Lean `encode`).
///
/// The trailing flag is what makes the codec self-delimiting, so `unstuff` can report the
/// residual bytes after the frame it read.
pub fn encode_frame(payload: &[u8], out: &mut Vec<u8>) {
    stuff(payload, out);
    out.push(MARKER);
}

/// Read one stuffed frame off the front of `wire` (Lean `decode`); returns the unstuffed payload
/// and the number of bytes consumed, the terminating flag included.
///
/// # Errors
///
/// Returns `Err(UnstuffError::Truncated)` when `wire` ends without a terminating `MARKER`, or
/// ends immediately after an `ESC`, and `Err(UnstuffError::BadEscape)` when an `ESC` is followed
/// by a byte that is neither `MARKER ^ XOR_MASK` nor `ESC ^ XOR_MASK`.
pub fn unstuff(wire: &[u8]) -> Result<(Vec<u8>, usize), UnstuffError> {
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < wire.len() {
        let b = match wire.get(i) {
            Some(b) => *b,
            None => return Err(UnstuffError::Truncated),
        };
        if b == MARKER {
            return Ok((out, i + 1));
        }
        if b == ESC {
            let c = match wire.get(i + 1) {
                Some(c) => *c,
                None => return Err(UnstuffError::Truncated),
            };
            if c != MARKER ^ XOR_MASK && c != ESC ^ XOR_MASK {
                return Err(UnstuffError::BadEscape);
            }
            out.push(c ^ XOR_MASK);
            i += 2;
        } else {
            out.push(b);
            i += 1;
        }
    }
    Err(UnstuffError::Truncated)
}
