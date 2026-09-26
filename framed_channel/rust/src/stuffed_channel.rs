// SPDX-License-Identifier: Apache-2.0
//! The transparent composite: a loopback channel whose `send` writes one frame onto the wire as
//! marker-free stuffed bytes and whose `deliver` reads one stuffed frame back off the wire and
//! pushes its payload onto a bounded queue.
//!
//! The executable counterpart of
//! `../../lean/FramedChannel/Composition/StuffedChannel/Theorems.lean`, operation for operation.
//! `StuffedChannel` is `Channel`'s transparent counterpart: where `Channel` writes a raw frame
//! behind a boundary byte, this one passes the whole frame body through `crate::stuff`, so no byte
//! of the body it writes is the HDLC flag. That is the property `Channel` cannot have, and the
//! Lean statement of it is `StuffedChannel.wire_flag_free_of_send`.
//!
//! The body is built exactly as `Channel`'s is -- `varint::encode_u32` of the payload length, the
//! payload, then `crc8::crc8` of the payload -- and is then handed whole to
//! `stuff::encode_frame`, which stuffs it and terminates it with the flag. `deliver` runs the same
//! three layers backwards: `stuff::unstuff` recovers the body and reports the bytes consumed,
//! `varint::decode_u32` reads the declared length, and the trailing byte must equal the CRC-8 of
//! the payload. The body carries no leading boundary byte: the terminating flag alone delimits a
//! frame, which is what makes the wire scannable.
//!
//! This module takes its flag only from `stuff`, never from `channel::MARKER`: the two constants
//! are deliberately separate (`../../certificate/stuff.yaml` records the duplication as
//! intentional) and nothing here claims they agree. The error and payload types *are* reused from
//! `channel`, because a second pair of one-field failure enums would add extraction candidates for
//! no formal gain.
//!
//! `StuffedChannel<Q>` is generic over any `Q: BoundedQueue<Frame>`, `RingBuffer<Frame>` by
//! default, and reaches the queue only through the trait -- the same substitution picture as
//! `Channel<Q>`, matching the Lean `SChan Q` and its theorems, each proved from the queue laws,
//! the codec interface and the checksum interface alone.

use crate::channel::{DeliverFail, Frame, SendFail};
use crate::crc8::crc8;
use crate::queue::BoundedQueue;
use crate::ring_buffer::{Full, RingBuffer};
use crate::stuff::{encode_frame as stuff_frame, unstuff};
use crate::varint::{decode_u32, encode_u32};

/// One frame's body, before stuffing: varint length, payload, CRC-8 of the payload. The Rust
/// reading of Lean `StuffedChannel.body`.
///
/// `len` is the payload length as a `u32`, which the caller obtains with `u32::try_from`, so a
/// payload of `2^32` bytes or more (outside Lean `Channel.FrameOK`) cannot reach this function.
/// `len` must equal `payload.len()`.
fn body(payload: &[u8], len: u32) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    encode_u32(len, &mut out);
    out.extend_from_slice(payload);
    out.push(crc8(payload));
    out
}

/// Append one stuffed frame to `out` (Lean `StuffedChannel.encodeStuffed`): the body of
/// `payload`, byte-stuffed, terminated by the HDLC flag. No byte written other than that
/// terminator is the flag.
pub fn encode_stuffed(payload: &[u8], len: u32, out: &mut Vec<u8>) {
    let frame = body(payload, len);
    stuff_frame(&frame, out);
}

/// Read one stuffed frame off the front of `wire` (Lean `StuffedChannel.parseStuffed`): unstuff to
/// the frame body, read the varint length `n`, take exactly `n` payload bytes and one check byte
/// that must equal the CRC-8 of the payload, with nothing left over. Returns the payload and the
/// number of wire bytes consumed, the terminating flag included, or `None` where the Lean
/// `parseStuffed` returns `.fail`. Every read goes through `get`, so no path here can panic on an
/// index.
#[must_use]
pub fn parse_stuffed(wire: &[u8]) -> Option<(Frame, usize)> {
    let Ok((frame, used)) = unstuff(wire) else {
        return None;
    };
    let Ok((n, consumed)) = decode_u32(&frame) else {
        return None;
    };
    let n = n as usize;
    // `decode_u32` reported `consumed` bytes read from `frame`, so this slice always exists; it
    // goes through `get` because no expression in this crate indexes directly.
    let rest = frame.get(consumed..)?;
    // Lean matches `bytes.drop n` against `[c]`: exactly the payload and one check byte remain.
    if rest.len() != n + 1 {
        return None;
    }
    let payload: Frame = rest.get(..n)?.to_vec();
    let check = *rest.get(n)?;
    if check != crc8(&payload) {
        return None;
    }
    Some((payload, used))
}

/// `bytes` without its first `n` bytes: the Lean `List.drop n`, empty when `n > bytes.len()`.
/// Reads through `get`, so it cannot panic.
fn drop_front(bytes: &[u8], n: usize) -> Vec<u8> {
    match bytes.get(n..) {
        Some(rest) => rest.to_vec(),
        None => Vec::new(),
    }
}

/// The Rust reading of Lean `StuffedChannel.SChan Q`: the output queue, the pending wire bytes,
/// and the number of frames sent but not yet delivered.
#[derive(Debug, Clone)]
pub struct StuffedChannel<Q = RingBuffer<Frame>> {
    out: Q,
    wire: Vec<u8>,
    in_flight: usize,
}

impl StuffedChannel<RingBuffer<Frame>> {
    /// A stuffed channel over the default queue, `RingBuffer<Frame>`. Kept alongside the generic
    /// `with_queue` because Rust cannot infer a struct's default type parameter in expression
    /// position (the `HashMap::new` pattern).
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        StuffedChannel::with_queue(capacity)
    }
}

impl<Q: BoundedQueue<Frame>> StuffedChannel<Q> {
    /// A stuffed channel over any `Q: BoundedQueue<Frame>`.
    #[must_use]
    pub fn with_queue(capacity: usize) -> Self {
        StuffedChannel { out: Q::with_capacity(capacity), wire: Vec::new(), in_flight: 0 }
    }

    /// Lean `StuffedChannel.send`: refuse when `queued + in_flight >= capacity`, then refuse a
    /// payload of `2^32` bytes or more, else append the frame's stuffed encoding to the wire and
    /// count it in flight. The capacity refusal is the discharge of `BoundedQueue::push`'s
    /// `not full` assumption (Lean `send_discharges_not_full`); the length refusal establishes
    /// `encode_stuffed`'s precondition (Lean `send_refuses_too_long`). Both refusals are
    /// `Err(SendFail)` and leave the channel untouched.
    ///
    /// # Errors
    ///
    /// Returns `Err(SendFail)` when `queued + in_flight >= capacity`, or when `payload.len()`
    /// does not fit a `u32`; the channel is left untouched either way.
    pub fn send(&mut self, payload: &[u8]) -> Result<(), SendFail> {
        if self.out.len() + self.in_flight >= self.out.capacity() {
            return Err(SendFail);
        }
        let Ok(len) = u32::try_from(payload.len()) else {
            return Err(SendFail);
        };
        encode_stuffed(payload, len, &mut self.wire);
        self.in_flight += 1;
        Ok(())
    }

    /// Lean `StuffedChannel.deliver`: read one stuffed frame off the wire, push its payload onto
    /// the output queue, and decrement the in-flight count. Fails, leaving the channel untouched,
    /// exactly where the Lean model gives `.fail`.
    ///
    /// # Errors
    ///
    /// Returns `Err(DeliverFail)` when the wire does not begin with a complete, well-formed
    /// stuffed frame, or when the output queue refuses the push; the channel is left untouched
    /// either way.
    pub fn deliver(&mut self) -> Result<Frame, DeliverFail> {
        let Some((payload, used)) = parse_stuffed(&self.wire) else {
            return Err(DeliverFail);
        };
        match self.out.push(payload.clone()) {
            Ok(()) => {
                // Rebuilds the wire without the consumed prefix (one allocation per delivered
                // frame), which reads exactly as the Lean residual `rest`.
                self.wire = drop_front(&self.wire, used);
                // Matches the Lean `inFlight - 1`, `Nat` subtraction truncating at zero.
                self.in_flight = self.in_flight.saturating_sub(1);
                Ok(payload)
            }
            Err(Full) => Err(DeliverFail),
        }
    }

    /// Dequeue the oldest delivered frame (Lean `QueueModel.pop` on `c.out`).
    pub fn take(&mut self) -> Option<Frame> {
        self.out.pop()
    }

    /// The number of frames waiting in the output queue (Lean `(QueueModel.toList c.out).length`).
    pub fn queued(&self) -> usize {
        self.out.len()
    }
}
