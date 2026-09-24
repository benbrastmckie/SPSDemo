// SPDX-License-Identifier: Apache-2.0
//! The composite: a loopback channel whose `send` writes one frame onto the wire and whose
//! `deliver` parses one frame off the wire and pushes it onto a bounded queue.
//!
//! The executable counterpart of `../../lean/FramedChannel/Composition/Channel.lean`, operation
//! for operation: `send` and `deliver` have the same guards, the same order of effects, and one
//! failure case each where the Lean model has `Result.fail`.
//!
//! `send = push ∘ checksum ∘ encode` reads, in these names, as `varint::encode_u32` then
//! `crc8::crc8` inside `encode_frame` at `send` time, then `BoundedQueue::push` at `deliver` time.
//! `push`'s `not full` assumption (Lean's `not_full_of_lt`) is discharged by `send`'s own capacity
//! check, `queued + in_flight < capacity`, which is why `deliver`'s push cannot fail on a frame
//! this channel sent; the Lean statement of that discharge is `Channel.send_discharges_not_full`.
//!
//! `Channel<Q>` is generic over any `Q: BoundedQueue<Frame>`, `RingBuffer<Frame>` by default, and
//! reaches the queue only through the trait -- the executable picture of substitution
//! `Channel[VecQueue/RingBuffer]`, matching the Lean `Chan Q` and its theorems, each proved from
//! the six laws alone.

use crate::crc8::crc8;
use crate::queue::BoundedQueue;
use crate::ring_buffer::{Full, RingBuffer};
use crate::varint::{decode_u32, encode_u32};

/// The frame boundary byte (Lean `Channel.marker`). `Channel` itself does not stuff: a `0x7E`
/// inside one of its frames (length bytes, payload, or check byte) is data, so the composite's
/// own framing offers no transparency. Byte stuffing is a separate unit -- see `crate::stuff`,
/// which owns its own `MARKER`/`ESC`/`XOR_MASK` and is not wired into `Channel`.
pub const MARKER: u8 = 0x7E;

/// One frame's payload, matching the Lean `Channel.Frame := List Byte`: a frame *is* its bytes.
pub type Frame = Vec<u8>;

/// The single failure case of `deliver`: either the wire does not begin with a complete,
/// well-formed frame, or the output queue refused the push. The Lean `deliver` collapses both
/// into one `Result.fail`, and so does this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeliverFail;

/// The single failure case of `send`: either `queued + in_flight >= capacity`, or the payload is
/// `2^32` bytes or more and its length does not fit the `u32` varint. The Lean `send` collapses
/// both refusals into one `Result.fail`, and so does this type. Either way the channel is left
/// untouched.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendFail;

/// One frame on the wire, as `Channel::send` writes it: marker, varint length, payload, CRC-8
/// of the payload. The Rust reading of Lean `Channel.encodeFrame`.
///
/// `len` is the payload length as a `u32`, which the caller obtains with `u32::try_from`, so a
/// payload of `2^32` bytes or more (outside Lean `Channel.FrameOK`) cannot reach this function.
/// `len` must equal `payload.len()`.
pub fn encode_frame(payload: &[u8], len: u32, out: &mut Vec<u8>) {
    out.push(MARKER);
    encode_u32(len, out);
    out.extend_from_slice(payload);
    out.push(crc8(payload));
}

/// Parse one frame off the front of `wire`: a marker, a varint length `n`, `n` payload bytes and
/// a check byte that must equal the CRC-8 of the payload. Returns the payload and the number of
/// bytes consumed, or `None` where the Lean `Channel.parseFrame` returns `.fail`. Every read goes
/// through `get`, so no path here can panic on an index.
#[must_use]
pub fn parse_frame(wire: &[u8]) -> Option<(Frame, usize)> {
    let (first, rest) = wire.split_first()?;
    if *first != MARKER {
        return None;
    }
    let Ok((n, used)) = decode_u32(rest) else {
        return None;
    };
    let n = n as usize;
    // `decode_u32` reported `used` bytes consumed from `rest`, so this slice always exists; it
    // goes through `get` because no expression in this crate indexes directly.
    let body = rest.get(used..)?;
    let payload: Frame = body.get(..n)?.to_vec();
    let check = *body.get(n)?;
    if check != crc8(&payload) {
        return None;
    }
    Some((payload, 1 + used + n + 1))
}

/// `bytes` without its first `n` bytes: the Lean `List.drop n`, empty when `n > bytes.len()`.
/// Reads through `get`, so it cannot panic.
fn drop_front(bytes: &[u8], n: usize) -> Vec<u8> {
    match bytes.get(n..) {
        Some(rest) => rest.to_vec(),
        None => Vec::new(),
    }
}

/// The Rust reading of Lean `Channel.Chan Q`: the output queue, the pending wire bytes, and the
/// number of frames sent but not yet delivered.
#[derive(Debug, Clone)]
pub struct Channel<Q = RingBuffer<Frame>> {
    out: Q,
    wire: Vec<u8>,
    in_flight: usize,
}

impl Channel<RingBuffer<Frame>> {
    /// A channel over the default queue, `RingBuffer<Frame>`. Kept alongside the generic
    /// `with_queue` because Rust cannot infer a struct's default type parameter in expression
    /// position (the `HashMap::new` pattern).
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Channel::with_queue(capacity)
    }
}

impl<Q: BoundedQueue<Frame>> Channel<Q> {
    /// A channel over any `Q: BoundedQueue<Frame>`.
    #[must_use]
    pub fn with_queue(capacity: usize) -> Self {
        Channel { out: Q::with_capacity(capacity), wire: Vec::new(), in_flight: 0 }
    }

    /// Lean `Channel.send`: refuse when `queued + in_flight >= capacity`, then refuse a payload
    /// of `2^32` bytes or more, else append the frame's encoding to the wire and count it in
    /// flight. The capacity refusal is the discharge of `BoundedQueue::push`'s `not full`
    /// assumption; the length refusal establishes `encode_frame`'s precondition (Lean
    /// `send_refuses_too_long`). Both refusals are `Err(SendFail)` and leave the channel untouched.
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
        encode_frame(payload, len, &mut self.wire);
        self.in_flight += 1;
        Ok(())
    }

    /// Lean `Channel.deliver`: parse one frame off the wire, push it onto the output queue, and
    /// decrement the in-flight count. Fails, leaving the channel untouched, exactly where the Lean
    /// model gives `.fail`.
    ///
    /// # Errors
    ///
    /// Returns `Err(DeliverFail)` when the wire does not begin with a complete, well-formed
    /// frame, or when the output queue refuses the push; the channel is left untouched either way.
    pub fn deliver(&mut self) -> Result<Frame, DeliverFail> {
        let Some((payload, used)) = parse_frame(&self.wire) else {
            return Err(DeliverFail);
        };
        match self.out.push(payload.clone()) {
            Ok(()) => {
                // Rebuilds the wire without the consumed prefix (one allocation per delivered
                // frame), which reads exactly as the Lean `wire.drop used`.
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
