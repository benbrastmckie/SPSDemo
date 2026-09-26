// SPDX-License-Identifier: Apache-2.0
//! The resynchronizing receive path: a receiver that accepts arbitrary bytes off the wire, scans
//! forward to the next HDLC flag, and either accepts the run it found as a frame or drops it and
//! resumes at the next flag.
//!
//! The executable counterpart of
//! `../../lean/FramedChannel/Composition/Receiver/Theorems.lean`, operation for operation.
//! `Receiver<Q>` is the counterpart of `StuffedChannel`'s `deliver` under corruption: where
//! `deliver` reads a wire its own `send` wrote and fails as a unit when that wire is malformed,
//! `feed` accepts *any* byte stream, keeps going, and counts what it could not parse.
//!
//! # Why this rests on stuffing
//!
//! Resynchronization is sound only because a stuffed body is marker-free (Lean
//! `FramedChannel.Stuff.stuff_marker_free`, and the composition-layer bundle's `body_flag_free`),
//! so a flag byte on the wire is unambiguously a frame boundary and never payload data.
//! `channel.rs`'s unstuffed framing cannot support this: `../../certificate/countermodels.txt`
//! records the negative half in the kernel, at a payload containing `0x7E`, where scan-to-flag
//! accepts a frame that was never sent. The flag therefore comes from `crate::stuff` only, never
//! from `channel::MARKER` -- the same deliberate separation `stuffed_channel.rs` records and
//! `../../certificate/stuff.yaml` justifies.
//!
//! # The acceptance test is `stuffed_channel::parse_stuffed`, not a second parser
//!
//! `finish_run` appends the flag to the buffered run and hands the result whole to
//! `stuffed_channel::parse_stuffed`. Because the run is flag-free by construction and exactly one
//! flag is appended, `unstuff` always stops at that appended flag, so `parse_stuffed`'s
//! "nothing left over" check *is* the run's own exactness check. There is no second run parser to
//! keep in step with the first, and the Lean `Receiver.acceptRun` is the same one-line reuse.
//!
//! # Termination
//!
//! `feed`'s loop is bounded by `bytes.len()`, a length already in hand, and its `i += 1` is
//! unconditional: every branch of the body advances, the rejected run included. That is the whole
//! termination argument, and it is what the extraction's measure
//! (`aeneas/FramedChannelAeneas/Bridge/Receiver/Loop.lean`) decreases on.
//!
//! # Standing limit
//!
//! A wire carrying no flag grows `self.buf` without bound. This is not a subset violation -- the
//! subset bounds *loops*, and this loop is bounded -- but it is a real limit, recorded in
//! `../../certificate/receiver.yaml`'s `not_claimed:` block with a bounded-buffer variant named as
//! future work.

use crate::channel::Frame;
use crate::queue::BoundedQueue;
use crate::ring_buffer::{Full, RingBuffer};
use crate::stuff::MARKER;
use crate::stuffed_channel::parse_stuffed;

/// The Rust reading of Lean `Receiver.Rcv Q`: the output queue of accepted frames, the bytes of
/// the run currently being scanned, and the number of runs dropped.
#[derive(Debug, Clone)]
pub struct Receiver<Q = RingBuffer<Frame>> {
    out: Q,
    buf: Vec<u8>,
    dropped: usize,
}

impl Receiver<RingBuffer<Frame>> {
    /// A receiver over the default queue, `RingBuffer<Frame>`. Kept alongside the generic
    /// `with_queue` because Rust cannot infer a struct's default type parameter in expression
    /// position (the `HashMap::new` pattern), exactly as `StuffedChannel::new` is.
    #[must_use]
    pub fn new(capacity: usize) -> Self {
        Receiver::with_queue(capacity)
    }
}

impl<Q: BoundedQueue<Frame>> Receiver<Q> {
    /// A receiver over any `Q: BoundedQueue<Frame>`.
    #[must_use]
    pub fn with_queue(capacity: usize) -> Self {
        Receiver { out: Q::with_capacity(capacity), buf: Vec::new(), dropped: 0 }
    }

    /// Lean `Receiver.feed`: feed arbitrary bytes off the wire, one byte at a time. A flag ends the
    /// current run and hands it to `finish_run`; any other byte is appended to the run. Bytes
    /// buffer across calls, which is what makes the chunking-invariance law
    /// `Receiver.feed_append` true: `feed(a ++ b)` and `feed(a); feed(b)` leave the same receiver.
    ///
    /// The loop is bounded by `bytes.len()` and `i` advances on every iteration.
    pub fn feed(&mut self, bytes: &[u8]) {
        let mut i: usize = 0;
        while i < bytes.len() {
            let b = match bytes.get(i) {
                Some(b) => *b,
                None => return,
            };
            if b == MARKER {
                self.finish_run();
            } else {
                self.buf.push(b);
            }
            i += 1;
        }
    }

    /// Lean `Receiver.finishRun`: the buffered run, terminated by a flag, either accepted as a
    /// frame or counted as a drop.
    ///
    /// An empty run is *idle*, not a drop: RFC 1662 §4.1 has two adjacent flags delimit an empty
    /// frame a conforming receiver ignores, and that early return is what makes the Lean law
    /// `Receiver.idle_flags` statable. A full-queue refusal counts as a drop, exactly as a
    /// malformed run does -- one rejected run, one increment, which is what keeps
    /// `Receiver.run_exactly_one` unconditional (the same conflation `DeliverFail` already makes).
    ///
    /// `saturating_add` rather than `+= 1`: a plain addition is an addition Aeneas requires not to
    /// overflow, which would put a `dropped < usize::MAX` hypothesis on every refinement triple.
    /// This mirrors `stuffed_channel.rs`'s `in_flight.saturating_sub(1)` and leaves `feed` with no
    /// arithmetic hypothesis at all.
    fn finish_run(&mut self) {
        if self.buf.is_empty() {
            return;
        }
        self.buf.push(MARKER);
        match parse_stuffed(&self.buf) {
            Some((payload, _used)) => match self.out.push(payload) {
                Ok(()) => {}
                Err(Full) => {
                    self.dropped = self.dropped.saturating_add(1);
                }
            },
            None => {
                self.dropped = self.dropped.saturating_add(1);
            }
        }
        // A fresh empty buffer rather than `clear()`: the Lean `buf := []`, and one fewer std
        // method for the extraction to model.
        self.buf = Vec::new();
    }

    /// Dequeue the oldest accepted frame (Lean `QueueModel.pop` on `c.out`).
    pub fn poll(&mut self) -> Option<Frame> {
        self.out.pop()
    }

    /// The number of runs dropped: malformed, or refused by a full queue (Lean `c.dropped`).
    pub fn dropped(&self) -> usize {
        self.dropped
    }

    /// The number of accepted frames waiting in the output queue (Lean
    /// `(QueueModel.toList c.out).length`).
    pub fn queued(&self) -> usize {
        self.out.len()
    }
}
