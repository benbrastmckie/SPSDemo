// SPDX-License-Identifier: Apache-2.0
//! `framed_channel`: a container, a codec, a checksum, and the glue that composes them.
//!
//! The subset is safe, sequential Rust: no `unsafe`, no `unwrap`, no trait objects, no closures
//! in `src/`, every slice read through `get`, every loop bounded. Generics with trait bounds are
//! permitted and are the point of the example. Index arithmetic matches the Lean models under
//! `../lean/FramedChannel/`.
//!
//! `BoundedQueue<T>` (`queue.rs`) is the executable counterpart of the Lean `QueueModel` /
//! `BoundedQueueLaws` classes. It has two implementations, `RingBuffer<T>` and `VecQueue<T>`, and
//! `Channel` is generic over any `Q: BoundedQueue<Frame>` -- `RingBuffer<Frame>` by default.
#![forbid(unsafe_code)]

pub mod channel;
pub mod crc8;
pub mod queue;
pub mod ring_buffer;
pub mod seq_num;
pub mod stuff;
pub mod stuffed_channel;
pub mod varint;
pub mod zigzag;

pub use channel::{Channel, DeliverFail, Frame, SendFail, MARKER};
pub use queue::{BoundedQueue, VecQueue};
pub use ring_buffer::{Full, RingBuffer};
pub use seq_num::SeqNum;
pub use stuffed_channel::StuffedChannel;
