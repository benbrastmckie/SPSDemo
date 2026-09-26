// SPDX-License-Identifier: Apache-2.0
//! `BoundedQueue<T>`: the executable counterpart of the Lean interface `QueueModel` /
//! `BoundedQueueLaws` in `../../lean/FramedChannel/Spec/Queue.lean`.
//!
//! `QueueModel`'s six fields (`push`, `pop`, `toList`, `full`, `empty`, `capacity`) become this
//! trait's methods one for one, `toList` as `contents`. There is no proof engine on this side, so
//! the six laws of `BoundedQueueLaws` are not restated as Rust obligations; they are exercised for
//! every implementor by the generic harness `check_bounded_queue_laws` in `../tests/differential.rs`.
//!
//! Two implementors: `RingBuffer<T>` (`ring_buffer.rs`) and `VecQueue<T>` below, which mirrors
//! `Model/VecQueue/{Defs,Theorems}.lean`'s `VQ α` field for field.

use crate::ring_buffer::Full;

/// The operations of Lean's `QueueModel`, constrained by the laws of `BoundedQueueLaws`.
pub trait BoundedQueue<T> {
    /// A queue of capacity `cap` (Lean `QueueModel.capacity` at construction).
    fn with_capacity(cap: usize) -> Self;

    /// Lean `QueueModel.capacity`; constrained by `push_capacity` (unchanged by `push`).
    fn capacity(&self) -> usize;

    /// The element count (`QueueModel.toList`'s length).
    fn len(&self) -> usize;

    /// Lean `QueueModel.empty`; constrained by `empty_law` (empty implies `pop` fails).
    fn is_empty(&self) -> bool;

    /// Lean `QueueModel.full`; constrained by `full_law` (full implies `push` fails) and
    /// `not_full_of_lt` (`len < capacity` implies not full).
    fn is_full(&self) -> bool;

    /// Lean `QueueModel.push`; constrained by `push_law` (not full implies success and
    /// `contents' == contents ++ [x]`) and `full_law` (full implies failure).
    ///
    /// # Errors
    ///
    /// Returns `Err(Full)` when the queue is at capacity (`is_full()`); the queue is left
    /// unchanged.
    fn push(&mut self, x: T) -> Result<(), Full>;

    /// Lean `QueueModel.pop`; constrained by `pop_law` (not empty implies success and the front
    /// element removed) and `empty_law` (empty implies failure).
    fn pop(&mut self) -> Option<T>;

    /// The abstraction function, Lean `QueueModel.toList`: the logical FIFO sequence.
    fn contents(&self) -> Vec<T>;
}

/// A list-backed bounded queue: field for field the Lean `VQ α` (`items : List α`, `cap : Nat`).
/// No invariant subtype is needed (contrast `RingBuffer`): `push` refuses once
/// `self.cap <= self.items.len()`, so every value reachable by `push` respects the bound.
#[derive(Debug, Clone)]
pub struct VecQueue<T> {
    items: Vec<T>,
    cap: usize,
}

impl<T: Clone> VecQueue<T> {
    /// A queue of capacity `cap`. Lean `VQ` carries no `0 < cap` invariant, so unlike
    /// `RingBuffer::with_capacity` a zero capacity is not rounded up here -- the one recorded
    /// difference between the queues.
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        VecQueue { items: Vec::new(), cap }
    }

    /// The bound (Lean `cap`).
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// The element count (Lean `items.length`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// Lean `empty` (`items.isEmpty`, which is `items.length = 0`). Spelled through `len` so the
    /// extraction needs only modelled library functions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Lean `full` (`cap <= items.length`): the same bound `push` tests.
    #[must_use]
    pub fn is_full(&self) -> bool {
        self.cap <= self.items.len()
    }

    /// Lean `VQ.push`: fail once the bound is reached, else append at the back.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full)` once `cap <= items.len()`; the queue is left unchanged.
    pub fn push(&mut self, x: T) -> Result<(), Full> {
        if self.cap <= self.items.len() {
            return Err(Full);
        }
        self.items.push(x);
        Ok(())
    }

    /// Lean `VQ.pop`: fail when empty, else remove from the front. Guarded on `is_empty` first,
    /// so `remove(0)` never panics (`Vec::remove` panics only when `index >= len`).
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }
    }

    /// The abstraction function (Lean `toList`): here the representation itself, already the
    /// logical FIFO sequence.
    #[must_use]
    pub fn contents(&self) -> Vec<T> {
        self.items.clone()
    }
}

impl<T: Clone> BoundedQueue<T> for VecQueue<T> {
    fn with_capacity(cap: usize) -> Self {
        VecQueue::with_capacity(cap)
    }

    fn capacity(&self) -> usize {
        VecQueue::capacity(self)
    }

    fn len(&self) -> usize {
        VecQueue::len(self)
    }

    fn is_empty(&self) -> bool {
        VecQueue::is_empty(self)
    }

    fn is_full(&self) -> bool {
        VecQueue::is_full(self)
    }

    fn push(&mut self, x: T) -> Result<(), Full> {
        VecQueue::push(self, x)
    }

    fn pop(&mut self) -> Option<T> {
        VecQueue::pop(self)
    }

    fn contents(&self) -> Vec<T> {
        VecQueue::contents(self)
    }
}
