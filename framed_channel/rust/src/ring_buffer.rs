// SPDX-License-Identifier: Apache-2.0
//! Bounded FIFO over a `Vec<T>`: the fully worked component, and the Rust picture of the Lean
//! `RingBuffer.BQ` refinement instance.
//!
//! Field for field the Lean model `FramedChannel.RingBuffer` (`buf`, `head`, `tail`, `len`). The
//! representation invariant is `0 < cap`, `len <= cap`, `head < cap`, `tail == (head + len) % cap`
//! with `cap == buf.len()`. `buf` is indexed only through the checked helpers `get` and `set`, so
//! no path can panic on an index.
//!
//! This is the safe core. A production ring buffer (`VecDeque`, `heapless::spsc`) keeps an
//! `unsafe`/`MaybeUninit` interior, which would enter through the verifiable-core / trusted-shell
//! split as a listed assumption; see `../../certificate/ring_buffer_push.yaml`.

use crate::queue::BoundedQueue;

/// The error of `push` on a full buffer (Lean `Result.fail`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full;

/// A `Vec`-backed ring buffer: field for field the Lean `RingBuffer` (`buf`, `head`, `tail`,
/// `len`). The capacity is `buf.len()`; the invariant is stated above.
#[derive(Debug, Clone)]
pub struct RingBuffer<T: Default + Clone> {
    buf: Vec<T>,
    head: usize,
    tail: usize,
    len: usize,
}

impl<T: Default + Clone> RingBuffer<T> {
    /// A buffer of capacity `cap`; a zero capacity is rounded up to one so that `0 < cap`.
    #[must_use]
    pub fn with_capacity(cap: usize) -> Self {
        let cap = if cap == 0 { 1 } else { cap };
        RingBuffer { buf: vec![T::default(); cap], head: 0, tail: 0, len: 0 }
    }

    /// The capacity (Lean `buf.length`).
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// The element count (Lean `len`).
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Lean `empty` (`len == 0`).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Lean `full` (`len == buf.length`): the same bound `push` tests.
    #[must_use]
    pub fn is_full(&self) -> bool {
        self.len == self.buf.len()
    }

    /// Checked read (Lean `buf.getD i default`): the only place `buf` is read by index.
    fn get(&self, i: usize) -> T {
        match self.buf.get(i) {
            Some(v) => v.clone(),
            None => T::default(),
        }
    }

    /// Checked write (Lean `buf.set i x`): the only place `buf` is written by index.
    fn set(&mut self, i: usize, x: T) {
        if let Some(slot) = self.buf.get_mut(i) {
            *slot = x;
        }
    }

    /// Lean `push`: fail when full, else write at `tail`, advance it modulo capacity, and
    /// increment the count.
    ///
    /// # Errors
    ///
    /// Returns `Err(Full)` once `len == buf.len()`; the buffer is left unchanged.
    pub fn push(&mut self, x: T) -> Result<(), Full> {
        if self.len == self.buf.len() {
            return Err(Full);
        }
        let cap = self.buf.len();
        self.set(self.tail, x);
        self.tail = (self.tail + 1) % cap;
        self.len += 1;
        Ok(())
    }

    /// Lean `pop`: fail when empty, else read at `head`, advance it modulo capacity, and
    /// decrement the count.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let cap = self.buf.len();
        let x = self.get(self.head);
        self.head = (self.head + 1) % cap;
        self.len -= 1;
        Some(x)
    }

    /// The abstraction function (Lean `contents`, the interface's `toList`): the logical FIFO
    /// sequence, read as a `len`-window from `head` modulo the capacity.
    #[must_use]
    pub fn contents(&self) -> Vec<T> {
        let mut out = Vec::new();
        let cap = self.buf.len();
        for i in 0..self.len {
            out.push(self.get((self.head + i) % cap));
        }
        out
    }
}

impl<T: Default + Clone> BoundedQueue<T> for RingBuffer<T> {
    fn with_capacity(cap: usize) -> Self {
        RingBuffer::with_capacity(cap)
    }

    fn capacity(&self) -> usize {
        RingBuffer::capacity(self)
    }

    fn len(&self) -> usize {
        RingBuffer::len(self)
    }

    fn is_empty(&self) -> bool {
        RingBuffer::is_empty(self)
    }

    fn is_full(&self) -> bool {
        RingBuffer::is_full(self)
    }

    fn push(&mut self, x: T) -> Result<(), Full> {
        RingBuffer::push(self, x)
    }

    fn pop(&mut self) -> Option<T> {
        RingBuffer::pop(self)
    }

    fn contents(&self) -> Vec<T> {
        RingBuffer::contents(self)
    }
}
