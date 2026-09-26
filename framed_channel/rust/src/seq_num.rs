// SPDX-License-Identifier: Apache-2.0
//! RFC 1982 serial-number arithmetic over a 16-bit sequence space: the sequence-number component.
//!
//! A `SeqNum` is a point of the cyclic space `Z/2^16` (the Lean model's `space = 65536`). Every
//! operation is modulo `2^16` and **wraps**, written with the explicit `wrapping_` methods: the
//! Charon/Aeneas extraction models plain `+`/`-` as a panic on overflow, so a silently wrapping
//! release build would diverge from the model, and `wrapping_add`/`wrapping_sub` are the only
//! spelling that means the same thing in both.
//!
//! `lt` is RFC 1982 §3.2's serial comparison, written as the one modular-distance test real
//! implementations use rather than the RFC's two-case formula. The two spellings are not asserted
//! to agree: the Lean model carries the literal §3.2 transcription as `ltRFC` beside this one as
//! `lt`, and `FramedChannel.SeqNum.lt_eq_ltRFC` proves they agree on every pair.
//!
//! **`lt` is not transitive, and that is a property of RFC 1982, not a defect here.** There are
//! triples with `a < b`, `b < c` and `c < a`; `lt(0, 20000)`, `lt(20000, 40000)` and
//! `lt(40000, 0)` are all true while `lt(0, 40000)` is false. The refutation is kernel-checked in
//! `../../lean/FramedChannel/Evidence/Countermodels.lean`, which is why the Lean `SerialLaws`
//! class has no transitivity field. Do not build an ordering, a sort or a `BTreeMap` key on this
//! relation.
//!
//! §3.2 also leaves the comparison **undefined** when the two numbers are exactly half the space
//! apart: `lt(0, 0x8000)` and `lt(0x8000, 0)` are both false, so neither is serially before the
//! other. That side condition -- `dist(a, b) != 0x8000` -- is the hypothesis of the Lean totality
//! law `lt_total_of_defined`; it is stated over `dist`, so this module needs no operation for it.
//!
//! Lean model: `../../lean/FramedChannel/Model/SeqNum/{Defs,Theorems}.lean`
//! (`FramedChannel.SeqNum`); interface `../../lean/FramedChannel/Spec/Serial.lean`.

/// Half the sequence space (Lean `half`). A distance of exactly `HALF` is §3.2's undefined case.
const HALF: u16 = 0x8000;

/// A 16-bit sequence number: a point of the cyclic space `Z/2^16` (Lean `BitVec 16`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SeqNum {
    value: u16,
}

impl SeqNum {
    /// The sequence number with this wire value.
    #[must_use]
    pub fn new(value: u16) -> Self {
        SeqNum { value }
    }

    /// The wire value (Lean: the `BitVec 16` itself).
    #[must_use]
    pub fn get(self) -> u16 {
        self.value
    }

    /// The next sequence number, wrapping past the top of the space (Lean `succ`).
    #[must_use]
    pub fn succ(self) -> Self {
        SeqNum { value: self.value.wrapping_add(1) }
    }

    /// This number advanced by `n`, wrapping (Lean `add`). RFC 1982 §3.1 only *defines* the sum
    /// for `0 < n < 2^15`; the operation itself is total, and the range is a condition on the
    /// claim `self < self.add(n)` (Lean `lt_add`), not a partiality of the arithmetic.
    ///
    /// Deliberately not a `std::ops::Add` impl: serial addition is asymmetric in its operand types
    /// (`SeqNum + u16`, never `SeqNum + SeqNum`) and a trait impl would put a dispatch in the
    /// extraction that this unit has no use for. The name matches the Lean `add`.
    #[allow(clippy::should_implement_trait)]
    #[must_use]
    pub fn add(self, n: u16) -> Self {
        SeqNum { value: self.value.wrapping_add(n) }
    }

    /// The forward distance from `self` to `other`, wrapping (Lean `dist`). Not symmetric:
    /// `dist(a, b)` and `dist(b, a)` sum to `0` modulo the space.
    #[must_use]
    pub fn dist(self, other: Self) -> u16 {
        other.value.wrapping_sub(self.value)
    }

    /// RFC 1982 §3.2's serial comparison: is `self` serially before `other`? (Lean `lt`.)
    ///
    /// Not transitive, and not total -- see the module header.
    #[must_use]
    pub fn lt(self, other: Self) -> bool {
        let d = other.value.wrapping_sub(self.value);
        d != 0 && d < HALF
    }
}
