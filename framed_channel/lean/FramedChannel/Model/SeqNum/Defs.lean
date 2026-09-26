-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Spec.Serial

/-!
# Model/SeqNum/Defs: the serial-number definitions

`[HAND-WRITTEN: model; bridged]` -- the definitions half of `Model/SeqNum/Theorems.lean`: half the
space, the modular distance, both spellings of RFC 1982 §3.2's comparison, the successor, the
bounded increment, the space size, the structural iterate, the defined-region predicate, the
component carrier `Serial` and its `SerialModel` instance. It holds definitions only, so that the
Challenge module `FramedChannelChallenge.SeqNum` can import them without importing a registered
theorem.

## Representation: `BitVec 16`, written literally at every binder

A sequence number is a `BitVec 16`, matching `Model/Crc8/Defs.lean`'s `BitVec 8` and **not** the
`Nat`-with-a-range-condition shape of `Varint` and `Stuff`. Wrapping is then definitional -- `BitVec`
`+` and `-` are already modulo `2 ^ 16` -- so there is no `% 65536` anywhere below, no
representation invariant to preserve, and the abstraction from the extracted `Std.U16` is an
equality of representations rather than a lossy projection. `certificate/seq_num.yaml`'s
`assumptions:` block records the rejected `Nat` alternative and why.

**There is deliberately no `abbrev`, `def` or `notation` synonym for the carrier, and every binder
below says `BitVec 16` literally.** This is a measured constraint, not a style preference: behind a
reducible synonym `bv_decide` abstracts `BitVec` subtraction as an opaque variable and then reports
a *spurious counterexample*, which reads as "the statement is false" rather than as a tactic
limitation. `lt_eq_ltRFC` in the proof module depends on that rung.

`Serial` is the carrier -- a one-field wrapper over `BitVec 16`, field for field the Rust newtype
`SeqNum { value: u16 }` -- because `SerialModel` is indexed by the representation, not by a
component tag the way `ChecksumModel` is. The registered theorems are all stated at `BitVec 16`
directly; `Serial` exists so that the interface instance has a carrier of its own and no instance is
declared on a core type.

## Rust to Lean mapping

| Rust `seq_num.rs`               | Lean                    |
|---------------------------------|-------------------------|
| `HALF: u16 = 0x8000`            | `half : BitVec 16`      |
| `SeqNum { value: u16 }`         | `Serial` (field `value`)|
| `SeqNum::succ`                  | `succ`                  |
| `SeqNum::add`                   | `add`                   |
| `SeqNum::dist`                  | `dist`                  |
| `SeqNum::lt`                    | `lt`                    |
| (no Rust counterpart)           | `ltRFC`, `iter`, `defined`, `space` |
-/

namespace FramedChannel.SeqNum

/-- Half the sequence space, `2 ^ 15`. A distance of exactly `half` is RFC 1982 §3.2's undefined
case. -/
def half : BitVec 16 := 0x8000#16

/-- The forward modular distance from `a` to `b`. Not symmetric: `dist a b` and `dist b a` sum to
`0` in the space. -/
def dist (a b : BitVec 16) : BitVec 16 := b - a

/-- Serial comparison, as the one modular-distance test real implementations use: `a` is serially
before `b` when the forward distance is nonzero and less than half the space. This is the spelling
the Rust `SeqNum::lt` has; `lt_eq_ltRFC` proves it agrees with `ltRFC` on every pair. -/
def lt (a b : BitVec 16) : Bool := 0#16 < dist a b && dist a b < half

/-- RFC 1982 §3.2 transcribed literally: `i1 < i2 and i2 - i1 < 2 ^ 15`, or
`i1 > i2 and i1 - i2 > 2 ^ 15`.

The RFC's requirement that the two numbers be distinct needs no conjunct of its own here: each
disjunct already carries a *strict* inequality between them (`a < b` in the first, `b < a` in the
second), so equal arguments satisfy neither. That redundancy was checked rather than assumed --
`lt_eq_ltRFC` compares this definition against `lt`, which refuses equal arguments through
`0#16 < dist a b`, on all `2 ^ 32` pairs. -/
def ltRFC (a b : BitVec 16) : Bool :=
  (a < b && b - a < half) || (b < a && half < a - b)

/-- The next sequence number, wrapping at the top of the space. -/
def succ (n : BitVec 16) : BitVec 16 := n + 1#16

/-- `n` advanced by `k`, wrapping. RFC 1982 §3.1 only *defines* the sum for `0 < k < 2 ^ 15`; the
operation is total, and that range is a condition on the claim `lt n (add n k)` (`lt_add`), not a
partiality of the arithmetic. -/
def add (n k : BitVec 16) : BitVec 16 := n + k

/-- The size of the sequence space, `2 ^ 16`. -/
def space : Nat := 65536

/-- `succ` applied `k` times, by structural recursion on `k`. The interface's own
`SerialModel.iter` is the same iteration over the `succ` field; `iter_serial` in the proof module
relates them. -/
def iter : Nat → BitVec 16 → BitVec 16
  | 0, n => n
  | k + 1, n => succ (iter k n)

/-- Whether §3.2's comparison is defined on this pair: false exactly on the pairs half the space
apart, where neither number is serially before the other. The hypothesis of
`lt_total_of_defined`, and the field `SerialModel.defined` is instantiated with. -/
def defined (a b : BitVec 16) : Bool := dist a b != half

/-- The component carrier: a 16-bit sequence number, field for field the Rust newtype
`SeqNum { value: u16 }`. -/
structure Serial where
  /-- The sequence number itself. -/
  value : BitVec 16

instance instSerialModel : SerialModel Serial where
  zero := ⟨0#16⟩
  succ := fun s => ⟨succ s.value⟩
  lt := fun a b => lt a.value b.value
  defined := fun a b => defined a.value b.value
  space := space

end FramedChannel.SeqNum
