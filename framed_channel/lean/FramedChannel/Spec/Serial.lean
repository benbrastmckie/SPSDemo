-- SPDX-License-Identifier: Apache-2.0
/-!
# Spec/Serial: the serial-number interface, `SerialModel` (L0) and `SerialLaws` (L1)

The two-layer anatomy `Spec/Queue.lean` gives the queue, at RFC 1982 serial-number arithmetic:
operations and types in `SerialModel`, laws over the serial ordering in `SerialLaws`.

This is the one interface of the example whose operation shape fits none of `QueueModel`,
`CodecModel` or `ChecksumModel`: there is no container and no encode/decode pair, only a cyclic
space with a successor and a partial order-like comparison on it.

## Three design decisions, each load-bearing

**`lt` is `Bool`-valued, not `Prop`-valued**, following `QueueModel.full`/`empty` rather than
`CodecModel.Dom`. Every law is then decidable, which is what makes the kernel `decide` rung and
the kernel countermodel searches of `Evidence/Countermodels.lean` available at all. A `Prop`-valued
comparison would put both out of reach for the sake of notation.

**`defined` is a field, and it is why the totality law is honest.** RFC 1982 §3.2 leaves the
comparison *undefined* on a pair exactly half the space apart: neither number is serially before
the other. Totality therefore holds only on the defined region, and the condition has to be
expressible at the interface. `dist` and `half` are model-side (as `Crc8.table` is), so the
condition enters L0 as one extra `Bool`-valued operation rather than by widening `lt` -- which
would smuggle the side condition into the very relation the law is about. The canonical model
instantiates it as `dist a b != half`; `Evidence/Countermodels.lean` refutes the unguarded law, so
this hypothesis is demonstrably load-bearing rather than decorative.

**`iter` is *derived* from `succ`, not an L0 field.** `succ_cycles` needs "`succ` applied `space`
times", and this package has no Mathlib, where `Function.iterate`/`f^[n]` lives; core Lean at the
pinned toolchain has neither the notation nor `Nat.iterate`. The alternative -- an
`iter : Nat → S → S` field -- was rejected because it makes the law **vacuous**: nothing would tie
a free `iter` field to `succ`, so an instance could satisfy `succ_cycles` with `iter := fun _ n => n`
and say nothing about its successor at all. `SerialModel.iter` below is a definition over the `succ`
field, so the law it states is about `succ` by construction.

## What this interface deliberately does not require

**There is no transitivity field, and its absence is a refutation rather than an omission.** RFC
1982's serial comparison is not transitive: `lt 0 20000`, `lt 20000 40000` and `lt 40000 0` all
hold while `lt 0 40000` does not, a genuine three-cycle. The witness is kernel-checked in
`FramedChannel/Evidence/Countermodels.lean` (`lt_trans_cand`, refuted at `(0, 20000, 40000)`) and
recorded in `certificate/countermodels.txt`. A consumer that needs a transitive order must not
build it on this relation; a reader of this class alone must not read the missing field as an
oversight.

`succ_cycles` states the *return* after `space` steps, the half a consumer uses. That the cycle is
exactly `space` long -- no shorter -- is proved too, as the model theorem
`FramedChannel.SeqNum.iter_ne_of_pos_lt`, deliberately not as a law field: it constrains the model
rather than the consumer. `certificate/seq_num.yaml`'s `guarantees:` block records that split, so
the narrower class is a recorded choice and not a gap.
-/

namespace FramedChannel

/-- L0: the operations of a cyclic serial-number space over a representation `S`. Operations and
types only; `add` and `dist` are model-side, as `Crc8.table` is. -/
class SerialModel (S : Type) where
  /-- A distinguished starting point of the space. -/
  zero : S
  /-- The next number, wrapping at the top of the space. -/
  succ : S → S
  /-- Serial comparison: is the first number serially before the second? Not an order -- see the
  module docstring. -/
  lt : S → S → Bool
  /-- Whether `lt` is defined on this pair at all (RFC 1982 §3.2 leaves the exactly-half-space-apart
  case undefined). The hypothesis of `SerialLaws.lt_total_of_defined`. -/
  defined : S → S → Bool
  /-- The size of the sequence space: the number of `succ` steps that return to the start. -/
  space : Nat

/-- `succ` applied `k` times. A definition over the `succ` field, not a field of its own: see the
module docstring on why a free `iter` field would make `SerialLaws.succ_cycles` vacuous. -/
def SerialModel.iter {S : Type} [SerialModel S] : Nat → S → S
  | 0, n => n
  | k + 1, n => SerialModel.succ (SerialModel.iter (S := S) k n)

/-- L1: the laws serial-number arithmetic actually supports, stated through `lt` and `succ`.

Four fields, and **no transitivity**: see the module docstring, and
`FramedChannel/Evidence/Countermodels.lean` for the kernel-checked three-cycle that refutes it. -/
class SerialLaws (S : Type) [SerialModel S] : Prop where
  /-- No number is serially before itself. -/
  lt_irrefl : ∀ n : S, SerialModel.lt n n = false
  /-- The successor is always serially after its argument: the one step the comparison is
  guaranteed to see. -/
  lt_succ : ∀ n : S, SerialModel.lt n (SerialModel.succ n) = true
  /-- The space closes: `space` successor steps return to where they started. -/
  succ_cycles : ∀ n : S, SerialModel.iter (SerialModel.space (S := S)) n = n
  /-- Totality, on the defined region only: two distinct comparable numbers are ordered one way or
  the other. The `defined` hypothesis is not removable -- `Evidence/Countermodels.lean` refutes the
  unguarded statement at `32768`, half the space from `0`. -/
  lt_total_of_defined : ∀ a b : S, a ≠ b → SerialModel.defined a b = true →
    SerialModel.lt a b = true ∨ SerialModel.lt b a = true

end FramedChannel
