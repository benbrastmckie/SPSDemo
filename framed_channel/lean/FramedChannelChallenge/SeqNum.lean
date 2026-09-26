-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Model.SeqNum.Defs

/-!
# FramedChannelChallenge.SeqNum: approved statements (RFC 1982 serial-number model)

Statement-only restatements of the registered theorems; the proofs are in
`lean/FramedChannel/Model/SeqNum/Theorems.lean`. See `lean/FramedChannelChallenge.lean` for what a
Challenge module is and what the gate checks.

**There is no transitivity statement here, and there is no `SerialLaws` field for one.** RFC 1982's
serial comparison is not transitive: `lean/FramedChannel/Evidence/Countermodels.lean` refutes it in
the kernel at `(0, 20000, 40000)`, a genuine three-cycle. A consumer needing a transitive order must
not build it on this relation.
-/

namespace FramedChannel.SeqNum

/-- No sequence number is serially before itself. One 16-bit variable, so the kernel decides all
65536 cases. -/
theorem lt_irrefl (n : BitVec 16) : lt n n = false := sorry

/-- Every sequence number is serially before its successor. -/
theorem lt_succ (n : BitVec 16) : lt n (succ n) = true := sorry

/-- The forward distance recovers the increment: `dist` is the left inverse of `add`. -/
theorem dist_add (n k : BitVec 16) : dist n (add n k) = k := sorry

/-- RFC 1982 §3.1's claim: advancing by a positive increment below half the space lands strictly
after where you started. Both hypotheses are needed -- `0#16 < k` because `add n 0 = n` is not
serially after `n`, and `k < half` because beyond half the space the comparison points the other
way. -/
theorem lt_add (n k : BitVec 16) (h0 : 0#16 < k) (hh : k < half) : lt n (add n k) = true := sorry

/-- RFC 1982 §3.2's two-case formula and the one-test distance form the Rust uses agree on every
pair. The registered proof takes the `bv_decide` rung, so this row is `verified := false` and
`certificate/policy.txt` declares it `flagged`; `lt_eq_ltRFC_kernel` below is its kernel replay. -/
theorem lt_eq_ltRFC (a b : BitVec 16) : ltRFC a b = lt a b := sorry

/-- The same statement, replayed in the kernel with no `bv_decide` and no compiler-trusting axiom.
Registered beside `lt_eq_ltRFC` rather than in place of it, as `Crc8.crc8_step_linear_kernel` is. -/
theorem lt_eq_ltRFC_kernel (a b : BitVec 16) : ltRFC a b = lt a b := sorry

/-- `space` successor steps return to where they started. -/
theorem iter_space (n : BitVec 16) : iter space n = n := sorry

/-- And no fewer: the cycle is *exactly* `space` long. The minimality half of "exactly `space`
steps", registered as a model theorem rather than made a `SerialLaws` field. -/
theorem iter_ne_of_pos_lt (k : Nat) (hk : 0 < k) (hks : k < space) (n : BitVec 16) :
    iter k n ≠ n := sorry

/-- Totality, on the defined region only. The `defined` hypothesis is not decoration:
`lt_total_cand` in `lean/FramedChannel/Evidence/Countermodels.lean` refutes the unguarded form at
`32768`, where the two numbers are exactly half the space apart. -/
theorem lt_total_of_defined (a b : BitVec 16) (hne : a ≠ b) (hd : defined a b = true) :
    lt a b = true ∨ lt b a = true := sorry

/-- Advancing both arguments leaves the comparison unchanged. This answers the §3.2 passage a reader
is most likely to misread: the remark that `s1 < s2` could coexist with `(s1 + 1) > (s2 + 1)` is
about a definition the RFC rejected, and this formulation does not have the defect. -/
theorem lt_translation_invariant (a b : BitVec 16) : lt (succ a) (succ b) = lt a b := sorry

/-- The refinement certificate as an interface instance: the canonical 16-bit model satisfies
exactly the four laws serial arithmetic supports, and no transitivity law, because there is none to
satisfy. -/
instance instSerialLaws : SerialLaws Serial := sorry

end FramedChannel.SeqNum
