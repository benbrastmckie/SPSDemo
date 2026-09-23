-- SPDX-License-Identifier: Apache-2.0
/-!
# Spec/Result: the specification layer's failure monad

The one outcome type every L0 interface in `Spec/` is stated over: `.ok` for a success carrying a
value, `.fail` for the single refusal a bounded operation can report. It is deliberately smaller
than Aeneas's `Result` (no error payload, no divergence): the specification says *that* an
operation refuses, and the bridge layer (`aeneas/FramedChannelAeneas/Bridge/`) relates each
extracted carrier's own error shape to `.fail` rather than widening this type to fit one of them.
-/

namespace FramedChannel

/-- The specification layer's outcome: a value, or the single refusal. -/
inductive Result (α : Type) where
  | ok : α → Result α
  | fail : Result α
deriving DecidableEq

end FramedChannel
