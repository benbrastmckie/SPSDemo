-- SPDX-License-Identifier: Apache-2.0
import FramedChannelChallenge.RingBuffer
import FramedChannelChallenge.VecQueue
import FramedChannelChallenge.Varint
import FramedChannelChallenge.Crc8
import FramedChannelChallenge.Channel

/-!
# FramedChannelChallenge: the core package's approved specification

The core package's statement-only Challenge library, and Comparator's `challenge_module` for it.
Each component module restates, with `:= sorry`, the registered theorems of
`lean/FramedChannel/Registry.lean` for that component: same names, and exactly the same elaborated
statements. The bridge package's library, `aeneas/FramedChannelAeneasChallenge.lean`, has the same
shape.

* **Approved source of truth.** The modules are maintained by hand and never regenerated from the
  proofs: the proofs are checked against them. Each module is approved with `approve.sh`, and
  `certificate/approvals.yaml` records its closure digest.
* **What the gate checks.** `check.sh` compares each statement hash with the registry column, and
  each module's closure digest (`SpecCheck.lean`) with its recorded approval.
* **Why `sorry`.** It is the Comparator statement form, not a deferred proof. The library is not a
  default build target, nothing in the proof packages or registries imports it, and `check.sh`
  accepts a `sorry` warning only for a declaration `SpecCheck.lean` confirms is a statement-only
  theorem of a Challenge module.
* **Imports** are limited to specification and definition modules (`Spec/`, the `Defs` modules and
  the extraction), so a module can mention every definition its statements need without importing
  a registered theorem. The one exception is the `shared-proof` rows of `certificate/policy.txt`,
  theorems a definition is built from, which are imported proved rather than restated.
-/
