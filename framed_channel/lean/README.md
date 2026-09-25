# lean/

The core Lake package of the worked example: specifications, hand-written models, the composite
channel, the core registry and the core Challenge library. It builds against core Lean and its
bundled `Std` alone, with no network access.

```
lake build                          every module of the default library
lake build FramedChannel.Model.Crc8.Theorems one module and its dependencies
lake build FramedChannelChallenge   the statement-only specification library (not a default
                                    target; one `sorry` warning per restated theorem, by design)
```

`../check.sh` wraps `lake build` in the full gate; see `../certificate/README.md`, "What the gate
enforces".

## The Lake project

`lakefile.toml` declares two libraries and **no `require` directive**. The default library,
`FramedChannel`, sets `autoImplicit = false`; it uses `Std.Tactic.BVDecide` for the one bit-vector
obligation and `import Lean` for the three modules with elaborators (`Certify`, `SpecCheck`,
`Ladder`). `FramedChannelChallenge` is the approved, statement-only specification (see below). The
package builds no executable: the differential vectors come from evaluating the extraction in
`../aeneas/`.

## The layout rule

Both Lake packages in this example follow one rule, and each new component should be copied from
the rule rather than from whichever file it happens to look at first.

**A unit layer holds one directory per unit: `<Layer>/<Unit>/`.** `Model/` and `Composition/`
here, `Bridge/` in `../aeneas`, are unit layers. There is no `<Unit>.lean` beside a `<Unit>/`
directory, and no flat unit module inside one.

- **`<Unit>/Defs.lean` is the unit's first module**: definitions only -- the representation, its
  invariant where it has one, the operations, the interface instance -- and it is the only module
  of that unit a Challenge module may import. `../check.sh`'s allow-only layer rule enforces
  exactly this, by an exact match on the last name component `Defs`, so a module named `FooDefs`
  is NOT a definitions module to the gate.
- **Proof modules are named for what they prove.** A unit whose proofs fit in one module names it
  `Theorems.lean`; a unit that splits them names each part (`Varint/{Encode,Decode}.lean`,
  `Crc8/{Bitwise,Table}.lean`, `Channel/{Abstraction,Frame,Refinement,Composite}.lean`) and ends
  at `Instance.lean`, which is where the interface instance on the extracted or composed carrier
  is built.
- **`Spec/` is not a unit layer.** It is one flat module per interface (`Spec/Queue.lean`,
  `Spec/Codec.lean`, `Spec/Checksum.lean`): an interface is not a unit, and nothing is proved
  about it.
- **A flat module directly under a unit layer means package-level infrastructure**, never a unit.
  `../aeneas`'s `Bridge/Std.lean` is the only such module in the example, and its own header says
  why.
- **`Composition/<Unit>/Instances.lean` is deliberately outside the composition layer's
  forbidden-import rule.** Instantiating the generic composition AT a queue model is that module's
  job, so it is the one composition module allowed to import one. `../check.sh`'s rule comment
  says so, and `../tests/layer/run.sh` pins both halves of it.

The unit's canonical name is fixed separately, by the name-mapping table in `../README.md`.

## Modules

The library is layered, and `../check.sh`'s layer import rule fails the run on a forbidden edge.

```
┌───────────────────────────────────────────────────────────────────┐
│ Registry.lean            rows, statement hashes, the core bank    │
│ Certify.lean             the scoring bank and register%           │
└──────────────────────────────┬────────────────────────────────────┘
                               │ registers theorems of
┌──────────────────────────────┴────────────────────────────────────┐
│ Composition/  Channel/Defs.lean (definitions),                    │
│               Channel/Theorems.lean (generic theorems),           │
│               Channel/Instances.lean (BQ and VQ)                  │
└──────────────────────────────┬────────────────────────────────────┘
                               │ Channel/Theorems.lean imports Ladder,
                               │ Channel/Defs, Varint and Crc8, but no queue
                               │ model; Channel/Instances.lean also imports
                               │ the models
┌──────────────────────────────┴────────────────────────────────────┐
│ Model/        <X>/Theorems.lean (theorems) and <X>/Defs.lean      │
│               (definitions), for RingBuffer, VecQueue, Varint     │
│               and Crc8: reference models, interface instances     │
└──────────────────────────────┬────────────────────────────────────┘
                               │ instantiate
┌──────────────────────────────┴────────────────────────────────────┐
│ Spec/         Result, Queue, Codec, Checksum                      │
│               L0 interfaces and L1 laws classes; no model         │
└───────────────────────────────────────────────────────────────────┘
```

**Definitions and theorems are split.** Each model and the composite keep their definitions in a
`Defs` module (`Model/<X>/Defs.lean`, `Composition/Channel/Defs.lean`) that the theorem module
imports, so the Challenge library can import every definition a registered statement mentions
without importing the theorem it restates. The one exception is `RingBuffer.push_inv`/`pop_inv`
(with the `inv_preserve` tactic that proves `pop_inv`): `pushBQ` and `popBQ` build the invariant
subtype from them, so they live, proved, in `Model/RingBuffer/Defs.lean`, as the `shared-proof`
rows of `../certificate/policy.txt`.

### Specification layer: `FramedChannel/Spec/`

The interfaces the models instantiate and the extraction is bridged to. No module here names an
implementation.

- **`Result.lean`**: `FramedChannel.Result`, `.ok` or the single `.fail`. The laws are stated over
  it, not over any carrier's own error shape.
- **`Queue.lean`**: `QueueModel` (L0: `push`, `pop`, `toList`, `full`, `empty`, `capacity`) and
  `BoundedQueueLaws` (L1: `push_law`, `pop_law`, `full_law`, `empty_law`, `not_full_of_lt`,
  `push_capacity`).
- **`Codec.lean`**: `CodecModel` (L0: `encode`, `decode`, `maxLen`, `Dom`) and `CodecLaws` (L1:
  `round_trip`, `length_le`).
- **`Checksum.lean`**: `ChecksumModel` (L0: `step`, `seed`, `digest`) and `ChecksumLaws` (L1:
  `digest_nil`, `digest_snoc`).

### Model layer: `FramedChannel/Model/`

Hand-written reference models in the shape the Aeneas Lean backend produces, each with its
interface instance, tagged `[HAND-WRITTEN: model; bridged]`. They are the abstraction targets the
bridge proves the extraction against, and the canonical non-vacuous instances of the laws. Each
component is one directory, splitting into `<X>/Theorems.lean` (the theorems below) and
`<X>/Defs.lean` (definitions only:
the representation, its invariant where it has one, the operations and the interface instance) --
`RingBuffer/Defs.lean`, `VecQueue/Defs.lean`, `Varint/Defs.lean`, `Crc8/Defs.lean` -- so the
Challenge module for that component can import definitions without importing a registered
theorem. `RingBuffer/Defs.lean` is the one exception documented in its own header: `pushBQ` and
`popBQ` build the invariant subtype with `push_inv` and `pop_inv`, so those two theorems (and the
`inv_preserve` seed tactic `pop_inv` is proved by) live there instead of in
`RingBuffer/Theorems.lean`.

- **`RingBuffer/Theorems.lean`**: the fully worked component. The `RingBuffer` structure with
  invariant `Inv`, abstraction function `contents`, `push` and `pop`; error agreement
  (`push_ok`/`push_fail`, `pop_ok`/`pop_fail`), invariant preservation (`push_inv`, `pop_inv`),
  refinement (`push_contents`, `pop_contents`), the `push_spec`/`pop_spec` existential specs, the
  lemma `idx_ne` and the bound `push_bounded`; then the `BoundedQueueLaws` instance on the invariant
  subtype `BQ α := { r // r.Inv }`. Two tactics -- `inv_preserve`, defined in
  `RingBuffer/Defs.lean`, and `refine_commute` -- replay the `push` scripts at `pop`; the "Seed
  tactics" section mid-file has the measured reuse table.
- **`VecQueue/Theorems.lean`**: a list-backed bounded queue `VQ`, its six-law instance and
  `push_bounded`. The second queue instance, without which substitution has nothing to substitute.
  Rust counterpart: `VecQueue<T>`.
- **`Varint/Theorems.lean`**: LEB128 for `u32`, both loops structurally recursive on explicit fuel
  `5`. `varint_roundtrip` for every `n < 2 ^ 32` and `encode_length_le` (at most five bytes), both
  closed by `grind` over the definitions, and the `CodecLaws` instance on the tag `Leb128`. The
  bound is a hypothesis because the unconditional form is false: `encodeF 5` emits a sixth byte once
  `n ≥ 128 ^ 5`.
- **`Crc8/Theorems.lean`**: CRC-8 with polynomial `0x07`, bytes as `BitVec 8`. `crc8_table_eq_bits`
  (the 256-entry table agrees with the bitwise loop, via a per-entry lemma closed by kernel
  `decide`), `stepTable_index_in_range`, and two `ChecksumLaws` instances, `Bitwise` and `Tabled`.
  `crc8_step_linear` is the example's one compiler-trusting declaration: proved by `bv_decide`,
  tagged `[PROVED: compiler-trusting]`, registered with `verified := false`, and the single entry on
  the flagged allow-list. `crc8_step_linear_kernel` proves the same statement in the kernel.

### Composition layer: `FramedChannel/Composition/`

- **`Channel/Defs.lean`**: the definitions half of `Channel/Theorems.lean` -- the wire format
  (`marker`, `lenBytes`, `encodeFrame`, `encodeFrameTable`, `parseFrame`), the delivered domain
  `FrameOK`, the `FrameCarrier` class and its identity instance, the channel state `Chan`, its
  operations `send` and `deliver`, and the invariant `ChanInv`. Definitions only (imports no queue
  model either), so the Challenge module can import it without importing a registered theorem.
- **`Channel/Theorems.lean`**: the composite, generic over its queue element `E` through
  `FrameCarrier E` and over any `[QueueModel Q E] [BoundedQueueLaws Q E]`.
  `encodeFrame`/`parseFrame` with `parseFrame_encodeFrame` and `encodeFrameTable_eq`; `Chan Q` with
  `send` (a capacity guard, then a guard refusing payloads of `2 ^ 32` bytes or more), `deliver` and
  the invariant `ChanInv`; and `send_discharges_not_full`, `send_bounded`, `send_inv`,
  `deliver_spec`, `send_deliver`, `send_refuses_too_long`. The module imports no queue model, so
  "proved once, holds for every instance" is enforced by the import graph.
- **`Channel/Instances.lean`**: `deliver_spec_RB` and `deliver_spec_VQ`, `deliver_spec` used
  unchanged at both queues.

### Registry and scoring: `Certify.lean`, `Registry.lean`

`Certify.lean` holds the scoring bank and the registration machinery: `Item` with its tier-scaled
weights, `totalScore`/`totalMax`, the `name_of%` elaborator, `CertifiedItem`, `toBank`,
`stmt_hash%` and the `register%` macro. It is a minimal re-implementation, written for this
repository, of a registry design from an earlier Lean project; its module header describes what was
reproduced and what was added. `register%` splices the theorem as `@thm`, so theorems with implicit
binders register too, which lets the bridge package use the same macro.

A **registry row** binds a theorem to its elaborated statement hash, so a silently weakened
theorem fails the build. The **bank** is the list of rows. Each row carries a weight set by its item
type; **score** sums the weights of rows marked verified, and the **achievable** total sums every
row's weight. The only gap is the compiler-trusting `crc8_step_linear` row, which scores `0`. Both
totals, and the row count, are closed by kernel `decide` in `Registry.lean`. The bridge registry
(`../aeneas/FramedChannelAeneas/Registry.lean`) extends the bank over both packages. Every name a
manifest lists under `proofs:` is registered in one of the two, and `../check.sh` fails when the
sets differ.

The statement hash is `Lean.Expr`'s 64-bit structural hash: a change detector, not a cryptographic
commitment, and toolchain-sensitive, which is why `lean-toolchain` is pinned. Regenerate the hash
columns with `bash ../scripts/refresh-hashes.sh --aeneas` (or `--core-only` to skip the bridge
registry; one of the two is required).

### The Challenge library: `FramedChannelChallenge/`

`FramedChannelChallenge/{RingBuffer,VecQueue,Varint,Crc8,Channel}.lean` (root
`FramedChannelChallenge.lean`) restate every core registered theorem except the shared-proof pair
with `:= sorry`, importing only `Defs` modules: the approved specification, in the form Comparator
consumes, one approval unit per component. It is maintained by hand, never regenerated from the
proofs, and the gate checks each statement hash against the registry column. The root module's
docstring explains the library in full.

### Tooling: `FramedChannel/Ladder.lean`

The proof-method ladder (the Prove step); it declares no theorem. `rung <method> => <script>`
proves a declaration with `<script>` after checking that the script is in the method's syntax class
and that no strictly cheaper rung closes the goal, and logs the record. `ladder_record%` records
the shared-proof pair after the fact and the class instances; `refuted%` records a rejected
candidate with the witness read off its kernel-checked search theorem. The module docstring gives
the syntax classes, the canonical attempt per rung, the audit's soundness details and the
toolchain-drift note. `../README.md`, "Proof ladder", summarizes it; `../tests/ladder/run.sh`
shows mislabeled records failing.

### Evidence: `FramedChannel/Evidence/Countermodels.lean`

Rejected candidate statements, each refuted in the kernel, imported by nothing and registered
nowhere. Each has a `Prop` definition, a `search_*` theorem proving by `decide +kernel` that an
explicit enumeration's first failure is the witness, a `*_false` refutation and a `refuted%`
record:

| Candidate | What it drops | Witness |
|---|---|---|
| `encode_length_le_unbounded` | `encode_length_le`'s `n < 2 ^ 32` | `2 ^ 35`, the first power of two encoding in six bytes |
| `varint_roundtrip_unbounded` | `varint_roundtrip`'s `n < 2 ^ 32` | `2 ^ 35`, whose sixth byte is left over |
| `parseFrameResync_roundtrip` | the receiver design: a parser treating a second `0x7E` as a new boundary | payload length `126`, whose one length byte is `0x7E` |
| `idx_ne_le` | `idx_ne`'s strict `i < len`, weakened to `i ≤ len` | `(i, len) = (0, 0)` |

### Tooling: `FramedChannel/SpecCheck.lean`

The `#spec_check` command, run by `../scripts/spec-check.sh` over a Challenge library. It prints purity
violations, each restated theorem's statement hash and module, each Challenge module's closure
digest (the `spec_digest` an approval records), the extracted definitions the statements reach, and
the proofs inside the definitions layer or reached by a statement. The digest is a 64-bit,
toolchain-bound change detector.

## Relation to extraction

Every certified unit is connected to the Charon/Aeneas extraction of `../rust` by the bridge proofs in
`../aeneas/`, which also instantiate the laws directly on the extracted carriers. How each
difference between an extraction and these models (vectors, bounded integers, the `Result` monad,
loops, trait dispatch) is discharged is described in `../aeneas/README.md`.

## Navigation

- [Parent Directory](../README.md)
