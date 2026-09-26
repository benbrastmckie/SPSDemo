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
  `Spec/Codec.lean`, `Spec/Checksum.lean`, `Spec/Serial.lean`, `Spec/Receiver.lean`): an interface is
  not a unit, and nothing is proved
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
│ Spec/         Result, Queue, Codec, Checksum, Serial, Receiver    │
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
- **`Serial.lean`**: `SerialModel` (L0: `zero`, `succ`, `lt`, `defined`, `space`, with `iter`
  *derived* from `succ` rather than a field) and `SerialLaws` (L1: `lt_irrefl`, `lt_succ`,
  `succ_cycles`, `lt_total_of_defined`). Four laws and **no transitivity**: RFC 1982's serial
  comparison is not transitive, and `Evidence/Countermodels.lean` refutes it in the kernel, so the
  missing field is evidenced rather than merely absent. `defined` is the field that makes the
  totality law honest -- §3.2 leaves the comparison undefined on a pair exactly half the space
  apart. The module docstring records all three decisions.
- **`Receiver.lean`**: `ReceiverModel` (L0: `feed`, `poll`, `accepted`, `dropped`, `room`, `quiet`)
  and `ReceiverLaws` (L1: `poll_accepted`, `feed_append`, `quiet_before_flag`, `idle_flags`,
  `run_exactly_one`, `feed_frame`). The one interface in this directory **written** rather than
  checked: the receive path's operation shape -- feed a byte stream, observe an accepted-frame
  sequence plus a drop count -- fits none of the four above. Every law is stated over the `accepted`
  observation and the `dropped` count, never over a representation, the way `BoundedQueueLaws` is
  stated over `toList`. Six fields and no more: resync progress, order preservation and soundness are
  *derived* in `Composition/Receiver/`, and `room`/`quiet` are L0 fields for the same reason
  `SerialModel.defined` is one -- `feed_frame` has a side condition, and the condition must be
  expressible at the interface rather than smuggled into the operation it is about. The canonical
  model is named in the module docstring, not instantiated here (as `Codec.lean` names `Leb128`).

### Model layer: `FramedChannel/Model/`

Hand-written reference models in the shape the Aeneas Lean backend produces, each with its
interface instance, tagged `[HAND-WRITTEN: model; bridged]`. They are the abstraction targets the
bridge proves the extraction against, and the canonical non-vacuous instances of the laws. Each
component is one directory, splitting into `<X>/Theorems.lean` (the theorems below) and
`<X>/Defs.lean` (definitions only:
the representation, its invariant where it has one, the operations and the interface instance) --
`RingBuffer/Defs.lean`, `VecQueue/Defs.lean`, `Varint/Defs.lean`, `Zigzag/Defs.lean`,
`Stuff/Defs.lean`, `Crc8/Defs.lean`, `SeqNum/Defs.lean` -- so the
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
- **`Zigzag/Theorems.lean`**: the protobuf zigzag signed varint over `i32`, giving `CodecModel` its
  second value type (`α = Int`, beside `Leb128` at the naturals and `Hdlc` at byte lists). It is
  **defined over `Varint.Leb128` through the L0 projections**, so `zigzag_roundtrip` and
  `encode_length_le` are recorded on the `retrieval` rung -- retrieved from `CodecLaws` at `Leb128`
  rather than re-derived -- and the only new arithmetic is `zigzag_lt`, that the zigzag image of the
  `i32` range lies in the varint's `u32` domain. The bijection (`unzigzag_zigzag`,
  `zigzag_unzigzag`) is registered hypothesis-free, which is stronger than mutual inversion on the
  `i32` range. Rust counterpart: `zigzag`, `unzigzag`, `encode_i32`, `decode_i32`, which delegate to
  `crate::varint` rather than reimplementing LEB128.
- **`Stuff/Theorems.lean`**: HDLC-style byte stuffing (RFC 1662 asynchronous framing), bytes as
  naturals below 256, giving `CodecModel`/`CodecLaws` a third value type (`α = List Nat`, beside
  `Leb128` at the naturals and `ZigzagI32` at the integers) on the tag `Hdlc`. `stuff_marker_free`
  (a stuffed payload contains no flag byte, which is what makes the decoder's scan-to-flag
  unambiguous), `stuff_roundtrip` -- unconditional, unlike `varint_roundtrip` -- and the two
  input-relative bounds `stuff_length_le` and `encode_length_le`, both strictly more informative
  than the constant `CodecLaws.length_le` demands. `Dom` carries a 255-byte payload bound, and the
  unconditional constant bound is *false*: `Evidence/Countermodels.lean` refutes it. Rust
  counterpart: `stuff`, `encode_frame`, `unstuff`.
- **`Crc8/Theorems.lean`**: CRC-8 with polynomial `0x07`, bytes as `BitVec 8`. `crc8_table_eq_bits`
  (the 256-entry table agrees with the bitwise loop, via a per-entry lemma closed by kernel
  `decide`), `stepTable_index_in_range`, and two `ChecksumLaws` instances, `Bitwise` and `Tabled`.
  `crc8_step_linear` is the example's **first** compiler-trusting declaration: proved by `bv_decide`,
  tagged `[PROVED: compiler-trusting]`, registered with `verified := false`, and one of the two
  entries on the flagged allow-list (`SeqNum.lt_eq_ltRFC` is the other).
  `crc8_step_linear_kernel` proves the same statement in the kernel.
- **`SeqNum/Theorems.lean`**: RFC 1982 serial-number arithmetic over a 16-bit space, sequence numbers
  as `BitVec 16`, giving `SerialModel`/`SerialLaws` their canonical instance on the carrier `Serial`.
  The unit deliberately spreads itself across four ladder rungs rather than landing at `manual`:
  `decide` for `lt_irrefl` and `lt_succ` (one 16-bit variable is 65536 cases, decided in the kernel
  at `Ladder.auditHeartbeats`), `grind` for `dist_add`, `lt_add` and `lt_translation_invariant`,
  `retrieval` for `iter_space`, and `bv_decide` for `lt_eq_ltRFC` -- the example's **second**
  compiler-trusting declaration, which proves that the one-test distance form the Rust uses agrees
  with §3.2's literal two-case formula on all `2 ^ 32` pairs. `lt_eq_ltRFC_kernel` replays it in the
  kernel beside it, registered `manual (excluding bv_decide)` for the reason
  `crc8_step_linear_kernel` records. There is **no transitivity theorem and never will be**: `lt` is
  not transitive, and `Evidence/Countermodels.lean` refutes it at a genuine three-cycle. Rust
  counterpart: `SeqNum`.

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
- **`StuffedChannel/Defs.lean`**: the definitions half of `StuffedChannel/Theorems.lean` -- the
  composition-layer law bundle `Transparent` (a round trip with an *arbitrary* residual, a
  flag-free body, a terminating flag, with `flag` a class parameter because a `Prop`-valued class
  cannot carry a `Nat` field), the frame body `body`, the stuffed wire format (`encodeStuffed`,
  `parseStuffed`), the channel state `SChan`, its `send` and `deliver`, and the invariant
  `SChanInv`. Definitions only, and it imports no queue model either.
- **`StuffedChannel/Theorems.lean`**: `Channel`'s transparent counterpart, and the example's
  strongest composition claim: it reaches **three** interfaces generically -- the queue through
  `Spec/Queue.lean`, the framing codec through `CodecModel` at L0 plus the `Transparent` bundle, and
  the checksum through `ChecksumModel` at L0 -- where `Channel` reaches one. `CodecLaws` is
  deliberately not used: its `Dom` at `Stuff` caps payloads at 255 bytes where this composite admits
  every payload below `2 ^ 32`, and its `round_trip` gives a residual of `[]` only, which would
  confine `SChanInv` to at most one pending frame. `wire_flag_free_of_send` is the headline and the
  theorem `Channel` cannot have: no byte written other than a frame terminator is the flag. The
  round trip `parseStuffed_encodeStuffed` is *not* the distinguishing claim -- `Channel`'s holds at
  marker-bearing payloads too -- and `Evidence/Countermodels.lean` refutes the marker-free-wire
  claim about `Channel.encodeFrame` in the kernel. The module imports no queue model and no
  `Model/Stuff/Theorems`, so the genericity is enforced by the import graph.
- **`StuffedChannel/Instances.lean`**: `instTransparentHdlc`, the `Transparent` bundle discharged at
  HDLC stuffing from `Stuff.unstuff_stuff` and `Stuff.stuff_marker_free` alone, plus
  `deliver_spec_RB` and `deliver_spec_VQ` -- the substitution row at a second composite.
- **`Receiver/Defs.lean`**: the definitions half of `Receiver/Theorems.lean` -- the receiver state
  `Rcv` (the queue of accepted frames, the bytes of the run being scanned, a drop count), the
  acceptance test `acceptRun` (one line of reuse: the run plus one flag handed to
  `StuffedChannel.parseStuffed`, with nothing left over), `EncRun`, `finishRun`, `step`, `feed`,
  `poll`, the observations `accepted`, `dropped`, `room` and `quiet`, the `ReceiverModel` instance and
  the scan invariant `RcvInv`. Definitions only, and it imports no queue model. It lives under
  `Composition/` rather than `Model/` precisely because its acceptance test is
  `StuffedChannel.parseStuffed`: the layer rule forbids a `Model/` file from importing a
  `Composition/` one, so a `Model/Receiver/` would have had to duplicate the run parser.
- **`Receiver/Theorems.lean`**: the resynchronizing receive path, generic over any
  `[QueueModel Q E] [BoundedQueueLaws Q E]`, any `CodecModel` carrying the `Transparent` bundle and
  any `ChecksumModel` at L0. The six `ReceiverLaws` fields (`poll_accepted`, `feed_append`,
  `quiet_before_flag`, `idle_flags`, `run_exactly_one`, `feed_frame`) and `accepted_sound`, the
  headline: every frame a fresh receiver accepts off an **arbitrary** byte stream is the acceptance
  test's own reading of a non-empty, flag-free, flag-terminated run that occurs in that stream. The
  witnessing run is explicit rather than the frame's own encoding because the encoding form is
  refuted in the kernel (see the countermodel table). `feed_frame` is where the `Transparent`
  bundle's `body_flag_free` is load-bearing rather than decorative.
- **`Receiver/Instances.lean`**: `instReceiverLaws` (so neither new class is vacuous), the two
  **derived** theorems `resync_progress` and `order_preserved` -- each from `feed_append` and
  `feed_frame`, which is why neither is a law field -- and `feed_spec_RB`/`feed_spec_VQ`, the
  substitution row at a third composite.

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
row's weight. The only gaps are the two compiler-trusting rows, `crc8_step_linear` and
`SeqNum.lt_eq_ltRFC`, which each score `0`. Both
totals, and the row count, are closed by kernel `decide` in `Registry.lean`. The bridge registry
(`../aeneas/FramedChannelAeneas/Registry.lean`) extends the bank over both packages. Every name a
manifest lists under `proofs:` is registered in one of the two, and `../check.sh` fails when the
sets differ.

The statement hash is `Lean.Expr`'s 64-bit structural hash: a change detector, not a cryptographic
commitment, and toolchain-sensitive, which is why `lean-toolchain` is pinned. Regenerate the hash
columns with `bash ../scripts/refresh-hashes.sh --aeneas` (or `--core-only` to skip the bridge
registry; one of the two is required).

### The Challenge library: `FramedChannelChallenge/`

`FramedChannelChallenge/{RingBuffer,VecQueue,Varint,Zigzag,Crc8,Stuff,SeqNum,Channel}.lean` (root
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
| `encode_no_expansion` | nothing -- it refutes a plausible *hope*: that a stuffed frame is no longer than its payload. Stuffing expands, which is what `stuff_length_le`'s factor of two is for | `[Stuff.marker]`, the one-byte payload that is itself the flag |
| `stuff_maxLen_unbounded` | `CodecLaws.length_le` at `Stuff` without the domain's `p.length ≤ 255`. This is what makes `Hdlc`'s `Dom` bound demonstrably load-bearing rather than decorative | a 256-byte all-flag payload, whose stuffed frame is 513 bytes against a `maxLen` of 511 |
| `zigzag_lt_unbounded` | `Zigzag.zigzag_lt`'s `i32`-range hypothesis | `2 ^ 31`, the first value outside `i32` |
| `zigzag_monotone` | nothing -- it refutes a plausible *misuse*: that `zigzag` preserves order, hence that encoded byte order is signed order | `(-2, -1)` |
| `zigzag_encode_length_le_unbounded` | `Zigzag.encode_length_le`'s domain hypothesis entirely | `2 ^ 34`, the **varint's** five-byte fuel boundary, not the `i32` one -- that refutation is `zigzag_lt_unbounded` |
| `lt_trans_cand` | nothing -- it is the one row here that refutes a law a reader would simply **assume** holds: that RFC 1982's serial `lt` is transitive. `SerialLaws` therefore has no such field | `(0, 20000, 40000)`, a genuine three-cycle (`cycle_witness` records `lt 40000 0` too). The enumeration steps by 5000 rather than by powers of two, whose first failure would instead be the undefined region below |
| `lt_total_cand` | `SeqNum.lt_total_of_defined`'s `defined` hypothesis | `32768`, exactly half the space from `0`, where §3.2 leaves the comparison undefined and neither number is serially before the other |
| `channel_wire_marker_free` | nothing -- it refutes the claim that makes `StuffedChannel` necessary: that the unstuffed `Channel` writes the flag byte nowhere after a frame's leading boundary byte, so a receiver could scan to the next flag. It cannot. Distinct from `parseFrameResync_roundtrip` above in quantified object (the encoder's output, not a receiver's behaviour), witness, and mechanism (a payload byte colliding with the flag, not a varint length byte) | `[marker]`, the one-byte payload that is itself the flag |
| `receiver_sound_unstuffed` | nothing -- it refutes the claim that makes stuffing load-bearing for the *receive* path: that a receiver which scans to the next flag is sound over the **unstuffed** `Channel` framing. It is not, so `Composition/Receiver/`'s soundness genuinely needs the marker-free body. Distinct from `parseFrameResync_roundtrip` (a hypothetical receiver's round trip) and from `channel_wire_marker_free` (the encoder's output) in quantified object: this one is about what a real receiver **accepts** | `[18#8, 126#8, 0#8]`, a payload whose middle byte is the flag -- the wire must carry the next frame's leading flag too, because a single `Channel` frame's final run is never flag-terminated and stays buffered |
| `receiver_accepted_canonical` | soundness in the **canonical-encoding** form: that every accepted frame's own encoding occurs in the wire that produced it. False even over **stuffed** framing -- the one row here that survives stuffing -- because a LEB128 length prefix is not canonical in either the model or the Rust. This is what makes `accepted_sound`'s witnessing-**run** form necessary rather than defensive | `[129, 0, 0, 0, 126]`, where the receiver accepts `[0]` whose canonical encoding `[1, 0, 0, 126]` occurs nowhere in that wire |

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
