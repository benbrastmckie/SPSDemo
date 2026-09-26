# rust/

The `framed_channel` crate: the Rust the worked example verifies. The Lean models under
`../lean/FramedChannel/` model it, and `../aeneas/` proves its Charon/Aeneas extraction refines
them. The crate is not published (`publish = false`) and needs Rust 1.95.0 or later.

```
cargo test                    the differential test suite; needs no Lean toolchain
cargo test -- --nocapture     the same, printing per-scenario input counts and the seed record
```

Without a Rust toolchain on PATH, from the repository root:
`nix develop --command bash -c 'cd framed_channel/rust && cargo test'`.

## The Rust subset

Safe, sequential and deterministic:

- `#![forbid(unsafe_code)]`;
- no interior mutability (`Cell`, `RefCell`, `Mutex`, `Arc`);
- no trait objects, closures or iterator chains; generics with trait bounds are permitted, and
  `BoundedQueue<T>` is the point of the example;
- no `unwrap` or `expect` in `src/` (the tests use `expect` in the vector parser, where a malformed
  vector file must abort the test, and on one value the same test has just encoded);
- every slice and array read goes through `get`, so no indexing expression in `src/` can panic;
- every loop is bounded: the varint loops to five iterations, the CRC inner loop to eight, the rest
  to the length of a list already in hand.

Anything outside the subset is excluded rather than modeled. The crate itself forbids `unsafe`
code entirely (`#![forbid(unsafe_code)]` above), so there is no `unsafe`/`MaybeUninit` interior to
exclude; the exclusion that would matter for a production ring buffer is concurrent use, listed
twice in `../certificate/ring_buffer.yaml`'s `not_claimed` block -- once for the model
(concurrent push/pop) and once for the extraction (concurrent use of the extracted code).

## Lint and format policy

`../check.sh` gates `cargo fmt --check` (against `rustfmt.toml`: `max_width = 100`,
`use_small_heuristics = "Max"`) and `cargo clippy --all-targets -- -D warnings` at the default lint
level. `clippy::pedantic` is not gated. The exceptions in the tree:

- five compact data arrays in `tests/differential.rs` carry `#[rustfmt::skip]`, to stay packed one
  line per group of related values;
- one `#[allow(clippy::cast_possible_truncation)]`, on the `k as u8` in the CRC incremental-prefix
  scenario of `tests/differential.rs`, guarded by the assertion just above it that the record holds
  256 digests;
- one `#[allow(clippy::should_implement_trait)]`, on `SeqNum::add` in `src/seq_num.rs`, whose
  operand types are asymmetric (`SeqNum + u16`, never `SeqNum + SeqNum`) and which is deliberately
  an inherent method rather than a `std::ops::Add` impl, so that the extraction carries no trait
  dispatch for it.

## The doc-comment citations in `src/` are deliberately frozen

`scripts/lib/approval-digests.sh`'s `source_sha256` -- the digest the recorded *selection*
approval in `certificate/approvals.yaml` is bound to -- is a sha256 over the raw bytes of every
`src/*.rs` plus `Cargo.toml` and `Cargo.lock`. It does not skip comments. Editing a `//!` or `///`
line in `src/` therefore stales the selection record and turns `../check.sh`'s approvals stage
red, and clearing it again costs a re-review of all 107 in-subset extraction candidates for a
change that alters no code.

So `src/*.rs` is edited only when the *code* changes, and a stale doc-comment citation waits for
the next change that is not comment-only rather than being corrected on its own.

Three such citations -- `queue.rs`'s header and four method docs naming `Model/ListQueue.lean` and
`LQ`, `ring_buffer.rs`'s header naming `certificate/ring_buffer_push.yaml`, and `channel.rs`'s
header naming `lean/FramedChannel/Composition/Channel.lean` -- were carried by the change that
added `src/stuffed_channel.rs`, which restaled the selection record anyway. They now read
`Model/VecQueue/{Defs,Theorems}.lean` / `VQ`, `certificate/ring_buffer.yaml`, and
`lean/FramedChannel/Composition/Channel/Theorems.lean`. None of them was ever a claim: each was a
path or a spelling, and the gate checks the real link (the `module:`/`declaration:` fields of
`certificate/*.yaml`, which are current) rather than the comment.

There is no outstanding correction as of that change. The rule stands: when one accumulates, record
it here and let the next code change carry it.

A separate, permanent naming exception is documented in `../README.md`'s unit name-mapping table:
the extraction module is `queue`, not `vec_queue`, because `src/queue.rs` holds the
`BoundedQueue` trait alongside the `VecQueue` type.

## Modules

### src/lib.rs
`#![forbid(unsafe_code)]`, the nine modules, and the re-exports `Channel`, `DeliverFail`, `Frame`,
`SendFail`, `MARKER`, `BoundedQueue`, `VecQueue`, `Full`, `RingBuffer`, `SeqNum`,
`StuffedChannel`.

### src/ring_buffer.rs
`RingBuffer<T: Default + Clone>` over a `Vec<T>` with fields `buf`, `head`, `tail`, `len`:
`with_capacity`, `push -> Result<(), Full>`, `pop -> Option<T>`, `capacity`, `len`, `is_full`,
`is_empty`, and `contents -> Vec<T>`, the abstraction function (Lean `contents`, the interface's
`toList`). `buf` is read and written only through private checked helpers `get` and `set`. Its Lean
model is `../lean/FramedChannel/Model/RingBuffer/Theorems.lean`, and its `BoundedQueue<T>` impl is the Rust
picture of the `RingBuffer.BQ` instance.

### src/queue.rs
`BoundedQueue<T>`, the executable counterpart of the Lean interface `QueueModel` constrained by
`BoundedQueueLaws`; each method's doc names the Lean field and the law that constrains it. The
laws are exercised for every implementor by `check_bounded_queue_laws` in `tests/differential.rs`.

Also `VecQueue<T>`, a list-backed bounded queue mirroring `Model/VecQueue/Theorems.lean`'s `VQ` field for
field; `push` refuses once `cap <= items.len()`. One recorded difference:
`RingBuffer::with_capacity(0)` rounds up to one (`0 < cap` is part of its invariant), while
`VecQueue::with_capacity(0)` does not, matching `VQ`.

### src/varint.rs
LEB128 for `u32`: `encode_u32(n, &mut Vec<u8>)` and
`decode_u32(&[u8]) -> Result<(u32, usize), VarintError>`, with `VarintError = Truncated | Overlong`.
Both loops are bounded to five iterations, which the Lean model makes explicit as fuel `5`.

### src/crc8.rs
CRC-8, polynomial `0x07`, initial value `0`, no reflection, no final xor: `crc8` (the bitwise loop)
and `crc8_table` (the 256-entry `const` table). Check value `crc8(b"123456789") == 0xF4`. The table
lookup goes through `get` with a `0` fallback that Lean's `stepTable_index_in_range` proves
unreachable.

### src/seq_num.rs
`SeqNum`, a 16-bit sequence number with RFC 1982 serial-number arithmetic: `new`, `get`, `succ`,
`add` (a bounded increment), `dist` (the forward modular distance) and `lt` (§3.2's serial
comparison, written as the one-test distance form). All arithmetic wraps and is written with the
explicit `wrapping_add`/`wrapping_sub` methods, because the extraction models plain `+`/`-` as a
panic on overflow. `lt` is **not transitive** -- `lt(0, 20000)`, `lt(20000, 40000)` and
`lt(40000, 0)` hold while `lt(0, 40000)` does not -- and is undefined on pairs exactly half the
space apart; both facts are kernel-refuted in
`../lean/FramedChannel/Evidence/Countermodels.lean`, and the RFC-faithfulness of the one-test form
is the Lean theorem `FramedChannel.SeqNum.lt_eq_ltRFC` rather than a comment.

### src/channel.rs
The composite and the wire format: `MARKER`, `Frame`, `DeliverFail`, `SendFail`,
`encode_frame(payload, len, out)`, `parse_frame`, and `Channel<Q = RingBuffer<Frame>>` with
`Q: BoundedQueue<Frame>`, whose public surface is `new`, `with_queue`, `send`, `deliver`, `take`,
`queued`.

`send(payload)` refuses when `queued + in_flight >= capacity`, then refuses a payload whose length
does not fit a `u32` (obtaining the checked `len` it passes to `encode_frame`), else appends the
frame to the wire and counts it in flight; both refusals are `Err(SendFail)` and leave the channel
untouched. The capacity refusal discharges `push`'s not-full assumption, so `deliver`'s push cannot
fail on a frame this channel sent; the length refusal is Lean's `send_refuses_too_long`.
`deliver()` parses one frame off the wire (`parse_frame` uses `?` on `Option` throughout), pushes
it and decrements the in-flight count, returning `Err(DeliverFail)` in exactly the cases where the
Lean `deliver` returns `.fail`. Every method reaches the queue only through the trait, the
executable picture of substitution.

### src/stuffed_channel.rs
`Channel`'s transparent counterpart: `encode_stuffed(payload, len, out)`, `parse_stuffed`, and
`StuffedChannel<Q = RingBuffer<Frame>>` with `Q: BoundedQueue<Frame>`, whose public surface is
`new`, `with_queue`, `send`, `deliver`, `take`, `queued`. It reuses `channel::{Frame, SendFail,
DeliverFail}` and declares no parallel error types.

`send` has the same two guards as `Channel::send` -- `queued + in_flight >= capacity`, then a
length that does not fit a `u32` -- and then builds the same body (`varint::encode_u32` of the
length, the payload, `crc8::crc8` of the payload) but hands it whole to `stuff::encode_frame`, so
the body reaches the wire byte-stuffed and terminated by the HDLC flag. No byte written other than
that terminator is the flag, which is the transparency `Channel` cannot offer and which the Lean
theorem `StuffedChannel.wire_flag_free_of_send` states. There is no leading boundary byte: the
terminating flag alone delimits a frame. `deliver` runs the three layers backwards -- `unstuff`,
`decode_u32`, then a trailing check byte that must equal the CRC-8 of the payload with nothing left
over -- and pushes the payload. The flag comes only from `stuff`; `channel::MARKER` is never read
here, and nothing in this module claims the two constants agree.

### tests/differential.rs
The differential suite: no randomness, no dependencies. It is the `validated` translation evidence
(G1/G2) and part of the G4 evidence the manifests under `../certificate/` cite; the module
docstring states its scope.

- **Rust against its own translation.** The `*_agrees_with_extracted_vectors` scenarios compare the
  compiled Rust with values Lean computed by evaluating the Charon/Aeneas extraction of this crate
  (`../certificate/vectors.txt`, read with `include_str!`). Each queue and each channel is compared
  with its own translation.
- **Rust against Rust.** `ring_buffer_agrees_with_vecdeque_oracle` and
  `crc8_bitwise_agrees_with_table` validate this half alone.
- **What `cargo test` alone does not check.** It trusts `vectors.txt` as committed;
  `bash ../check.sh` (the gate's differential vectors stage) ties that file back to the extraction.
  `extracted_vectors_cover_every_translated_operation` asserts the file cannot silently shrink.
- **Out of the codec's domain.** `varint_out_of_domain_agrees_with_extracted_vectors` covers inputs
  denoting values at or above `2 ^ 32`, where Rust and extraction agree on `Err(Overlong)`; the
  hand-written model's divergence there is a theorem
  (`FramedChannel.Bridge.varint.decode_err_iff`), not a test.
- **The length-126 case.** A 126-byte payload encodes its length as `0x7E`, the marker byte.
  `channel_len126_roundtrip` and `channel_len126_roundtrip_vec_queue` keep it covered.

## Navigation

- [Parent Directory](../README.md)
