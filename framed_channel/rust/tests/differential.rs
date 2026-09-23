// SPDX-License-Identifier: Apache-2.0
//! Differential execution: each component against a standard-library oracle, a second
//! implementation, or the vectors Lean computed by evaluating the Charon/Aeneas extraction of this
//! crate (`../../certificate/vectors.txt`, from `../../aeneas/GenVectors.lean`), on fixed inputs.
//! Finite testing, not proof: the validated evidence named in each manifest's `trust:` block. Every
//! scenario reports its input count under `cargo test -- --nocapture`; see `../README.md`.

use framed_channel::channel::{encode_frame, parse_frame, DeliverFail, SendFail};
use framed_channel::crc8::{crc8, crc8_table};
use framed_channel::queue::BoundedQueue;
use framed_channel::ring_buffer::{Full, RingBuffer};
use framed_channel::varint::{decode_u32, encode_u32, VarintError};
use framed_channel::{Channel, Frame, VecQueue, MARKER};
use std::collections::VecDeque;

/// The seed record for the whole suite. See the module docstring: there is no RNG, so there is
/// no seed, and this constant records that fact where a seed would otherwise be reported.
const SEED_RECORD: &str = "seed: none (deterministic fixed-vector suite, no RNG)";

/// Per-scenario input accounting. `saw()` adds one examined input, called once beside each
/// operation it counts -- never as a single precomputed total -- so a count can only grow by one
/// call per examined item. `report()` prints the line that `cargo test -- --nocapture` shows.
/// `count` also serves as each scenario's did-this-actually-run guard, so no scenario keeps a
/// second tally of the same thing.
struct Inputs {
    name: &'static str,
    count: usize,
}

impl Inputs {
    fn new(name: &'static str) -> Self {
        Inputs { name, count: 0 }
    }

    fn saw(&mut self) {
        self.count += 1;
    }

    fn report(&self) {
        println!("[differential] {}: {} inputs examined; {}", self.name, self.count, SEED_RECORD);
    }
}

#[derive(Clone, Copy)]
enum Op {
    Push(u32),
    Pop,
}

#[test]
fn ring_buffer_agrees_with_vecdeque_oracle() {
    let cap = 4;
    #[rustfmt::skip]
    let ops = [
        Op::Push(1), Op::Push(2), Op::Pop, Op::Push(3), Op::Push(4), Op::Push(5), Op::Push(6),
        Op::Pop, Op::Pop, Op::Push(7), Op::Push(8), Op::Pop, Op::Pop, Op::Pop, Op::Pop, Op::Pop,
        Op::Push(9), Op::Push(10), Op::Push(11), Op::Push(12), Op::Push(13), Op::Pop, Op::Push(14),
    ];
    let mut inputs = Inputs::new("ring_buffer_agrees_with_vecdeque_oracle");
    let mut rb: RingBuffer<u32> = RingBuffer::with_capacity(cap);
    let mut oracle: VecDeque<u32> = VecDeque::new();
    for op in ops {
        inputs.saw();
        match op {
            Op::Push(x) => {
                let expected = if oracle.len() == cap {
                    Err(Full)
                } else {
                    oracle.push_back(x);
                    Ok(())
                };
                assert_eq!(rb.push(x), expected);
            }
            Op::Pop => assert_eq!(rb.pop(), oracle.pop_front()),
        }
        assert_eq!(rb.contents(), Vec::from(oracle.clone()));
        assert_eq!(rb.len(), oracle.len());
        assert_eq!(rb.is_full(), oracle.len() == cap);
        assert_eq!(rb.is_empty(), oracle.is_empty());
    }
    inputs.report();
}

/// Fill to capacity, then cycle pop-then-push thirty times so `head` and `tail` both wrap while
/// the buffer is full; the contents must stay the last three values pushed, in order.
#[test]
fn ring_buffer_wraps_around_many_times() {
    let mut inputs = Inputs::new("ring_buffer_wraps_around_many_times");
    let mut rb: RingBuffer<u8> = RingBuffer::with_capacity(3);
    for i in 0..3u8 {
        inputs.saw();
        assert_eq!(rb.push(i), Ok(()));
    }
    for i in 3..33u8 {
        assert!(rb.is_full());
        inputs.saw();
        assert_eq!(rb.pop(), Some(i - 3));
        inputs.saw();
        assert_eq!(rb.push(i), Ok(()));
        assert_eq!(rb.contents(), vec![i - 2, i - 1, i]);
    }
    inputs.report();
}

/// The one recorded difference between the queues, pinned on both sides: `RingBuffer` rounds a
/// zero capacity up to one (`0 < cap` is part of its invariant); `VecQueue`, like Lean `VQ`, keeps
/// it, so every push fails.
#[test]
fn zero_capacity_differs_as_recorded() {
    let mut inputs = Inputs::new("zero_capacity_differs_as_recorded");
    let mut rb: RingBuffer<u32> = RingBuffer::with_capacity(0);
    inputs.saw();
    assert_eq!(rb.capacity(), 1);
    assert_eq!(rb.push(1), Ok(()));
    assert_eq!(rb.push(2), Err(Full));
    let mut vq: VecQueue<u32> = VecQueue::with_capacity(0);
    inputs.saw();
    assert_eq!(vq.capacity(), 0);
    assert!(vq.is_full() && vq.is_empty());
    assert_eq!(vq.push(1), Err(Full));
    inputs.report();
}

/// The executable analogue of the Lean `BoundedQueueLaws` instance: at any `Q: BoundedQueue<u32>`
/// this checks all six laws at every step of one sequence that fills past full, drains past empty,
/// and interleaves both. One body, run at two implementations below.
fn check_bounded_queue_laws<Q: BoundedQueue<u32>>(cap: usize, inputs: &mut Inputs) {
    #[rustfmt::skip]
    let ops = [
        // fill past full
        Op::Push(1), Op::Push(2), Op::Push(3), Op::Push(4), Op::Push(5),
        // drain past empty
        Op::Pop, Op::Pop, Op::Pop, Op::Pop, Op::Pop, Op::Pop,
        // interleaved
        Op::Push(6), Op::Pop, Op::Push(7), Op::Push(8), Op::Pop, Op::Push(9),
    ];
    let mut q: Q = Q::with_capacity(cap);
    for op in ops {
        inputs.saw();
        let capacity_before = q.capacity();
        let contents_before = q.contents();
        let full_before = q.is_full();
        let empty_before = q.is_empty();
        // not_full_of_lt: room below the capacity means not full.
        if contents_before.len() < capacity_before {
            assert!(!full_before);
        }
        match op {
            Op::Push(x) => {
                if full_before {
                    // full_law: full implies push fails, contents unchanged.
                    assert_eq!(q.push(x), Err(Full));
                    assert_eq!(q.contents(), contents_before);
                } else {
                    // push_law: not full implies success and contents appended.
                    assert_eq!(q.push(x), Ok(()));
                    let mut expected = contents_before.clone();
                    expected.push(x);
                    assert_eq!(q.contents(), expected);
                }
                // push_capacity: capacity unchanged by push, success or failure.
                assert_eq!(q.capacity(), capacity_before);
            }
            Op::Pop => {
                if empty_before {
                    // empty_law: empty implies pop fails (None).
                    assert_eq!(q.pop(), None);
                } else {
                    // pop_law: not empty implies success, the front element removed.
                    let front = contents_before[0];
                    assert_eq!(q.pop(), Some(front));
                    assert_eq!(q.contents(), contents_before[1..].to_vec());
                }
            }
        }
        assert_eq!(q.len(), q.contents().len());
    }
}

#[test]
fn bounded_queue_laws() {
    let mut inputs = Inputs::new("bounded_queue_laws");
    check_bounded_queue_laws::<RingBuffer<u32>>(1, &mut inputs);
    check_bounded_queue_laws::<RingBuffer<u32>>(3, &mut inputs);
    inputs.report();
}

#[test]
fn bounded_queue_laws_vec_queue() {
    let mut inputs = Inputs::new("bounded_queue_laws_vec_queue");
    check_bounded_queue_laws::<VecQueue<u32>>(1, &mut inputs);
    check_bounded_queue_laws::<VecQueue<u32>>(3, &mut inputs);
    inputs.report();
}

/// The Rust side of the round trip row, `decode ∘ encode = id`.
#[test]
fn varint_roundtrip_on_fixed_inputs() {
    let mut inputs = Inputs::new("varint_roundtrip_on_fixed_inputs");
    #[rustfmt::skip]
    let vectors: [u32; 13] = [0, 1, 126, 127, 128, 255, 300, 16_383, 16_384, 2_097_151, 2_097_152, 268_435_455, u32::MAX];
    for &n in &vectors {
        inputs.saw();
        let mut bytes = Vec::new();
        encode_u32(n, &mut bytes);
        assert!(bytes.len() <= 5);
        for (i, b) in bytes.iter().enumerate() {
            let last = i + 1 == bytes.len();
            assert_eq!(b & 0x80 == 0, last);
        }
        assert_eq!(decode_u32(&bytes), Ok((n, bytes.len())));
        // trailing bytes are left unconsumed
        bytes.push(0x2A);
        let (m, used) = decode_u32(&bytes).expect("decodes with trailing byte");
        assert_eq!(m, n);
        assert_eq!(used, bytes.len() - 1);
    }
    inputs.report();
}

#[test]
fn varint_rejects_truncated_and_overlong() {
    let mut inputs = Inputs::new("varint_rejects_truncated_and_overlong");
    let cases: [(&[u8], VarintError); 4] = [
        (&[], VarintError::Truncated),
        (&[0x80], VarintError::Truncated),
        (&[0x80, 0x80, 0x80, 0x80, 0x80, 0x01], VarintError::Overlong),
        (&[0x80, 0x80, 0x80, 0x80, 0x10], VarintError::Overlong),
    ];
    for (bytes, want) in cases {
        inputs.saw();
        assert_eq!(decode_u32(bytes), Err(want));
    }
    inputs.report();
}

/// The Rust side of the equivalence row, `CRC-8 ≃ bitwise CRC-8`.
#[test]
fn crc8_bitwise_agrees_with_table() {
    let mut inputs = Inputs::new("crc8_bitwise_agrees_with_table");
    let vectors: [&[u8]; 6] =
        [b"", b"a", b"123456789", b"\x00\x00\x00", b"\xff\xff\xff\xff", b"framed_channel"];
    for v in vectors {
        inputs.saw();
        assert_eq!(crc8(v), crc8_table(v));
    }
    assert_eq!(crc8(b"123456789"), 0xF4);
    let mut all = Vec::new();
    for b in 0..=255u8 {
        inputs.saw();
        all.push(b);
        assert_eq!(crc8(&all), crc8_table(&all));
    }
    inputs.report();
}

/// A 126-byte payload whose varint length byte is `MARKER` (`0x7E`), and which also contains a
/// `0x7E` byte -- legal, since there is no byte stuffing. The Lean model needs no side condition
/// here either: `parseFrame` reads the byte after the marker as a length byte whatever its value.
fn payload126() -> Vec<u8> {
    let mut p: Vec<u8> = Vec::new();
    for i in 0..126u32 {
        p.push((i % 253) as u8);
    }
    p[10] = MARKER;
    p
}

// Each channel scenario below is written once as a generic `_at<Q: BoundedQueue<Frame>>` helper
// and run at both queues -- the executable picture of `Channel[VecQueue/RingBuffer]` substitution,
// mirroring `deliver_spec_RB`/`deliver_spec_VQ` on the Lean side.

fn channel_len126_roundtrip_at<Q: BoundedQueue<Frame>>(inputs: &mut Inputs) {
    let p126 = payload126();
    let mut ch: Channel<Q> = Channel::with_queue(2);
    inputs.saw();
    assert_eq!(ch.send(&p126), Ok(()));
    inputs.saw();
    assert_eq!(ch.send(b"x"), Ok(()));
    assert_eq!(ch.deliver(), Ok(p126.clone()));
    assert_eq!(ch.deliver(), Ok(b"x".to_vec()));
    assert_eq!(ch.queued(), 2);
    assert_eq!(ch.take(), Some(p126.clone()));
    assert_eq!(ch.take(), Some(b"x".to_vec()));
    assert_eq!(ch.take(), None);
}

#[test]
fn channel_len126_roundtrip() {
    // keeps `Channel::new`'s default type parameter (`Channel<RingBuffer<Frame>>`) compile-checked.
    let _: Channel<RingBuffer<Frame>> = Channel::new(2);
    let mut inputs = Inputs::new("channel_len126_roundtrip");
    channel_len126_roundtrip_at::<RingBuffer<Frame>>(&mut inputs);
    inputs.report();
}

#[test]
fn channel_len126_roundtrip_vec_queue() {
    let mut inputs = Inputs::new("channel_len126_roundtrip_vec_queue");
    channel_len126_roundtrip_at::<VecQueue<Frame>>(&mut inputs);
    inputs.report();
}

fn channel_capacity_check_discharges_not_full_at<Q: BoundedQueue<Frame>>(inputs: &mut Inputs) {
    let mut ch: Channel<Q> = Channel::with_queue(2);
    inputs.saw();
    assert_eq!(ch.send(b"one"), Ok(()));
    inputs.saw();
    assert_eq!(ch.send(b"two"), Ok(()));
    // queued + in_flight == capacity: send refuses, which is what makes deliver's push total.
    inputs.saw();
    assert_eq!(ch.send(b"three"), Err(SendFail));
    assert_eq!(ch.deliver(), Ok(b"one".to_vec()));
    assert_eq!(ch.deliver(), Ok(b"two".to_vec()));
    assert_eq!(ch.queued(), 2);
    assert_eq!(ch.take(), Some(b"one".to_vec()));
    assert_eq!(ch.take(), Some(b"two".to_vec()));
    assert_eq!(ch.take(), None);
    inputs.saw();
    assert_eq!(ch.send(b"three"), Ok(()));
    assert_eq!(ch.deliver(), Ok(b"three".to_vec()));
}

#[test]
fn channel_capacity_check_discharges_not_full() {
    let mut inputs = Inputs::new("channel_capacity_check_discharges_not_full");
    channel_capacity_check_discharges_not_full_at::<RingBuffer<Frame>>(&mut inputs);
    inputs.report();
}

#[test]
fn channel_capacity_check_discharges_not_full_vec_queue() {
    let mut inputs = Inputs::new("channel_capacity_check_discharges_not_full_vec_queue");
    channel_capacity_check_discharges_not_full_at::<VecQueue<Frame>>(&mut inputs);
    inputs.report();
}

/// `send` refuses a payload of exactly `2^32` bytes -- the shortest one whose length does not fit
/// the `u32` varint -- and leaves the wire and the in-flight count untouched: the executable
/// reading of the Lean `Channel.send_refuses_too_long`. The allocation is lazily zeroed and the
/// refusal never reads the bytes, so this costs a few megabytes of resident memory, not 4 GiB.
#[cfg(target_pointer_width = "64")]
fn channel_refuses_payload_of_2_pow_32_bytes_at<Q: BoundedQueue<Frame>>(inputs: &mut Inputs) {
    let big: Vec<u8> = vec![0u8; 1usize << 32];
    let mut ch: Channel<Q> = Channel::with_queue(2);
    inputs.saw();
    assert_eq!(ch.send(&big), Err(SendFail));
    drop(big);
    // A refusal is effect-free: the next frame is the first one on the wire.
    inputs.saw();
    assert_eq!(ch.send(b"a"), Ok(()));
    assert_eq!(ch.deliver(), Ok(b"a".to_vec()));
    assert_eq!(ch.deliver(), Err(DeliverFail));
}

#[cfg(target_pointer_width = "64")]
#[test]
fn channel_refuses_payload_of_2_pow_32_bytes() {
    let mut inputs = Inputs::new("channel_refuses_payload_of_2_pow_32_bytes");
    channel_refuses_payload_of_2_pow_32_bytes_at::<RingBuffer<Frame>>(&mut inputs);
    inputs.report();
}

#[cfg(target_pointer_width = "64")]
#[test]
fn channel_refuses_payload_of_2_pow_32_bytes_vec_queue() {
    let mut inputs = Inputs::new("channel_refuses_payload_of_2_pow_32_bytes_vec_queue");
    channel_refuses_payload_of_2_pow_32_bytes_at::<VecQueue<Frame>>(&mut inputs);
    inputs.report();
}

/// `send` then `deliver` pushes exactly the sent frame onto the abstract queue: the executable
/// reading of the Lean headline composite `Channel.send_deliver`.
fn channel_send_deliver_pushes_exactly_p_at<Q: BoundedQueue<Frame>>(inputs: &mut Inputs) {
    let payloads: [&[u8]; 5] = [b"", b"a", b"hello", b"\x7E\x7E\x7E", b"framed_channel"];
    for p in payloads {
        inputs.saw();
        let mut ch: Channel<Q> = Channel::with_queue(4);
        let before = ch.queued();
        assert_eq!(ch.send(p), Ok(()));
        assert_eq!(ch.deliver(), Ok(p.to_vec()));
        assert_eq!(ch.queued(), before + 1);
        assert_eq!(ch.take(), Some(p.to_vec()));
    }
}

#[test]
fn channel_send_deliver_pushes_exactly_p() {
    let mut inputs = Inputs::new("channel_send_deliver_pushes_exactly_p");
    channel_send_deliver_pushes_exactly_p_at::<RingBuffer<Frame>>(&mut inputs);
    inputs.report();
}

#[test]
fn channel_send_deliver_pushes_exactly_p_vec_queue() {
    let mut inputs = Inputs::new("channel_send_deliver_pushes_exactly_p_vec_queue");
    channel_send_deliver_pushes_exactly_p_at::<VecQueue<Frame>>(&mut inputs);
    inputs.report();
}

// ===================================================================================
// Extracted-evaluation vectors: the parser
// ===================================================================================
//
// The grammar is `<op> <inputs...> => <field>; <field>; ...`; `#`-prefixed lines are comments,
// blank lines are skipped, and a result field is the Rust result as the extraction returned it:
// `ok`/`err`, `ok <scalars>`, `err <variant>`, `some`/`none`.
//
// The parser is hand-written and dependency-free on purpose: pulling in serde to read one text
// file would add a dependency to a crate whose point is that it has none. It stays inside the
// crate's subset (no closures, no iterator chains, no `collect`, no `unwrap`). A malformed vector
// file aborts the test rather than being tolerated. Byte fields parse as `u8`, value fields as
// `u32` and counts as `usize`, so an out-of-range emission is a loud parse failure and never a
// silent truncation.

const VECTORS: &str = include_str!("../../certificate/vectors.txt");

/// One record: the operation, its input tokens, and the `;`-separated result fields.
struct Record {
    op: String,
    args: Vec<String>,
    fields: Vec<Vec<String>>,
}

impl Record {
    /// Field `i`, or the empty field where the record elided a trailing separator.
    fn field(&self, i: usize) -> &[String] {
        match self.fields.get(i) {
            Some(f) => f,
            None => &[],
        }
    }

    /// The leading result token of field `i` (`ok`, `err`, `some`, `none`, ...).
    fn status(&self, i: usize) -> &str {
        match self.field(i).first() {
            Some(s) => s.as_str(),
            None => "",
        }
    }

    /// Field `i` past its result token.
    fn rest(&self, i: usize) -> &[String] {
        match self.field(i).get(1..) {
            Some(s) => s,
            None => &[],
        }
    }
}

fn tokens(s: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for t in s.split_whitespace() {
        out.push(t.to_string());
    }
    out
}

fn parse_vectors() -> Vec<Record> {
    let mut out: Vec<Record> = Vec::new();
    for raw in VECTORS.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let Some(at) = line.find("=>") else { panic!("vectors.txt: record without '=>': {line}") };
        let mut lhs = tokens(&line[..at]);
        assert!(!lhs.is_empty(), "vectors.txt: record without an operation: {line}");
        let op = lhs.remove(0);
        let mut fields: Vec<Vec<String>> = Vec::new();
        for f in line[at + 2..].split(';') {
            fields.push(tokens(f));
        }
        out.push(Record { op, args: lhs, fields });
    }
    out
}

fn u8s(ts: &[String]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    for t in ts {
        out.push(t.parse::<u8>().expect("vectors.txt: byte does not fit u8"));
    }
    out
}

fn u32s(ts: &[String]) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    for t in ts {
        out.push(t.parse::<u32>().expect("vectors.txt: value does not fit u32"));
    }
    out
}

fn one_u32(ts: &[String]) -> u32 {
    match u32s(ts).first() {
        Some(n) => *n,
        None => panic!("vectors.txt: expected one scalar"),
    }
}

fn one_usize(ts: &[String]) -> usize {
    match ts.first() {
        Some(t) => t.parse::<usize>().expect("vectors.txt: count does not fit usize"),
        None => panic!("vectors.txt: expected one count"),
    }
}

fn flag(r: &Record, i: usize) -> bool {
    match r.field(i).first() {
        Some(s) => s == "1",
        None => panic!("vectors.txt: missing 0/1 flag in {}", r.op),
    }
}

/// The five observed fields from `base`: `contents; is_empty; is_full; len; capacity`, each read
/// through the extracted `BoundedQueue` record on the Lean side and through the trait here.
fn check_queue_state<Q: BoundedQueue<u32>>(q: &Q, r: &Record, base: usize) {
    assert_eq!(q.contents(), u32s(r.field(base)), "contents disagree at {}", r.op);
    assert_eq!(q.is_empty(), flag(r, base + 1), "is_empty disagrees at {}", r.op);
    assert_eq!(q.is_full(), flag(r, base + 2), "is_full disagrees at {}", r.op);
    assert_eq!(q.len(), one_usize(r.field(base + 3)), "len disagrees at {}", r.op);
    assert_eq!(q.capacity(), one_usize(r.field(base + 4)), "capacity disagrees at {}", r.op);
}

/// Replay every `<prefix>.new`/`.push`/`.pop` record in file order against a Rust queue, comparing
/// each operation's result and the resulting state. `prefix` selects the extracted record the
/// records were computed at: `ringbuffer` for `RingBuffer<u32>`, `vecqueue` for `VecQueue<u32>`.
fn queue_agrees_with_extracted_vectors<Q: BoundedQueue<u32>>(prefix: &str, inputs: &mut Inputs) {
    let records = parse_vectors();
    let mut q: Q = Q::with_capacity(1);
    let mut started = false;
    let before = inputs.count;
    for r in &records {
        let Some(op) = r.op.strip_prefix(prefix) else {
            continue;
        };
        match op {
            ".new" => {
                q = Q::with_capacity(one_u32(&r.args) as usize);
                started = true;
                inputs.saw();
                check_queue_state(&q, r, 0);
            }
            ".push" => {
                assert!(started, "vectors.txt: a push record before any .new for {prefix}");
                inputs.saw();
                let got = q.push(one_u32(&r.args));
                match r.status(0) {
                    "ok" => assert_eq!(got, Ok(()), "push result disagrees at {}", r.op),
                    "err" => assert_eq!(got, Err(Full), "push result disagrees at {}", r.op),
                    other => panic!("vectors.txt: unexpected push result {other}"),
                }
                check_queue_state(&q, r, 1);
            }
            ".pop" => {
                assert!(started, "vectors.txt: a pop record before any .new for {prefix}");
                inputs.saw();
                let got = q.pop();
                match r.status(0) {
                    "some" => {
                        assert_eq!(got, Some(one_u32(r.rest(0))), "pop disagrees at {}", r.op);
                    }
                    "none" => assert_eq!(got, None, "pop should have been None at {}", r.op),
                    other => panic!("vectors.txt: unexpected pop result {other}"),
                }
                check_queue_state(&q, r, 1);
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no records for {prefix}");
}

/// `RingBuffer<u32>` against the extracted ring buffer record, record by record, including the
/// zero requested capacity the extracted `with_capacity` rounds up to one.
#[test]
fn ring_buffer_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("ring_buffer_agrees_with_extracted_vectors");
    queue_agrees_with_extracted_vectors::<RingBuffer<u32>>("ringbuffer", &mut inputs);
    inputs.report();
}

/// `VecQueue<u32>` against the extracted `VecQueue` record, including the zero capacity in which
/// every push is refused.
#[test]
fn vec_queue_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("vec_queue_agrees_with_extracted_vectors");
    queue_agrees_with_extracted_vectors::<VecQueue<u32>>("vecqueue", &mut inputs);
    inputs.report();
}

/// A decode record's expected Rust result.
fn expected_decode(r: &Record) -> Result<(u32, usize), VarintError> {
    match r.status(0) {
        "ok" => {
            let rest = r.rest(0);
            let value = match rest.first() {
                Some(v) => v.parse::<u32>().expect("vectors.txt: decoded value does not fit u32"),
                None => panic!("vectors.txt: an ok decode record with no value"),
            };
            let used = match rest.get(1..) {
                Some(u) => one_usize(u),
                None => panic!("vectors.txt: an ok decode record with no consumed count"),
            };
            Ok((value, used))
        }
        "err" => match r.rest(0).first() {
            Some(v) if v == "truncated" => Err(VarintError::Truncated),
            Some(v) if v == "overlong" => Err(VarintError::Overlong),
            _ => panic!("vectors.txt: a decode error record with no known variant"),
        },
        other => panic!("vectors.txt: unexpected decode result {other}"),
    }
}

/// `encode_u32`/`decode_u32` against the extracted functions: the encoded bytes, and the decode
/// result with its error variant and consumed count.
#[test]
fn varint_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("varint_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "varint.encode" => {
                inputs.saw();
                let mut got: Vec<u8> = Vec::new();
                encode_u32(one_u32(&r.args), &mut got);
                assert_eq!(got, u8s(r.field(0)), "encode disagrees for {}", r.args.join(" "));
            }
            "varint.decode" => {
                inputs.saw();
                let got = decode_u32(&u8s(&r.args));
                assert_eq!(got, expected_decode(r), "decode disagrees for {}", r.args.join(" "));
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no varint records");
    inputs.report();
}

/// Out of the codec's domain: a fifth group too wide for a `u32`. The Rust and the extraction agree
/// on `Err(Overlong)` -- an agreement record like any other. The hand-written `Nat` model decodes a
/// value at or above `2 ^ 32` on these inputs; that model divergence is a theorem
/// (`FramedChannel.Bridge.varint.decode_err_iff`), not a test.
#[test]
fn varint_out_of_domain_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("varint_out_of_domain_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        if r.op != "varint.decode.out_of_domain" {
            continue;
        }
        inputs.saw();
        assert_eq!(
            expected_decode(r),
            Err(VarintError::Overlong),
            "an out-of-domain record the extraction did not reject as Overlong"
        );
        assert_eq!(
            decode_u32(&u8s(&r.args)),
            expected_decode(r),
            "out-of-domain decode disagrees for {}",
            r.args.join(" ")
        );
    }
    assert!(inputs.count > before, "vectors.txt has lost the out-of-domain varint class");
    inputs.report();
}

/// `crc8`/`crc8_table` against the extracted `crc8`/`crc8_table`, on the six named vectors and the
/// 256 incremental prefixes. The prefixes arrive as one compact record whose input rule the vector
/// file's header states: digest `k` is the checksum of the byte sequence `0, 1, ..., k`.
#[test]
fn crc8_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("crc8_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "crc8.bits" | "crc8.table" => {
                inputs.saw();
                let want = u8s(r.field(0));
                let digest = match want.first() {
                    Some(d) => *d,
                    None => panic!("vectors.txt: a crc8 record with no digest"),
                };
                let message = u8s(&r.args);
                let got = if r.op == "crc8.bits" { crc8(&message) } else { crc8_table(&message) };
                assert_eq!(got, digest, "{} disagrees for {}", r.op, r.args.join(" "));
            }
            "crc8.incremental_prefixes" => {
                let digests = u8s(r.field(0));
                assert_eq!(digests.len(), 256, "the incremental-prefix record is not 256 digests");
                let mut all: Vec<u8> = Vec::new();
                let mut k = 0usize;
                while k < digests.len() {
                    inputs.saw();
                    // digests.len() == 256 is asserted above, so k < 256 always fits a u8.
                    #[allow(clippy::cast_possible_truncation)]
                    let byte = k as u8;
                    all.push(byte);
                    assert_eq!(crc8(&all), digests[k], "incremental prefix {k} disagrees");
                    k += 1;
                }
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no crc8 records");
    inputs.report();
}

/// The frame codec byte for byte against the extracted `encode_frame`/`parse_frame`, including the
/// 126-byte payload whose length byte is the marker, a trailing byte, a short wire and a corrupted
/// check byte. `parse_frame` records carry `(payload, consumed)` exactly as the Rust returns them.
#[test]
fn frame_codec_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("frame_codec_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "channel.encode_frame" => {
                inputs.saw();
                let payload = u8s(&r.args);
                let Ok(len) = u32::try_from(payload.len()) else {
                    panic!("vectors.txt: an encode_frame payload longer than u32::MAX");
                };
                let mut got: Vec<u8> = Vec::new();
                encode_frame(&payload, len, &mut got);
                assert_eq!(got, u8s(r.field(0)), "encode_frame disagrees");
            }
            "channel.parse_frame" => {
                inputs.saw();
                let got = parse_frame(&u8s(&r.args));
                match r.status(0) {
                    "some" => assert_eq!(
                        got,
                        Some((u8s(r.field(1)), one_usize(r.field(2)))),
                        "parse_frame disagrees"
                    ),
                    "none" => assert_eq!(got, None, "parse_frame should have returned None"),
                    other => panic!("vectors.txt: unexpected parse_frame result {other}"),
                }
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no frame-codec records");
    inputs.report();
}

/// The channel state machine, replayed against a Rust `Channel<Q>` from the records the extraction
/// computed at the same queue: `prefix` is `channel.ringbuffer` (the records from `Channel::new`
/// over the extracted ring buffer record) or `channel.vecqueue` (`Channel::with_queue` over the
/// extracted `VecQueue` record). `wire` and `in_flight` are private, so the comparison is at the
/// result, the payload and `queued()`.
fn channel_agrees_with_extracted_vectors_at<Q: BoundedQueue<Frame>>(
    prefix: &str,
    new: fn(usize) -> Channel<Q>,
    inputs: &mut Inputs,
) {
    let records = parse_vectors();
    let mut ch: Channel<Q> = new(1);
    let mut started = false;
    let before = inputs.count;
    for r in &records {
        let Some(op) = r.op.strip_prefix(prefix) else {
            continue;
        };
        match op {
            ".new" => {
                ch = new(one_u32(&r.args) as usize);
                started = true;
                inputs.saw();
                assert_eq!(ch.queued(), one_usize(r.field(0)), "queued disagrees at new");
            }
            ".send" => {
                assert!(started, "vectors.txt: a send record before any .new for {prefix}");
                inputs.saw();
                let got = ch.send(&u8s(&r.args));
                match r.status(0) {
                    "ok" => assert_eq!(got, Ok(()), "send result disagrees"),
                    "err" => assert_eq!(got, Err(SendFail), "send result disagrees"),
                    other => panic!("vectors.txt: unexpected send result {other}"),
                }
                assert_eq!(ch.queued(), one_usize(r.field(1)), "queued disagrees after send");
            }
            ".deliver" => {
                assert!(started, "vectors.txt: a deliver record before any .new for {prefix}");
                inputs.saw();
                let got = ch.deliver();
                match r.status(0) {
                    "ok" => assert_eq!(got, Ok(u8s(r.field(1))), "deliver payload disagrees"),
                    "err" => assert_eq!(got, Err(DeliverFail), "deliver should have failed"),
                    other => panic!("vectors.txt: unexpected deliver result {other}"),
                }
                assert_eq!(ch.queued(), one_usize(r.field(2)), "queued disagrees after deliver");
            }
            ".take" => {
                assert!(started, "vectors.txt: a take record before any .new for {prefix}");
                inputs.saw();
                let got = ch.take();
                match r.status(0) {
                    "some" => assert_eq!(got, Some(u8s(r.field(1))), "take payload disagrees"),
                    "none" => assert_eq!(got, None, "take should have returned None"),
                    other => panic!("vectors.txt: unexpected take result {other}"),
                }
                assert_eq!(ch.queued(), one_usize(r.field(2)), "queued disagrees after take");
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no channel records for {prefix}");
}

fn new_ring_buffer_channel(cap: usize) -> Channel<RingBuffer<Frame>> {
    Channel::new(cap)
}

fn new_vec_queue_channel(cap: usize) -> Channel<VecQueue<Frame>> {
    Channel::with_queue(cap)
}

/// `Channel::new` (the ring buffer channel) against its own extracted translation.
#[test]
fn channel_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("channel_agrees_with_extracted_vectors");
    channel_agrees_with_extracted_vectors_at(
        "channel.ringbuffer",
        new_ring_buffer_channel,
        &mut inputs,
    );
    inputs.report();
}

/// `Channel::with_queue` at `VecQueue<Frame>` against its own extracted translation.
#[test]
fn channel_agrees_with_extracted_vectors_vec_queue() {
    let mut inputs = Inputs::new("channel_agrees_with_extracted_vectors_vec_queue");
    channel_agrees_with_extracted_vectors_at(
        "channel.vecqueue",
        new_vec_queue_channel,
        &mut inputs,
    );
    inputs.report();
}

/// Count the records of `op` whose field 0 starts with `status` (any status when `status` is
/// empty) and, when `detail` is non-empty, whose second token of field 0 is `detail`.
fn count_records(records: &[Record], op: &str, status: &str, detail: &str) -> usize {
    let mut n = 0usize;
    for r in records {
        if r.op != op {
            continue;
        }
        if !status.is_empty() && r.status(0) != status {
            continue;
        }
        if !detail.is_empty() {
            match r.rest(0).first() {
                Some(d) if d == detail => {}
                _ => continue,
            }
        }
        n += 1;
    }
    n
}

/// A structural guard that the committed artifact cannot silently shrink. Every comparison above
/// iterates the records it finds, so a vector file that lost a whole operation -- or one branch
/// of one -- would leave every test passing while checking less. This asserts instead that each
/// translated operation is present with every branch, both queue records and both channel queues,
/// the zero-capacity traces, the compact CRC record, the out-of-domain class, and that no record
/// carries a panic.
#[test]
fn extracted_vectors_cover_every_translated_operation() {
    let mut inputs = Inputs::new("extracted_vectors_cover_every_translated_operation");
    let records = parse_vectors();
    #[rustfmt::skip]
    let branches: [(&str, &str, &str); 26] = [
        ("ringbuffer.push", "ok", ""), ("ringbuffer.push", "err", ""),
        ("ringbuffer.pop", "some", ""), ("ringbuffer.pop", "none", ""),
        ("vecqueue.push", "ok", ""), ("vecqueue.push", "err", ""),
        ("vecqueue.pop", "some", ""), ("vecqueue.pop", "none", ""),
        ("varint.decode", "ok", ""), ("varint.decode", "err", "truncated"),
        ("varint.decode", "err", "overlong"), ("varint.decode.out_of_domain", "err", "overlong"),
        ("channel.parse_frame", "some", ""), ("channel.parse_frame", "none", ""),
        ("channel.ringbuffer.send", "ok", ""), ("channel.ringbuffer.send", "err", ""),
        ("channel.ringbuffer.deliver", "ok", ""), ("channel.ringbuffer.deliver", "err", ""),
        ("channel.ringbuffer.take", "some", ""), ("channel.ringbuffer.take", "none", ""),
        ("channel.vecqueue.send", "ok", ""), ("channel.vecqueue.send", "err", ""),
        ("channel.vecqueue.deliver", "ok", ""), ("channel.vecqueue.deliver", "err", ""),
        ("channel.vecqueue.take", "some", ""), ("channel.vecqueue.take", "none", ""),
    ];
    for (op, status, detail) in branches {
        inputs.saw();
        assert!(
            count_records(&records, op, status, detail) > 0,
            "vectors.txt has no {status} {detail} record for {op}"
        );
    }
    #[rustfmt::skip]
    let total: [&str; 8] = [
        "ringbuffer.new", "vecqueue.new", "channel.ringbuffer.new", "channel.vecqueue.new",
        "varint.encode", "crc8.bits", "crc8.table", "channel.encode_frame",
    ];
    for op in total {
        inputs.saw();
        assert!(count_records(&records, op, "", "") > 0, "vectors.txt has no record for {op}");
    }
    let mut zero_caps = 0usize;
    let mut panics = 0usize;
    for r in &records {
        if (r.op == "ringbuffer.new" || r.op == "vecqueue.new") && r.args.join(" ") == "0" {
            zero_caps += 1;
        }
        for f in &r.fields {
            if let Some(t) = f.first() {
                if t == "panic" || t == "div" {
                    panics += 1;
                }
            }
        }
    }
    inputs.saw();
    assert_eq!(zero_caps, 2, "vectors.txt has lost a zero-capacity queue trace");
    inputs.saw();
    assert_eq!(panics, 0, "an extracted evaluation recorded in vectors.txt did not return");
    inputs.saw();
    assert_eq!(
        count_records(&records, "crc8.incremental_prefixes", "", ""),
        1,
        "vectors.txt has lost the compact incremental-prefix record"
    );
    inputs.report();
}
