// SPDX-License-Identifier: Apache-2.0
//! Differential execution: each component against a standard-library oracle, a second
//! implementation, or the vectors Lean computed by evaluating the Charon/Aeneas extraction of this
//! crate (`../../certificate/vectors.txt`, from `../../aeneas/GenVectors.lean`), on fixed inputs.
//! Finite testing, not proof: the validated evidence named in each manifest's `trust:` block. Every
//! scenario reports its input count under `cargo test -- --nocapture`; see `../README.md`.

use framed_channel::channel::{encode_frame, parse_frame, DeliverFail, SendFail};
use framed_channel::crc8::{crc8, crc8_table};
use framed_channel::queue::BoundedQueue;
use framed_channel::receiver::Receiver;
use framed_channel::ring_buffer::{Full, RingBuffer};
use framed_channel::seq_num::SeqNum;
use framed_channel::stuff::{encode_frame as stuff_encode_frame, stuff, unstuff, UnstuffError};
use framed_channel::stuffed_channel::{encode_stuffed, parse_stuffed, StuffedChannel};
use framed_channel::varint::{decode_u32, encode_u32, VarintError};
use framed_channel::zigzag::{decode_i32, encode_i32, unzigzag, zigzag};
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

fn one_i32(ts: &[String]) -> i32 {
    match ts.first() {
        Some(t) => t.parse::<i32>().expect("vectors.txt: signed value does not fit i32"),
        None => panic!("vectors.txt: expected one signed scalar"),
    }
}

fn one_u16(ts: &[String]) -> u16 {
    match ts.first() {
        Some(t) => t.parse::<u16>().expect("vectors.txt: sequence number does not fit u16"),
        None => panic!("vectors.txt: expected one sequence number"),
    }
}

fn two_u16(ts: &[String]) -> (u16, u16) {
    match (ts.first(), ts.get(1)) {
        (Some(a), Some(b)) => (
            a.parse::<u16>().expect("vectors.txt: sequence number does not fit u16"),
            b.parse::<u16>().expect("vectors.txt: sequence number does not fit u16"),
        ),
        _ => panic!("vectors.txt: expected two sequence numbers"),
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

/// The signed decode result a `zigzag.decode` record records.
fn expected_zigzag_decode(r: &Record) -> Result<(i32, usize), VarintError> {
    match r.status(0) {
        "ok" => {
            let rest = r.rest(0);
            let value = match rest.first() {
                Some(v) => v.parse::<i32>().expect("vectors.txt: decoded value does not fit i32"),
                None => panic!("vectors.txt: an ok zigzag decode record with no value"),
            };
            let used = match rest.get(1..) {
                Some(u) => one_usize(u),
                None => panic!("vectors.txt: an ok zigzag decode record with no consumed count"),
            };
            Ok((value, used))
        }
        "err" => match r.rest(0).first() {
            Some(v) if v == "truncated" => Err(VarintError::Truncated),
            Some(v) if v == "overlong" => Err(VarintError::Overlong),
            _ => panic!("vectors.txt: a zigzag decode error record with no known variant"),
        },
        other => panic!("vectors.txt: unexpected zigzag decode result {other}"),
    }
}

/// `zigzag`/`unzigzag`/`encode_i32`/`decode_i32` against the extracted functions: the signed map and
/// its inverse, the encoded bytes, and the decode result with its error variant and consumed count.
/// The vectors cover `i32::MIN`, `i32::MAX`, zero and both signs either side of the one-byte and
/// two-byte encoding boundaries. Since `decode_i32` forwards the `VarintError` its `decode_u32` call
/// returns, the error variants here are the varint's own -- the agreement the model states as
/// `FramedChannel.Zigzag.decode_fail_iff` and the bridge as
/// `FramedChannel.Bridge.zigzag.decode_err_iff`.
#[test]
fn zigzag_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("zigzag_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "zigzag.zigzag" => {
                inputs.saw();
                let want = match r.field(0).first() {
                    Some(v) => {
                        v.parse::<u32>().expect("vectors.txt: zigzag image does not fit u32")
                    }
                    None => panic!("vectors.txt: a zigzag.zigzag record with no image"),
                };
                assert_eq!(
                    zigzag(one_i32(&r.args)),
                    want,
                    "zigzag disagrees for {}",
                    r.args.join(" ")
                );
            }
            "zigzag.unzigzag" => {
                inputs.saw();
                let want = match r.field(0).first() {
                    Some(v) => {
                        v.parse::<i32>().expect("vectors.txt: unzigzag value does not fit i32")
                    }
                    None => panic!("vectors.txt: a zigzag.unzigzag record with no value"),
                };
                assert_eq!(
                    unzigzag(one_u32(&r.args)),
                    want,
                    "unzigzag disagrees for {}",
                    r.args.join(" ")
                );
            }
            "zigzag.encode" => {
                inputs.saw();
                let mut got: Vec<u8> = Vec::new();
                encode_i32(one_i32(&r.args), &mut got);
                assert!(got.len() <= 5, "a zigzag encoding exceeded five bytes");
                assert_eq!(got, u8s(r.field(0)), "encode_i32 disagrees for {}", r.args.join(" "));
            }
            "zigzag.decode" => {
                inputs.saw();
                let got = decode_i32(&u8s(&r.args));
                assert_eq!(
                    got,
                    expected_zigzag_decode(r),
                    "decode_i32 disagrees for {}",
                    r.args.join(" ")
                );
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no zigzag records");
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

/// The transparent frame codec byte for byte against the extracted
/// `encode_stuffed`/`parse_stuffed`, and the state machine replayed against a Rust
/// `StuffedChannel<Q>` from the records the extraction computed at the same queue: `prefix` is
/// `stuffed_channel.ringbuffer` (`StuffedChannel::new` over the extracted ring buffer record) or
/// `stuffed_channel.vecqueue` (`StuffedChannel::with_queue` over the extracted `VecQueue` record).
/// `wire` and `in_flight` are private, so the comparison is at the result, the payload and
/// `queued()`.
fn stuffed_channel_agrees_with_extracted_vectors_at<Q: BoundedQueue<Frame>>(
    prefix: &str,
    new: fn(usize) -> StuffedChannel<Q>,
    inputs: &mut Inputs,
) {
    let records = parse_vectors();
    let mut ch: StuffedChannel<Q> = new(1);
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
    assert!(inputs.count > before, "vectors.txt carries no stuffed-channel records for {prefix}");
}

fn new_ring_buffer_stuffed_channel(cap: usize) -> StuffedChannel<RingBuffer<Frame>> {
    StuffedChannel::new(cap)
}

fn new_vec_queue_stuffed_channel(cap: usize) -> StuffedChannel<VecQueue<Frame>> {
    StuffedChannel::with_queue(cap)
}

/// The transparent codec and `StuffedChannel::new` (the ring buffer channel) against their own
/// extracted translation. The `encode_stuffed` records also pin the property the channel's
/// `encode_frame` records cannot show: the flag byte appears in a stuffed frame only as its last
/// byte.
#[test]
fn stuffed_channel_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("stuffed_channel_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "stuffed_channel.encode_stuffed" => {
                inputs.saw();
                let payload = u8s(&r.args);
                let Ok(len) = u32::try_from(payload.len()) else {
                    panic!("vectors.txt: an encode_stuffed payload longer than u32::MAX");
                };
                let mut got: Vec<u8> = Vec::new();
                encode_stuffed(&payload, len, &mut got);
                let expected = u8s(r.field(0));
                assert_eq!(got, expected, "encode_stuffed disagrees");
                // Transparency, on the bytes themselves: the flag is the frame terminator and
                // nothing else. The corresponding assertion about `encode_frame` would fail.
                assert_eq!(got.last(), Some(&MARKER), "a stuffed frame must end with the flag");
                let body = got.get(..got.len() - 1).expect("a stuffed frame is never empty");
                assert!(
                    !body.contains(&MARKER),
                    "the flag byte appears inside a stuffed frame: {body:?}"
                );
            }
            "stuffed_channel.parse_stuffed" => {
                inputs.saw();
                let got = parse_stuffed(&u8s(&r.args));
                match r.status(0) {
                    "some" => assert_eq!(
                        got,
                        Some((u8s(r.field(1)), one_usize(r.field(2)))),
                        "parse_stuffed disagrees"
                    ),
                    "none" => assert_eq!(got, None, "parse_stuffed should have returned None"),
                    other => panic!("vectors.txt: unexpected parse_stuffed result {other}"),
                }
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no stuffed frame-codec records");
    stuffed_channel_agrees_with_extracted_vectors_at(
        "stuffed_channel.ringbuffer",
        new_ring_buffer_stuffed_channel,
        &mut inputs,
    );
    inputs.report();
}

/// `StuffedChannel::with_queue` at `VecQueue<Frame>` against its own extracted translation.
#[test]
fn stuffed_channel_agrees_with_extracted_vectors_vec_queue() {
    let mut inputs = Inputs::new("stuffed_channel_agrees_with_extracted_vectors_vec_queue");
    stuffed_channel_agrees_with_extracted_vectors_at(
        "stuffed_channel.vecqueue",
        new_vec_queue_stuffed_channel,
        &mut inputs,
    );
    inputs.report();
}

/// The receive path against its own extracted translation, over one queue record. `feed` records
/// carry the drop and queued counts after the feed, `poll` records the popped frame and both counts,
/// so every observer the extraction exposes is compared at every step. The private `finish_run` has
/// no records and cannot: a test cannot call it without widening the crate's API, and it is covered
/// by its bridge row (`Bridge.receiver.finish_run_refines`) instead.
fn receiver_agrees_with_extracted_vectors_at<Q: BoundedQueue<Frame>>(
    prefix: &str,
    new: fn(usize) -> Receiver<Q>,
    inputs: &mut Inputs,
) {
    let records = parse_vectors();
    let mut rcv: Receiver<Q> = new(1);
    let mut started = false;
    let before = inputs.count;
    for r in &records {
        let Some(op) = r.op.strip_prefix(prefix) else {
            continue;
        };
        match op {
            ".new" => {
                rcv = new(one_u32(&r.args) as usize);
                started = true;
                inputs.saw();
                assert_eq!(rcv.dropped(), one_usize(r.field(0)), "dropped disagrees at new");
                assert_eq!(rcv.queued(), one_usize(r.field(1)), "queued disagrees at new");
            }
            ".feed" => {
                assert!(started, "vectors.txt: a feed record before any .new for {prefix}");
                inputs.saw();
                rcv.feed(&u8s(&r.args));
                assert_eq!(rcv.dropped(), one_usize(r.field(0)), "dropped disagrees after feed");
                assert_eq!(rcv.queued(), one_usize(r.field(1)), "queued disagrees after feed");
            }
            ".poll" => {
                assert!(started, "vectors.txt: a poll record before any .new for {prefix}");
                inputs.saw();
                let got = rcv.poll();
                match r.status(0) {
                    "some" => assert_eq!(got, Some(u8s(r.field(1))), "poll payload disagrees"),
                    "none" => assert_eq!(got, None, "poll should have returned None"),
                    other => panic!("vectors.txt: unexpected poll result {other}"),
                }
                assert_eq!(rcv.dropped(), one_usize(r.field(2)), "dropped disagrees after poll");
                assert_eq!(rcv.queued(), one_usize(r.field(3)), "queued disagrees after poll");
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no receiver records for {prefix}");
}

fn new_ring_buffer_receiver(cap: usize) -> Receiver<RingBuffer<Frame>> {
    Receiver::new(cap)
}

fn new_vec_queue_receiver(cap: usize) -> Receiver<VecQueue<Frame>> {
    Receiver::with_queue(cap)
}

/// `Receiver::new` (the ring buffer receiver) against its own extracted translation. The wires the
/// vectors feed are deliberately not all well formed: a bumped check byte, a truncated frame, the
/// fused run the next flag closes, adjacent flags (RFC 1662 4.1's idle case), a garbage prefix both
/// with and without its terminating flag, and a full-queue refusal at capacity 1.
#[test]
fn receiver_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("receiver_agrees_with_extracted_vectors");
    receiver_agrees_with_extracted_vectors_at(
        "receiver.ringbuffer",
        new_ring_buffer_receiver,
        &mut inputs,
    );
    inputs.report();
}

/// `Receiver::with_queue` at `VecQueue<Frame>` against its own extracted translation.
#[test]
fn receiver_agrees_with_extracted_vectors_vec_queue() {
    let mut inputs = Inputs::new("receiver_agrees_with_extracted_vectors_vec_queue");
    receiver_agrees_with_extracted_vectors_at(
        "receiver.vecqueue",
        new_vec_queue_receiver,
        &mut inputs,
    );
    inputs.report();
}

/// One stuffed frame's wire bytes, flag terminator included.
fn stuffed_wire(payload: &[u8]) -> Vec<u8> {
    let mut w: Vec<u8> = Vec::new();
    let len = u32::try_from(payload.len()).expect("a test payload shorter than u32::MAX");
    encode_stuffed(payload, len, &mut w);
    w
}

/// Drain every accepted frame from a receiver, front first.
fn drain<Q: BoundedQueue<Frame>>(r: &mut Receiver<Q>) -> Vec<Frame> {
    let mut out: Vec<Frame> = Vec::new();
    let mut n = r.queued();
    while n > 0 {
        match r.poll() {
            Some(f) => out.push(f),
            None => return out,
        }
        n -= 1;
    }
    out
}

/// The resynchronizing receive path on the six scenarios that distinguish it from
/// `StuffedChannel::deliver`: a clean stream, a corrupted run, an unterminated tail, adjacent
/// flags, a marker-bearing payload, and a full-queue refusal. Generic over the queue, so both
/// implementations are exercised through the same script.
fn receiver_resyncs_at<Q: BoundedQueue<Frame>>(inputs: &mut Inputs) {
    // A clean two-frame stream: both accepted, in order, nothing dropped.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    let mut wire = stuffed_wire(&[1, 2, 3]);
    wire.extend_from_slice(&stuffed_wire(&[9]));
    r.feed(&wire);
    assert_eq!(drain(&mut r), vec![vec![1, 2, 3], vec![9]], "a clean stream is accepted in order");
    assert_eq!(r.dropped(), 0, "a clean stream drops nothing");
    inputs.saw();

    // Chunking invariance: the same wire fed one byte at a time gives the same result.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    let mut i = 0usize;
    while i < wire.len() {
        let b = *wire.get(i).expect("i < wire.len()");
        r.feed(&[b]);
        i += 1;
    }
    assert_eq!(drain(&mut r), vec![vec![1, 2, 3], vec![9]], "feed is chunking-invariant");
    assert_eq!(r.dropped(), 0);
    inputs.saw();

    // A corrupted check byte: the run is dropped, and the receiver resynchronizes on the frame
    // that follows rather than wedging.
    let mut bad = stuffed_wire(&[7, 7]);
    let last = bad.len() - 2;
    let b = *bad.get(last).expect("a stuffed frame has at least two bytes");
    let slot = bad.get_mut(last).expect("a stuffed frame has at least two bytes");
    *slot = b ^ 0x01;
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    r.feed(&bad);
    r.feed(&stuffed_wire(&[5]));
    assert_eq!(drain(&mut r), vec![vec![5]], "the frame after a corrupted run is still accepted");
    assert_eq!(r.dropped(), 1, "a corrupted run is one drop");
    inputs.saw();

    // An unterminated tail buffers and is neither accepted nor dropped: there is no flag yet, so
    // there is no run to judge. This is the qualifier `Receiver.quiet_before_flag` states.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    let clean = stuffed_wire(&[4, 4]);
    let head = clean.get(..clean.len() - 1).expect("a stuffed frame is never empty");
    r.feed(head);
    assert_eq!(r.queued(), 0, "an unterminated run is not accepted");
    assert_eq!(r.dropped(), 0, "an unterminated run is not dropped either");
    // The terminator completes it.
    r.feed(&[MARKER]);
    assert_eq!(drain(&mut r), vec![vec![4, 4]], "the flag completes the buffered run");
    assert_eq!(r.dropped(), 0);
    inputs.saw();

    // Adjacent flags are idle (RFC 1662 §4.1): an empty run is ignored, never counted as a drop.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    r.feed(&[MARKER, MARKER, MARKER]);
    assert_eq!(r.queued(), 0, "flags alone accept nothing");
    assert_eq!(r.dropped(), 0, "flags alone drop nothing");
    r.feed(&stuffed_wire(&[8]));
    assert_eq!(drain(&mut r), vec![vec![8]], "idle flags leave the receiver usable");
    assert_eq!(r.dropped(), 0);
    inputs.saw();

    // A marker-bearing payload: the stuffing is what makes this work at all. The wire carries the
    // flag only as its terminator, so the receiver sees exactly one run.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    let w = stuffed_wire(&[MARKER, MARKER]);
    let body = w.get(..w.len() - 1).expect("a stuffed frame is never empty");
    assert!(!body.contains(&MARKER), "a stuffed body carries no flag: {body:?}");
    r.feed(&w);
    assert_eq!(drain(&mut r), vec![vec![MARKER, MARKER]], "a marker-bearing payload round-trips");
    assert_eq!(r.dropped(), 0);
    inputs.saw();

    // A garbage prefix must be FLAG-TERMINATED to resynchronize. Unterminated, it fuses with the
    // next frame's body and that frame is lost -- the qualifier `Receiver.resync_progress` carries.
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    r.feed(&[3, 4, 5]);
    r.feed(&stuffed_wire(&[9]));
    assert_eq!(r.queued(), 0, "an unterminated garbage prefix fuses with the next frame");
    assert_eq!(r.dropped(), 1, "and that fused run is the one drop");
    let mut r: Receiver<Q> = Receiver::with_queue(4);
    r.feed(&[3, 4, 5, MARKER]);
    r.feed(&stuffed_wire(&[9]));
    assert_eq!(drain(&mut r), vec![vec![9]], "a flag-terminated prefix resynchronizes");
    assert_eq!(r.dropped(), 1, "the garbage run itself is the one drop");
    inputs.saw();

    // A full queue refuses the push, and that refusal counts as a drop -- the same conflation
    // `DeliverFail` already makes, and what keeps `run_exactly_one` unconditional.
    let mut r: Receiver<Q> = Receiver::with_queue(1);
    r.feed(&stuffed_wire(&[1]));
    r.feed(&stuffed_wire(&[2]));
    assert_eq!(r.queued(), 1, "the second frame does not fit");
    assert_eq!(r.dropped(), 1, "a full-queue refusal is a drop");
    assert_eq!(drain(&mut r), vec![vec![1]], "the frame that fit is the one kept");
    inputs.saw();
}

/// The receive path at the default `RingBuffer<Frame>` queue.
#[test]
fn receiver_resyncs() {
    let mut inputs = Inputs::new("receiver_resyncs");
    receiver_resyncs_at::<RingBuffer<Frame>>(&mut inputs);
    // `new` and `with_queue` agree at the default queue: the two-constructor pattern.
    let mut a: Receiver<RingBuffer<Frame>> = Receiver::new(2);
    let mut b: Receiver<RingBuffer<Frame>> = Receiver::with_queue(2);
    let w = stuffed_wire(&[6, 6]);
    a.feed(&w);
    b.feed(&w);
    assert_eq!(drain(&mut a), drain(&mut b), "new and with_queue agree at the default queue");
    inputs.saw();
    inputs.report();
}

/// The same script at `VecQueue<Frame>`: the substitution the Lean `feed_spec_RB`/`_VQ` pair
/// states, executed.
#[test]
fn receiver_resyncs_vec_queue() {
    let mut inputs = Inputs::new("receiver_resyncs_vec_queue");
    receiver_resyncs_at::<VecQueue<Frame>>(&mut inputs);
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
/// The `unstuff` outcome a vector record states, read back as the Rust `Result`.
fn expected_unstuff(r: &Record) -> Result<(Vec<u8>, usize), UnstuffError> {
    match r.status(0) {
        "ok" => {
            let rest = r.rest(0);
            let used = match rest.last() {
                Some(u) => {
                    u.parse::<usize>().expect("vectors.txt: consumed count does not fit usize")
                }
                None => panic!("vectors.txt: an ok unstuff record with no consumed count"),
            };
            let payload = match rest.get(..rest.len() - 1) {
                Some(p) => u8s(p),
                None => panic!("vectors.txt: an ok unstuff record with no payload field"),
            };
            Ok((payload, used))
        }
        "err" => match r.rest(0).first() {
            Some(v) if v == "truncated" => Err(UnstuffError::Truncated),
            Some(v) if v == "badescape" => Err(UnstuffError::BadEscape),
            _ => panic!("vectors.txt: an unstuff error record with no known variant"),
        },
        other => panic!("vectors.txt: unexpected unstuff result {other}"),
    }
}

/// HDLC byte stuffing against the extracted `stuff`, `encode_frame` and `unstuff`: the stuffed
/// payload and the framed payload byte for byte, and every `unstuff` outcome -- success with and
/// without residual bytes, both truncation exits and a bad escape -- as the result, the consumed
/// count and the error variant.
#[test]
fn stuff_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("stuff_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    for r in &records {
        match r.op.as_str() {
            "stuff.stuff" => {
                inputs.saw();
                let mut got: Vec<u8> = Vec::new();
                stuff(&u8s(&r.args), &mut got);
                assert_eq!(got, u8s(r.field(0)), "stuff disagrees for {}", r.args.join(" "));
            }
            "stuff.encode_frame" => {
                inputs.saw();
                let mut got: Vec<u8> = Vec::new();
                stuff_encode_frame(&u8s(&r.args), &mut got);
                assert_eq!(got, u8s(r.field(0)), "encode_frame disagrees for {}", r.args.join(" "));
            }
            "stuff.unstuff" => {
                inputs.saw();
                let got = unstuff(&u8s(&r.args));
                assert_eq!(got, expected_unstuff(r), "unstuff disagrees for {}", r.args.join(" "));
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no stuff records");
    inputs.report();
}

/// `SeqNum` against the extracted `new`/`get`/`succ`/`add`/`dist`/`lt`, on vectors that cross the
/// wrap boundary in both directions.
///
/// Two groups of records are the reason this test exists rather than being filler. The `lt` records
/// carry the **non-transitive triple**: `lt(0, 20000)`, `lt(20000, 40000)` and `lt(40000, 0)` all
/// hold while `lt(0, 40000)` does not, a genuine three-cycle, and this is where the compiled Rust is
/// held to it. The pair `0` and `32768` is RFC 1982 §3.2's undefined region -- exactly half the space
/// apart, with `lt` false in both directions -- and no proof in this repository states that about the
/// *Rust*, so these two records are the only place it is checked.
#[test]
fn seq_num_agrees_with_extracted_vectors() {
    let mut inputs = Inputs::new("seq_num_agrees_with_extracted_vectors");
    let records = parse_vectors();
    let before = inputs.count;
    let mut cycle_edges = 0usize;
    let mut undefined_pairs = 0usize;
    for r in &records {
        match r.op.as_str() {
            "seq_num.new" => {
                inputs.saw();
                let n = one_u16(&r.args);
                assert_eq!(
                    SeqNum::new(n).get(),
                    one_u16(r.field(0)),
                    "SeqNum::new disagrees for {n}"
                );
            }
            "seq_num.get" => {
                inputs.saw();
                let n = one_u16(&r.args);
                assert_eq!(SeqNum::new(n).get(), one_u16(r.field(0)), "get disagrees for {n}");
            }
            "seq_num.succ" => {
                inputs.saw();
                let n = one_u16(&r.args);
                assert_eq!(
                    SeqNum::new(n).succ().get(),
                    one_u16(r.field(0)),
                    "succ disagrees for {n}"
                );
            }
            "seq_num.add" => {
                inputs.saw();
                let (n, k) = two_u16(&r.args);
                assert_eq!(
                    SeqNum::new(n).add(k).get(),
                    one_u16(r.field(0)),
                    "add disagrees for {n} {k}"
                );
            }
            "seq_num.dist" => {
                inputs.saw();
                let (a, b) = two_u16(&r.args);
                assert_eq!(
                    SeqNum::new(a).dist(SeqNum::new(b)),
                    one_u16(r.field(0)),
                    "dist disagrees for {a} {b}"
                );
            }
            "seq_num.lt" => {
                inputs.saw();
                let (a, b) = two_u16(&r.args);
                let want = flag(r, 0);
                assert_eq!(SeqNum::new(a).lt(SeqNum::new(b)), want, "lt disagrees for {a} {b}");
                // The three edges of the non-transitive cycle, and the two undefined-region pairs.
                if (a, b) == (0, 20000) || (a, b) == (20000, 40000) || (a, b) == (40000, 0) {
                    assert!(want, "the cycle edge lt({a}, {b}) is no longer true");
                    cycle_edges += 1;
                }
                if (a, b) == (0, 32768) || (a, b) == (32768, 0) {
                    assert!(!want, "the undefined-region pair lt({a}, {b}) is no longer false");
                    undefined_pairs += 1;
                }
            }
            _ => {}
        }
    }
    assert!(inputs.count > before, "vectors.txt carries no seq_num records");
    // A vector set that lost either group would still pass every assertion above, so the two groups
    // are counted rather than assumed.
    assert_eq!(cycle_edges, 3, "vectors.txt has lost an edge of the non-transitive cycle");
    assert_eq!(undefined_pairs, 2, "vectors.txt has lost an undefined-region pair");
    assert!(
        !SeqNum::new(0).lt(SeqNum::new(40000)),
        "lt(0, 40000) must be false: that is what makes the cycle non-transitive"
    );
    inputs.report();
}

/// of one -- would leave every test passing while checking less. This asserts instead that each
/// translated operation is present with every branch, both queue records and both channel queues,
/// the zero-capacity traces, the compact CRC record, the out-of-domain class, and that no record
/// carries a panic.
#[test]
fn extracted_vectors_cover_every_translated_operation() {
    let mut inputs = Inputs::new("extracted_vectors_cover_every_translated_operation");
    let records = parse_vectors();
    #[rustfmt::skip]
    let branches: [(&str, &str, &str); 50] = [
        ("ringbuffer.push", "ok", ""), ("ringbuffer.push", "err", ""),
        ("ringbuffer.pop", "some", ""), ("ringbuffer.pop", "none", ""),
        ("vecqueue.push", "ok", ""), ("vecqueue.push", "err", ""),
        ("vecqueue.pop", "some", ""), ("vecqueue.pop", "none", ""),
        ("varint.decode", "ok", ""), ("varint.decode", "err", "truncated"),
        ("varint.decode", "err", "overlong"), ("varint.decode.out_of_domain", "err", "overlong"),
        ("zigzag.decode", "ok", ""), ("zigzag.decode", "err", "truncated"),
        ("zigzag.decode", "err", "overlong"),
        ("channel.parse_frame", "some", ""), ("channel.parse_frame", "none", ""),
        ("channel.ringbuffer.send", "ok", ""), ("channel.ringbuffer.send", "err", ""),
        ("channel.ringbuffer.deliver", "ok", ""), ("channel.ringbuffer.deliver", "err", ""),
        ("channel.ringbuffer.take", "some", ""), ("channel.ringbuffer.take", "none", ""),
        ("channel.vecqueue.send", "ok", ""), ("channel.vecqueue.send", "err", ""),
        ("channel.vecqueue.deliver", "ok", ""), ("channel.vecqueue.deliver", "err", ""),
        ("channel.vecqueue.take", "some", ""), ("channel.vecqueue.take", "none", ""),
        ("stuff.unstuff", "ok", ""), ("stuff.unstuff", "err", "truncated"),
        ("stuff.unstuff", "err", "badescape"),
        ("stuffed_channel.parse_stuffed", "some", ""), ("stuffed_channel.parse_stuffed", "none", ""),
        ("stuffed_channel.ringbuffer.send", "ok", ""), ("stuffed_channel.ringbuffer.send", "err", ""),
        ("stuffed_channel.ringbuffer.deliver", "ok", ""),
        ("stuffed_channel.ringbuffer.deliver", "err", ""),
        ("stuffed_channel.ringbuffer.take", "some", ""), ("stuffed_channel.ringbuffer.take", "none", ""),
        ("stuffed_channel.vecqueue.send", "ok", ""), ("stuffed_channel.vecqueue.send", "err", ""),
        ("stuffed_channel.vecqueue.deliver", "ok", ""), ("stuffed_channel.vecqueue.deliver", "err", ""),
        ("stuffed_channel.vecqueue.take", "some", ""), ("stuffed_channel.vecqueue.take", "none", ""),
        ("receiver.ringbuffer.poll", "some", ""), ("receiver.ringbuffer.poll", "none", ""),
        ("receiver.vecqueue.poll", "some", ""), ("receiver.vecqueue.poll", "none", ""),
    ];
    for (op, status, detail) in branches {
        inputs.saw();
        assert!(
            count_records(&records, op, status, detail) > 0,
            "vectors.txt has no {status} {detail} record for {op}"
        );
    }
    #[rustfmt::skip]
    let total: [&str; 26] = [
        "ringbuffer.new", "vecqueue.new", "channel.ringbuffer.new", "channel.vecqueue.new",
        "varint.encode", "crc8.bits", "crc8.table", "channel.encode_frame",
        "stuff.stuff", "stuff.encode_frame",
        "zigzag.encode", "zigzag.zigzag", "zigzag.unzigzag",
        "seq_num.new", "seq_num.get", "seq_num.succ", "seq_num.add", "seq_num.dist", "seq_num.lt",
        "stuffed_channel.encode_stuffed",
        "stuffed_channel.ringbuffer.new", "stuffed_channel.vecqueue.new",
        "receiver.ringbuffer.new", "receiver.vecqueue.new",
        "receiver.ringbuffer.feed", "receiver.vecqueue.feed",
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
