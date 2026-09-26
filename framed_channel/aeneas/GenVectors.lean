-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneas.Extracted.Funs

/-!
# GenVectors: the differential vectors, computed by evaluating the Aeneas extraction

The generator behind `../certificate/vectors.txt`. It sits outside `FramedChannelAeneas/`, so neither
the library glob nor the axiom-audit module scan sweeps it: it contains no theorem, states no
obligation and carries no `#print axioms` record. It only *evaluates* the extracted definitions in
`FramedChannelAeneas/Extracted/Funs.lean` -- what Charon and Aeneas produced from `../rust/src` --
and prints the results. `../rust/tests/differential.rs` compares the compiled Rust against the
committed file.

Run it with `lake env lean --run GenVectors.lean` from `aeneas/` (`../scripts/refresh-vectors.sh` does, and
`bash ../check.sh` regenerates into a temporary file and diffs). It is interpreted, not a
`lean_exe`: a native executable would compile Aeneas and Mathlib to C.

## What agreement with the Rust establishes

For every recorded input, the pinned `rustc` build of `../rust` and Lean's evaluation of the
Charon/Aeneas output of the same source return the same observable result. That is direct evidence
against a translation fault (rustc MIR, Charon, Aeneas) **on those inputs**. It is testing, not
proof: nothing about other inputs, about paths no record reaches, about release-profile arithmetic,
or about the Lean interpreter that computed the values (the extracted `loop` is a
`partial_fixpoint`, which the interpreter runs and the kernel does not reduce). The proofs relating
the extraction to the models are in `FramedChannelAeneas/Bridge/`; together with this agreement they
give model-to-Rust agreement on the same inputs, which is why no second, hand-model vector source
exists.

## Grammar

One record per line, `<op> <input tokens...> => <field>; <field>; ...`. `#`-prefixed lines are
comments, blank lines are skipped, scalars are decimal, list fields are whitespace-separated (an
empty field is the empty list). A result field is the Rust result as the extraction returns it:
`ok`/`err` for `Result<(), _>`, `ok <scalars>` or `err <variant>` for a `Result` with a payload,
`some`/`none` for an `Option`. An operation whose extracted evaluation fails is recorded as
`panic <error>` (or `div`), never aborting the generator, so a translation divergence shows up as a
record the Rust test names. Stateful traces replay in file order: a `.new` record resets the state.
-/

open Aeneas Aeneas.Std Result framed_channel

namespace GenVectors

/-! ## Inputs and rendering -/

def u8 (n : Nat) : Std.U8 :=
  UScalar.ofNatCore (n % 256) (by have := Nat.mod_lt n (show 256 > 0 by decide); simp; omega)

def u32 (n : Nat) : Std.U32 :=
  UScalar.ofNatCore (n % 2 ^ 32)
    (by have := Nat.mod_lt n (show 2 ^ 32 > 0 by decide); simp; omega)

def u16 (n : Nat) : Std.U16 :=
  UScalar.ofNatCore (n % 2 ^ 16)
    (by have := Nat.mod_lt n (show 2 ^ 16 > 0 by decide); simp; omega)

def usize (n : Nat) : Std.Usize :=
  if h : n ≤ Usize.max then UScalar.ofNatCore n (by simp; scalar_tac) else 0#usize

/-- A machine `i32` from an `Int` inside the signed range. The `else` arm is unreachable for every
input below and mirrors `usize`'s own total-function shape. -/
def i32 (n : Int) : Std.I32 :=
  if h : -2 ^ 31 ≤ n ∧ n < 2 ^ 31 then
    IScalar.ofIntCore n (by simp only [IScalarTy.numBits]; omega)
  else 0#i32

def vecOf (ns : List Nat) : alloc.vec.Vec Std.U8 :=
  if h : ns.length ≤ Usize.max then alloc.vec.Vec.from (ns.map u8) (by simpa using h)
  else alloc.vec.Vec.new Std.U8

def sliceOf (ns : List Nat) : Slice Std.U8 := alloc.vec.Vec.deref (vecOf ns)

def natsToStr (ns : List Nat) : String := String.intercalate " " (ns.map toString)

def u8sToStr (v : List Std.U8) : String := natsToStr (v.map (·.val))

def u32sToStr (v : List Std.U32) : String := natsToStr (v.map (·.val))

def boolToStr (b : Bool) : String := if b then "1" else "0"

/-- One record: the left-hand side, ` => `, and the `; `-separated fields, with no trailing
whitespace (the file must survive a hook that strips it). -/
def mkRec (lhs : String) (fields : List String) : String :=
  (lhs ++ " => " ++ String.intercalate "; " fields).trimAsciiEnd.toString

def mkLhs (op : String) (args : String) : String :=
  if args.isEmpty then op else op ++ " " ++ args

/-- Evaluate `r`; on `ok`, render with `f`, otherwise record the failure. -/
def fields {α : Type} (r : Result α) (f : α → List String) : List String :=
  match r.match with
  | .ok a => f a
  | .div => ["div"]
  | .vis (.fail e) _ => [s!"panic {repr e}"]

/-- Evaluate a stateful step: on `ok`, the rendered fields and the new state; otherwise the failure
record and the unchanged state. -/
def stepWith {α σ : Type} (s : σ) (r : Result α) (f : α → List String × σ) : List String × σ :=
  match r.match with
  | .ok a => f a
  | .div => (["div"], s)
  | .vis (.fail e) _ => ([s!"panic {repr e}"], s)

/-- Fold a step function over a trace, one record per operation. -/
def runOps {σ ω : Type} (step : σ → ω → String × σ) (s : σ) : List ω → List String
  | [] => []
  | o :: rest =>
    let (line, s') := step s o
    line :: runOps step s' rest

/-! ## Queues, through the extracted `BoundedQueue` records at `u32`

Both queues are driven through their extracted trait records, exactly the functions the Rust
`BoundedQueue<u32>` impls compile from. The state is observed through the same record: `contents`
(an extracted loop for the ring buffer), `is_empty`, `is_full`, `len` and `capacity`. -/

abbrev rbRecord : queue.BoundedQueue (ring_buffer.RingBuffer Std.U32) Std.U32 :=
  ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue core.default.DefaultU32
    core.clone.CloneU32

abbrev vqRecord : queue.BoundedQueue (queue.VecQueue Std.U32) Std.U32 :=
  queue.VecQueue.Insts.Framed_channelQueueBoundedQueue core.clone.CloneU32

inductive QOp where
  | push (x : Nat)
  | pop

/-- The observed state: `contents; is_empty; is_full; len; capacity`. -/
def qState {S : Type} (inst : queue.BoundedQueue S Std.U32) (s : S) : Result (List String) := do
  let c ← inst.contents s
  let e ← inst.is_empty s
  let f ← inst.is_full s
  let n ← inst.len s
  let k ← inst.capacity s
  ok [u32sToStr c.val, boolToStr e, boolToStr f, toString n.val, toString k.val]

def qStep {S : Type} (pfx : String) (inst : queue.BoundedQueue S Std.U32) (s : S) (op : QOp) :
    String × S :=
  match op with
  | .push x =>
    let lhs := s!"{pfx}.push {x}"
    let (fs, s') := stepWith s (do
        let (r, s') ← inst.push s (u32 x)
        let st ← qState inst s'
        ok (r, st, s'))
      fun (r, st, s') =>
        ((match r with | .Ok _ => "ok" | .Err _ => "err") :: st, s')
    (mkRec lhs fs, s')
  | .pop =>
    let lhs := s!"{pfx}.pop"
    let (fs, s') := stepWith s (do
        let (o, s') ← inst.pop s
        let st ← qState inst s'
        ok (o, st, s'))
      fun (o, st, s') =>
        ((match o with | some y => s!"some {y.val}" | none => "none") :: st, s')
    (mkRec lhs fs, s')

def qTrace {S : Type} (pfx : String) (inst : queue.BoundedQueue S Std.U32) (cap : Nat)
    (ops : List QOp) : List String :=
  let lhs := s!"{pfx}.new {cap}"
  match (do let s ← inst.with_capacity (usize cap); let st ← qState inst s; ok (s, st)).match with
  | .ok (s, st) => mkRec lhs st :: runOps (qStep pfx inst) s ops
  | .div => [mkRec lhs ["div"]]
  | .vis (.fail e) _ => [mkRec lhs [s!"panic {repr e}"]]

/-- Fill past full, drain past empty, interleave: at `cap = 1` every second push is refused. -/
def traceCap1 : List QOp :=
  [.push 1, .push 2, .pop, .pop, .push 3, .pop, .push 4, .push 5, .pop, .pop]

/-- Fill past full, drain past empty, interleave, and three more full cycles, so the ring buffer's
indices wrap around the backing store. -/
def traceCap3 : List QOp :=
  [.push 1, .push 2, .push 3, .push 4, .pop, .pop, .pop, .pop,
   .push 5, .push 6, .pop, .push 7, .push 8, .push 9, .pop, .pop, .pop, .pop,
   .push 10, .push 11, .push 12, .pop, .pop, .pop,
   .push 13, .push 14, .push 15, .pop, .pop, .pop,
   .push 16, .push 17, .push 18, .push 19, .pop, .pop, .pop, .pop]

/-- A zero requested capacity: the ring buffer rounds it up to one, `VecQueue` refuses every push.
The one recorded difference between the queues, now computed on both. -/
def traceCap0 : List QOp :=
  [.push 1, .pop, .push 2, .push 3, .pop]

/-! ## Varint -/

def varintValues : List Nat :=
  [0, 1, 126, 127, 128, 255, 300, 16383, 16384, 2097151, 2097152, 268435455, 4294967295]

/-- The extracted `encode_u32` of `n` into an empty vector, as naturals (the empty list when the
evaluation fails; that failure is recorded by the `varint.encode` record itself). -/
def encodeBytes (n : Nat) : List Nat :=
  match (varint.encode_u32 (u32 n) (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => v.val.map (·.val)
  | _ => []

def properPrefixes (l : List Nat) : List (List Nat) :=
  (List.range l.length).map (fun k => l.take k)

/-- Each complete encoding, its proper prefixes (`Err(Truncated)`), the encoding with a trailing
byte (`Ok` with the byte left unconsumed), and fuel exhaustion (`Err(Overlong)`). -/
def varintDecodeInputs : List (List Nat) :=
  let perValue := varintValues.flatMap fun n =>
    let e := encodeBytes n
    (e :: properPrefixes e) ++ [e ++ [42]]
  (perValue ++ [[128, 128, 128, 128, 128], [128, 128, 128, 128, 128, 1]]).eraseDups

/-- A fifth group too wide for a `u32`: the Rust and the extraction return `Err(Overlong)`, where
the hand-written `Nat` model decodes a value at or above `2 ^ 32` (the model divergence the bridge
states as `decode_err_iff`). Labelled so the class cannot silently disappear. -/
def varintOutOfDomainInputs : List (List Nat) :=
  [[128, 128, 128, 128, 16], [128, 128, 128, 128, 127]]

def decodeFields (bs : List Nat) : List String :=
  fields (varint.decode_u32 (sliceOf bs)) fun r =>
    match r with
    | .Ok (v, k) => [s!"ok {v.val} {k.val}"]
    | .Err .Truncated => ["err truncated"]
    | .Err .Overlong => ["err overlong"]

/-! ## Zigzag: the signed varint over `i32`

The values cover zero, both signs either side of the one-byte and two-byte encoding boundaries, and
both extremes of the range (`i32::MIN` and `i32::MAX`) -- the signed counterpart of
`varintValues`. -/

/-- Signed inputs: zero, both signs across each byte boundary, and both ends of the `i32` range. -/
def zigzagValues : List Int :=
  [0, -1, 1, -2, 63, -64, 64, -65, 8191, -8192, 8192, -8193, 2147483647, -2147483648]

/-- The extracted `encode_i32` of `n` into an empty vector, as naturals (the empty list when the
evaluation fails; that failure is recorded by the `zigzag.encode` record itself). -/
def zigzagEncodeBytes (n : Int) : List Nat :=
  match (zigzag.encode_i32 (i32 n) (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => v.val.map (·.val)
  | _ => []

/-- The extracted `zigzag` of `n` (`0` when the evaluation fails, which the `zigzag.zigzag` record
itself reports); the input list for the `unzigzag` records. -/
def zigzagMapped (n : Int) : Nat :=
  match (zigzag.zigzag (i32 n)).match with
  | .ok v => v.val
  | _ => 0

/-- Decode inputs: each complete encoding, each of its proper prefixes (`Truncated`), each encoding
followed by a trailing byte, and the two `Overlong` wires -- the same three classes
`varintDecodeInputs` covers, since `decode_i32` forwards the varint's own errors unchanged. -/
def zigzagDecodeInputs : List (List Nat) :=
  let perValue := zigzagValues.flatMap fun n =>
    let e := zigzagEncodeBytes n
    (e :: properPrefixes e) ++ [e ++ [42]]
  (perValue ++ [[128, 128, 128, 128, 128], [128, 128, 128, 128, 128, 1]]).eraseDups

def zigzagDecodeFields (bs : List Nat) : List String :=
  fields (zigzag.decode_i32 (sliceOf bs)) fun r =>
    match r with
    | .Ok (v, k) => [s!"ok {v.val} {k.val}"]
    | .Err .Truncated => ["err truncated"]
    | .Err .Overlong => ["err overlong"]

/-! ## Crc8 -/

def asciiBytes (s : String) : List Nat := s.toList.map Char.toNat

/-! ## Stuff: HDLC byte stuffing

The payloads deliberately include both reserved bytes, so the escape branches are exercised, and the
`unstuff` inputs cover all three outcomes: a well-formed frame with and without residual bytes, a
wire with no terminating flag (`err truncated`), a wire ending inside an escape (`err truncated`
again, by the second of the extracted code's two truncation exits) and a bad escape
(`err badescape`). -/

/-- Payloads for the encode side: empty, plain, each reserved byte alone, both together, and a
payload that is nothing but reserved bytes (the worst case for the length bound). -/
def stuffPayloads : List (List Nat) :=
  [ [], [1, 2, 3], [0x7E], [0x7D], [1, 0x7E, 2, 0x7D, 3], [0x7E, 0x7D, 0x7E],
    asciiBytes "framed_channel" ]

/-- The extracted `stuff` and `encode_frame` of a payload, into an empty vector. -/
def stuffRecs (ns : List Nat) : List String :=
  [ mkRec (mkLhs "stuff.stuff" (natsToStr ns))
      (fields (stuff.stuff (sliceOf ns) (alloc.vec.Vec.new Std.U8)) fun v => [u8sToStr v.val])
  , mkRec (mkLhs "stuff.encode_frame" (natsToStr ns))
      (fields (stuff.encode_frame (sliceOf ns) (alloc.vec.Vec.new Std.U8)) fun v =>
        [u8sToStr v.val]) ]

/-- Wires for the decode side. The first group is `encode_frame` output, some with residual bytes
after the flag; then the refusals. -/
def stuffWires : List (List Nat) :=
  [ [0x7E]
  , [1, 2, 3, 0x7E]
  , [1, 0x7D, 0x5E, 2, 0x7D, 0x5D, 3, 0x7E]
  , [1, 2, 0x7E, 9, 9]
  , [1, 2, 3]
  , []
  , [1, 0x7D]
  , [1, 0x7D, 0x41, 0x7E]
  , [0x7D, 0x00, 0x7E] ]

/-- The extracted `unstuff` of a wire: `ok <payload> <consumed>`, `err truncated` or
`err badescape`. -/
def unstuffFields (bs : List Nat) : List String :=
  fields (stuff.unstuff (sliceOf bs)) fun r =>
    match r with
    | .Ok (v, k) => [s!"ok {u8sToStr v.val} {k.val}"]
    | .Err .Truncated => ["err truncated"]
    | .Err .BadEscape => ["err badescape"]

/-! ## SeqNum: the extracted RFC 1982 serial-number arithmetic

The vectors are chosen to carry this unit's actual content rather than filler. They cross the wrap
boundary in **both** directions, and they include the **non-transitive triple itself**
(`0 -> 20000 -> 40000 -> 0`), which is the one behaviour of this unit a reader is most likely to
assume away; the vector file is where the compiled Rust is held to it. They also include the pair
exactly half the space apart (`0` and `32768`), RFC 1982 §3.2's undefined region, where the Rust
answers `false` in both directions -- a fact no proof in this repository states about the *Rust*, so
these two records are the only place it is checked. -/

def seqNumValues : List Nat := [0, 1, 4, 20000, 32768, 40000, 65530, 65535]

/-- `add` arguments: the increment `0` (which is *not* serially after its argument), the two
wraparound cases, half the space, and the increment that returns to the start. -/
def seqNumAddPairs : List (Nat × Nat) :=
  [ (0, 0), (0, 1), (20000, 20000), (65530, 10), (65535, 1), (0, 32768), (4, 65526) ]

/-- Comparison and distance arguments. The first four are the non-transitive cycle; the next two are
the undefined region; the rest cross the wrap boundary both ways, and include the reflexive pair. -/
def seqNumPairs : List (Nat × Nat) :=
  [ (0, 20000), (20000, 40000), (0, 40000), (40000, 0)
  , (0, 32768), (32768, 0)
  , (65530, 4), (4, 65530), (65535, 0), (0, 65535), (0, 0), (20000, 20000) ]

def seqNumRecs : List String :=
  seqNumValues.map (fun n =>
      mkRec (mkLhs "seq_num.new" (toString n))
        (fields (seq_num.SeqNum.new (u16 n)) fun s => [toString s.value.val]))
    ++ seqNumValues.map (fun n =>
      mkRec (mkLhs "seq_num.get" (toString n))
        (fields (seq_num.SeqNum.get ⟨u16 n⟩) fun v => [toString v.val]))
    ++ seqNumValues.map (fun n =>
      mkRec (mkLhs "seq_num.succ" (toString n))
        (fields (seq_num.SeqNum.succ ⟨u16 n⟩) fun s => [toString s.value.val]))
    ++ seqNumAddPairs.map (fun p =>
      mkRec (mkLhs "seq_num.add" (natsToStr [p.1, p.2]))
        (fields (seq_num.SeqNum.add ⟨u16 p.1⟩ (u16 p.2)) fun s => [toString s.value.val]))
    ++ seqNumPairs.map (fun p =>
      mkRec (mkLhs "seq_num.dist" (natsToStr [p.1, p.2]))
        (fields (seq_num.SeqNum.dist ⟨u16 p.1⟩ ⟨u16 p.2⟩) fun d => [toString d.val]))
    ++ seqNumPairs.map (fun p =>
      mkRec (mkLhs "seq_num.lt" (natsToStr [p.1, p.2]))
        (fields (seq_num.SeqNum.lt ⟨u16 p.1⟩ ⟨u16 p.2⟩) fun b => [boolToStr b]))

def crc8Vectors : List (List Nat) :=
  [ [], asciiBytes "a", asciiBytes "123456789", [0, 0, 0], [255, 255, 255, 255],
    asciiBytes "framed_channel" ]

def crc8Recs (ns : List Nat) : List String :=
  [ mkRec (mkLhs "crc8.bits" (natsToStr ns)) (fields (crc8.crc8 (sliceOf ns)) fun c => [toString c.val])
  , mkRec (mkLhs "crc8.table" (natsToStr ns))
      (fields (crc8.crc8_table (sliceOf ns)) fun c => [toString c.val]) ]

/-- Digest `k` is the extracted `crc8` of the byte sequence `0, 1, ..., k`. -/
def crc8IncrementalDigests : List String :=
  (List.range 256).map fun k =>
    match (crc8.crc8 (sliceOf ((List.range 256).take (k + 1)))).match with
    | .ok c => toString c.val
    | .div => "div"
    | .vis (.fail e) _ => s!"panic({repr e})"

/-! ## Channel: the extracted frame codec and `Channel<Q>` at both extracted queue records

The frame codec is compared byte for byte (`encode_frame`/`parse_frame` are `pub`). The channel
state machine is compared at the public surface: each operation's result, the delivered or taken
payload, and `queued()`; `wire` and `in_flight` are private on the Rust side, so they are not
recorded. Each trace is generated twice, as separately prefixed records: at the ring buffer record
through `Channel::new` (`channel.ChannelRingBufferVecU8.new`), and at the `VecQueue` record through
`Channel::with_queue`, so each Rust queue is compared with its own translation. -/

abbrev FrameVec := alloc.vec.Vec Std.U8

abbrev rbFrameRecord : queue.BoundedQueue (ring_buffer.RingBuffer FrameVec) FrameVec :=
  ring_buffer.RingBuffer.Insts.Framed_channelQueueBoundedQueue
    (alloc.vec.Vec.Insts.CoreDefaultDefault Std.U8) (core.clone.CloneallocvecVec core.clone.CloneU8)

abbrev vqFrameRecord : queue.BoundedQueue (queue.VecQueue FrameVec) FrameVec :=
  queue.VecQueue.Insts.Framed_channelQueueBoundedQueue (core.clone.CloneallocvecVec core.clone.CloneU8)

/-- The extracted `encode_frame` of a payload into an empty vector, as naturals. -/
def encodeFrameBytes (p : List Nat) : List Nat :=
  match (channel.encode_frame (sliceOf p) (u32 p.length) (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => v.val.map (·.val)
  | _ => []

def parseFrameRec (w : List Nat) : String :=
  mkRec (mkLhs "channel.parse_frame" (natsToStr w))
    (fields (channel.parse_frame (sliceOf w)) fun o =>
      match o with
      | some (v, used) => ["some", u8sToStr v.val, toString used.val]
      | none => ["none"])

/-- For one payload: its encoding, the parse of that encoding, the parse with a trailing byte (the
consumed count stops at the frame), one byte short (`None`) and a corrupted check byte (`None`). -/
def frameCodecRecs (p : List Nat) : List String :=
  let w := encodeFrameBytes p
  let short := w.take (w.length - 1)
  let badCrc := short ++ [((w.getLast?).getD 0 + 1) % 256]
  [ mkRec (mkLhs "channel.encode_frame" (natsToStr p))
      (fields (channel.encode_frame (sliceOf p) (u32 p.length) (alloc.vec.Vec.new Std.U8))
        fun v => [u8sToStr v.val])
  , parseFrameRec w
  , parseFrameRec (w ++ [99])
  , parseFrameRec short
  , parseFrameRec badCrc ]

/-- The 126-byte payload whose single varint length byte is the marker `0x7E`, with a `0x7E` inside
it as well: `(i % 253) as u8` for `i < 126`, then index 10 set to the marker. -/
def payload126 : List Nat :=
  (List.range 126).map fun i => if i == 10 then 126 else i % 253

inductive COp where
  | send (p : List Nat)
  | deliver
  | take

def chStep {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (c : channel.Channel S) (op : COp) : String × channel.Channel S :=
  match op with
  | .send p =>
    let lhs := mkLhs s!"{pfx}.send" (natsToStr p)
    let (fs, c') := stepWith c (do
        let (r, c') ← channel.Channel.send inst c (sliceOf p)
        let n ← channel.Channel.queued inst c'
        ok (r, n, c'))
      fun (r, n, c') => ([(match r with | .Ok _ => "ok" | .Err _ => "err"), toString n.val], c')
    (mkRec lhs fs, c')
  | .deliver =>
    let (fs, c') := stepWith c (do
        let (r, c') ← channel.Channel.deliver inst c
        let n ← channel.Channel.queued inst c'
        ok (r, n, c'))
      fun (r, n, c') =>
        ((match r with
          | .Ok v => ["ok", u8sToStr v.val, toString n.val]
          | .Err _ => ["err", "", toString n.val]), c')
    (mkRec s!"{pfx}.deliver" fs, c')
  | .take =>
    let (fs, c') := stepWith c (do
        let (o, c') ← channel.Channel.take inst c
        let n ← channel.Channel.queued inst c'
        ok (o, n, c'))
      fun (o, n, c') =>
        ((match o with
          | some v => ["some", u8sToStr v.val, toString n.val]
          | none => ["none", "", toString n.val]), c')
    (mkRec s!"{pfx}.take" fs, c')

def chTrace {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (channel.Channel S)) (cap : Nat) (ops : List COp) : List String :=
  let lhs := s!"{pfx}.new {cap}"
  match (do let c ← mk (usize cap); let n ← channel.Channel.queued inst c; ok (c, n)).match with
  | .ok (c, n) => mkRec lhs [toString n.val] :: runOps (chStep pfx inst) c ops
  | .div => [mkRec lhs ["div"]]
  | .vis (.fail e) _ => [mkRec lhs [s!"panic {repr e}"]]

/-- The capacity refusal and the empty-wire `deliver` failure, in one trace. -/
def chTraceCapacity : List COp :=
  [ .deliver
  , .send (asciiBytes "one"), .send (asciiBytes "two")
  , .send (asciiBytes "three")
  , .deliver, .deliver
  , .deliver
  , .take, .take, .take
  , .send (asciiBytes "three"), .deliver, .take ]

/-- One send/deliver/take round per payload, including the empty payload and marker bytes. -/
def chTraceRoundTrip : List COp :=
  [ .send [], .deliver, .take
  , .send (asciiBytes "a"), .deliver, .take
  , .send (asciiBytes "hello"), .deliver, .take
  , .send [126, 126, 126], .deliver, .take
  , .send (asciiBytes "framed_channel"), .deliver, .take ]

/-- The 126-byte payload whose length byte is the marker, interleaved with a second frame. -/
def chTrace126 : List COp :=
  [ .send payload126, .send (asciiBytes "x")
  , .deliver, .deliver
  , .take, .take, .take ]

def chTraces {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (channel.Channel S)) : List String :=
  chTrace pfx inst mk 2 chTraceCapacity ++ chTrace pfx inst mk 4 chTraceRoundTrip
    ++ chTrace pfx inst mk 2 chTrace126

/-! ## StuffedChannel: the transparent composite -/

/-- The extracted `encode_stuffed` of a payload into an empty vector, as naturals. -/
def encodeStuffedBytes (p : List Nat) : List Nat :=
  match (stuffed_channel.encode_stuffed (sliceOf p) (u32 p.length)
      (alloc.vec.Vec.new Std.U8)).match with
  | .ok v => v.val.map (·.val)
  | _ => []

def parseStuffedRec (w : List Nat) : String :=
  mkRec (mkLhs "stuffed_channel.parse_stuffed" (natsToStr w))
    (fields (stuffed_channel.parse_stuffed (sliceOf w)) fun o =>
      match o with
      | some (v, used) => ["some", u8sToStr v.val, toString used.val]
      | none => ["none"])

/-- Bump the byte before the terminating flag: the last byte of the stuffed body, which is the check
byte or the second half of its escape sequence. -/
def bumpSecondLast (w : List Nat) : List Nat :=
  match w.reverse with
  | flag :: b :: rest => rest.reverse ++ [(b + 1) % 256, flag]
  | _ => w

/-- For one payload: the stuffed frame, the parse of that frame, the parse with a trailing byte (the
consumed count stops at the terminating flag), one byte short, and the frame with the byte before the
flag bumped.

No record for the extracted `body`: it is a private Rust function, so `differential.rs` cannot call
it without widening the crate's API for a test's sake, and a vector nothing consumes is exactly the
silent gap `extracted_vectors_cover_every_translated_operation` exists to prevent. The channel's
private `drop_front` has no records either, for the same reason. `body` is covered by the bridge
instead, by `Bridge.stuffed_channel.body_refines`. -/
def stuffedCodecRecs (p : List Nat) : List String :=
  let w := encodeStuffedBytes p
  [ mkRec (mkLhs "stuffed_channel.encode_stuffed" (natsToStr p))
      (fields (stuffed_channel.encode_stuffed (sliceOf p) (u32 p.length)
        (alloc.vec.Vec.new Std.U8)) fun v => [u8sToStr v.val])
  , parseStuffedRec w
  , parseStuffedRec (w ++ [99])
  , parseStuffedRec (w.take (w.length - 1))
  , parseStuffedRec (bumpSecondLast w) ]

inductive SCOp where
  | send (p : List Nat)
  | deliver
  | take

def scStep {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (c : stuffed_channel.StuffedChannel S) (op : SCOp) :
    String × stuffed_channel.StuffedChannel S :=
  match op with
  | .send p =>
    let lhs := mkLhs s!"{pfx}.send" (natsToStr p)
    let (fs, c') := stepWith c (do
        let (r, c') ← stuffed_channel.StuffedChannel.send inst c (sliceOf p)
        let n ← stuffed_channel.StuffedChannel.queued inst c'
        ok (r, n, c'))
      fun (r, n, c') => ([(match r with | .Ok _ => "ok" | .Err _ => "err"), toString n.val], c')
    (mkRec lhs fs, c')
  | .deliver =>
    let (fs, c') := stepWith c (do
        let (r, c') ← stuffed_channel.StuffedChannel.deliver inst c
        let n ← stuffed_channel.StuffedChannel.queued inst c'
        ok (r, n, c'))
      fun (r, n, c') =>
        ((match r with
          | .Ok v => ["ok", u8sToStr v.val, toString n.val]
          | .Err _ => ["err", "", toString n.val]), c')
    (mkRec s!"{pfx}.deliver" fs, c')
  | .take =>
    let (fs, c') := stepWith c (do
        let (o, c') ← stuffed_channel.StuffedChannel.take inst c
        let n ← stuffed_channel.StuffedChannel.queued inst c'
        ok (o, n, c'))
      fun (o, n, c') =>
        ((match o with
          | some v => ["some", u8sToStr v.val, toString n.val]
          | none => ["none", "", toString n.val]), c')
    (mkRec s!"{pfx}.take" fs, c')

def scTrace {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (stuffed_channel.StuffedChannel S)) (cap : Nat) (ops : List SCOp) :
    List String :=
  let lhs := s!"{pfx}.new {cap}"
  match (do
      let c ← mk (usize cap)
      let n ← stuffed_channel.StuffedChannel.queued inst c
      ok (c, n)).match with
  | .ok (c, n) => mkRec lhs [toString n.val] :: runOps (scStep pfx inst) c ops
  | .div => [mkRec lhs ["div"]]
  | .vis (.fail e) _ => [mkRec lhs [s!"panic {repr e}"]]

/-- The capacity refusal and the empty-wire `deliver` failure, in one trace. -/
def scTraceCapacity : List SCOp :=
  [ .deliver
  , .send (asciiBytes "one"), .send (asciiBytes "two")
  , .send (asciiBytes "three")
  , .deliver, .deliver
  , .deliver
  , .take, .take, .take
  , .send (asciiBytes "three"), .deliver, .take ]

/-- One send/deliver/take round per payload: the empty payload, plain payloads, the flag byte, the
escape byte, and both reserved bytes together -- the cases stuffing exists for. -/
def scTraceRoundTrip : List SCOp :=
  [ .send [], .deliver, .take
  , .send (asciiBytes "a"), .deliver, .take
  , .send (asciiBytes "hello"), .deliver, .take
  , .send [126, 126, 126], .deliver, .take
  , .send [125, 125], .deliver, .take
  , .send [126, 125, 0, 126], .deliver, .take
  , .send (asciiBytes "framed_channel"), .deliver, .take ]

/-- The 126-byte payload whose varint length byte is the flag, with a flag byte inside it too: under
stuffing both are escaped, so the wire carries the flag only as the terminator. Interleaved with a
second frame, so the residual wire is exercised. -/
def scTrace126 : List SCOp :=
  [ .send payload126, .send (asciiBytes "x")
  , .deliver, .deliver
  , .take, .take, .take ]

def scTraces {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (stuffed_channel.StuffedChannel S)) : List String :=
  scTrace pfx inst mk 2 scTraceCapacity ++ scTrace pfx inst mk 4 scTraceRoundTrip
    ++ scTrace pfx inst mk 2 scTrace126

/-! ## Receiver: the extracted resynchronizing receive path -/

inductive RcvOp where
  | feed (bs : List Nat)
  | poll

/-- One receiver step. A `feed` record carries the drop count and the queued count after the feed;
a `poll` record carries the popped frame (or `none`) and both counters. `dropped` and `queued` are
recorded as fields of every step rather than as records of their own, exactly as the channel traces
record `queued`: they are observers, and a record nothing advances would test nothing. -/
def rcvStep {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (c : receiver.Receiver S) (op : RcvOp) : String × receiver.Receiver S :=
  match op with
  | .feed bs =>
    let (fs, c') := stepWith c (do
        let c' ← receiver.Receiver.feed inst c (sliceOf bs)
        let d ← receiver.Receiver.impl.dropped inst c'
        let n ← receiver.Receiver.queued inst c'
        ok (d, n, c'))
      fun (d, n, c') => ([toString d.val, toString n.val], c')
    (mkRec (mkLhs s!"{pfx}.feed" (natsToStr bs)) fs, c')
  | .poll =>
    let (fs, c') := stepWith c (do
        let (o, c') ← receiver.Receiver.poll inst c
        let d ← receiver.Receiver.impl.dropped inst c'
        let n ← receiver.Receiver.queued inst c'
        ok (o, d, n, c'))
      fun (o, d, n, c') =>
        ((match o with
          | some v => ["some", u8sToStr v.val, toString d.val, toString n.val]
          | none => ["none", "", toString d.val, toString n.val]), c')
    (mkRec s!"{pfx}.poll" fs, c')

def rcvTrace {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (receiver.Receiver S)) (cap : Nat) (ops : List RcvOp) : List String :=
  let lhs := s!"{pfx}.new {cap}"
  match (do
      let c ← mk (usize cap)
      let d ← receiver.Receiver.impl.dropped inst c
      let n ← receiver.Receiver.queued inst c
      ok (c, d, n)).match with
  | .ok (c, d, n) => mkRec lhs [toString d.val, toString n.val] :: runOps (rcvStep pfx inst) c ops
  | .div => [mkRec lhs ["div"]]
  | .vis (.fail e) _ => [mkRec lhs [s!"panic {repr e}"]]

/-- A clean stream: two frames in one feed, then the same two frames fed one byte at a time, which is
chunking invariance (`Receiver.feed_append`) made visible in the vectors. Order preservation is what
the two `poll`s after each show. -/
def rcvTraceClean : List RcvOp :=
  [ .feed (encodeStuffedBytes (asciiBytes "hi") ++ encodeStuffedBytes (asciiBytes "there"))
  , .poll, .poll, .poll ]
    ++ (encodeStuffedBytes (asciiBytes "hi") ++ encodeStuffedBytes (asciiBytes "there")).map
        (fun b => RcvOp.feed [b])
    ++ [ .poll, .poll, .poll ]

/-- The payloads stuffing exists for, each fed as a whole frame: the flag byte three times over, the
escape byte twice, both reserved bytes together, the empty payload (whose frame is a body and a
flag), and the 126-byte payload whose varint length byte is itself the flag. Every one is accepted,
and `dropped` stays 0 throughout -- that is the transparency claim exercised at the receive path. -/
def rcvTraceReserved : List RcvOp :=
  [ .feed (encodeStuffedBytes [126, 126, 126]), .poll
  , .feed (encodeStuffedBytes [125, 125]), .poll
  , .feed (encodeStuffedBytes [126, 125, 0, 126]), .poll
  , .feed (encodeStuffedBytes []), .poll
  , .feed (encodeStuffedBytes payload126), .poll ]

/-- Corruption and truncation, the cases this unit exists for.

* a frame whose check byte is bumped: one drop, nothing accepted, and the receiver keeps going;
* a truncated (unterminated) frame: nothing is dropped and nothing is accepted, because the run stays
  buffered -- then the NEXT frame's leading flag closes that fused run as one drop and the frame that
  follows it is lost. That is why Decision 3's resync-progress law needs its flag-terminated
  qualifier, and it is recorded here rather than argued;
* adjacent flags: RFC 1662 4.1's idle case. Two, then three in a row: no drop, no acceptance;
* a garbage prefix that IS flag-terminated: the garbage is one drop and the frame after it is
  accepted (resync progress);
* a garbage prefix that is NOT flag-terminated: it fuses with the following frame's body, so that
  frame is lost -- one drop, nothing accepted. The pair is the law's qualifier, shown. -/
def rcvTraceResync : List RcvOp :=
  [ .feed (bumpSecondLast (encodeStuffedBytes (asciiBytes "hello"))), .poll
  , .feed ((encodeStuffedBytes (asciiBytes "hello")).take
      ((encodeStuffedBytes (asciiBytes "hello")).length - 1))
  , .poll
  , .feed (encodeStuffedBytes (asciiBytes "lost")), .poll
  , .feed [126, 126], .poll
  , .feed [126, 126, 126], .poll
  , .feed ([3, 4, 5, 126] ++ encodeStuffedBytes (asciiBytes "after")), .poll, .poll
  , .feed ([3, 4, 5] ++ encodeStuffedBytes (asciiBytes "fused")), .poll ]

/-- The full-queue refusal, at capacity 1: two frames in one feed, the second refused by the queue
and counted as a drop exactly as a malformed run is (`Receiver.run_exactly_one` is what that keeps
unconditional). Then a poll drains the queue and a third frame is accepted, so the refusal is shown
not to wedge the receiver. -/
def rcvTraceFull : List RcvOp :=
  [ .feed (encodeStuffedBytes (asciiBytes "first") ++ encodeStuffedBytes (asciiBytes "second"))
  , .poll, .poll
  , .feed (encodeStuffedBytes (asciiBytes "third"))
  , .poll, .poll ]

def rcvTraces {S : Type} (pfx : String) (inst : queue.BoundedQueue S FrameVec)
    (mk : Std.Usize → Result (receiver.Receiver S)) : List String :=
  rcvTrace pfx inst mk 4 rcvTraceClean ++ rcvTrace pfx inst mk 4 rcvTraceReserved
    ++ rcvTrace pfx inst mk 4 rcvTraceResync ++ rcvTrace pfx inst mk 1 rcvTraceFull

/-! ## Header and sections -/

/-- The pinned Aeneas revision, read from `lakefile.toml` in the working directory (the generator
runs from `aeneas/`). -/
def aeneasRev : IO String := do
  let text ← (IO.FS.readFile "lakefile.toml").toBaseIO
  match text with
  | .error _ => pure "unknown"
  | .ok t =>
    let revs := (t.splitOn "\n").filterMap fun l =>
      let l := l.trimAscii.toString
      if l.startsWith "rev = \"" then some ((l.drop 7).takeWhile (· != '"')).toString else none
    pure (revs.headD "unknown")

def header (rev : String) : List String :=
  [ "# framed_channel differential vectors, computed by evaluating the Aeneas extraction"
  , "# GENERATED by aeneas/GenVectors.lean; do not edit (the same discipline as axioms.txt and digests.txt)"
  , "# regenerate: bash scripts/refresh-vectors.sh    (drift gate: bash check.sh)"
  , s!"# lean: {Lean.versionString}"
  , s!"# aeneas: {rev}"
  , s!"# platform: usize is {System.Platform.numBits} bits"
  , "#"
  , "# Grammar: one record per line, `<op> <inputs...> => <field>; <field>; ...`."
  , "#   `#`-prefixed lines are comments, blank lines are skipped, scalars are decimal,"
  , "#   list fields are whitespace-separated (an empty field is the empty list)."
  , "# Result fields are the Rust results as the extraction returns them: ok/err, ok <scalars>,"
  , "#   err <variant>, some/none. `panic <error>` or `div` marks an extracted evaluation that"
  , "#   did not return; no record is expected to carry one."
  , "# Stateful traces replay in file order: a `.new` record resets the state."
  , "#"
  ]

def queueSection : List String :=
  [ "# ---- Queues: the extracted BoundedQueue records at u32 ------------------------------"
  , "# Every state field is `<contents>; <is_empty>; <is_full>; <len>; <capacity>`, read through"
  , "#   the extracted record. push records lead with ok/err, pop records with some <x>/none."
  , "# cap 0: the extracted RingBuffer::with_capacity rounds up to one; VecQueue keeps zero."
  ] ++ qTrace "ringbuffer" rbRecord 1 traceCap1 ++ qTrace "ringbuffer" rbRecord 3 traceCap3
    ++ qTrace "ringbuffer" rbRecord 0 traceCap0
    ++ qTrace "vecqueue" vqRecord 1 traceCap1 ++ qTrace "vecqueue" vqRecord 3 traceCap3
    ++ qTrace "vecqueue" vqRecord 0 traceCap0

def varintSection : List String :=
  [ "# ---- Varint: the extracted encode_u32 / decode_u32 ---------------------------------"
  , "# decode records carry the Rust result: `ok <value> <consumed>`, `err truncated` or"
  , "#   `err overlong`."
  ] ++ varintValues.map (fun n =>
        mkRec s!"varint.encode {n}"
          (fields (varint.encode_u32 (u32 n) (alloc.vec.Vec.new Std.U8)) fun v => [u8sToStr v.val]))
    ++ varintDecodeInputs.map (fun bs => mkRec (mkLhs "varint.decode" (natsToStr bs)) (decodeFields bs))
    ++ [ "# Out of the codec's domain: a fifth group too wide for a u32. The Rust and the extraction"
       , "#   agree on Err(Overlong); the hand-written Nat model would decode a value at or above"
       , "#   2 ^ 32 here, the divergence the bridge states as decode_err_iff."
       ] ++ varintOutOfDomainInputs.map (fun bs =>
        mkRec (mkLhs "varint.decode.out_of_domain" (natsToStr bs)) (decodeFields bs))

def zigzagSection : List String :=
  [ "# ---- Zigzag: the extracted zigzag / unzigzag / encode_i32 / decode_i32 --------------"
  , "# The signed varint, delegating to the varint codec. zigzag and unzigzag records carry the"
  , "#   mapped scalar; encode records carry the bytes; decode records carry the Rust result,"
  , "#   `ok <value> <consumed>`, `err truncated` or `err overlong` -- decode_i32 forwards the"
  , "#   VarintError unchanged, so no new error variant appears."
  , "# Signed arguments and signed results are decimal and may carry a leading minus."
  ] ++ zigzagValues.map (fun n =>
        mkRec (mkLhs "zigzag.zigzag" (toString n))
          (fields (zigzag.zigzag (i32 n)) fun v => [toString v.val]))
    ++ (zigzagValues.map zigzagMapped).eraseDups.map (fun m =>
        mkRec (mkLhs "zigzag.unzigzag" (toString m))
          (fields (zigzag.unzigzag (u32 m)) fun v => [toString v.val]))
    ++ zigzagValues.map (fun n =>
        mkRec (mkLhs "zigzag.encode" (toString n))
          (fields (zigzag.encode_i32 (i32 n) (alloc.vec.Vec.new Std.U8)) fun v =>
            [u8sToStr v.val]))
    ++ zigzagDecodeInputs.map (fun bs =>
        mkRec (mkLhs "zigzag.decode" (natsToStr bs)) (zigzagDecodeFields bs))

def stuffSection : List String :=
  [ "# ---- Stuff: the extracted stuff / encode_frame / unstuff ---------------------------"
  , "# stuff records carry the stuffed payload; encode_frame records add the terminating flag."
  , "# unstuff records carry the Rust result: `ok <payload> <consumed>`, `err truncated` or"
  , "#   `err badescape`. The consumed count includes the terminating flag."
  ] ++ stuffPayloads.flatMap stuffRecs
    ++ stuffWires.map (fun bs => mkRec (mkLhs "stuff.unstuff" (natsToStr bs)) (unstuffFields bs))

def crc8Section : List String :=
  [ "# ---- Crc8: the extracted crc8 (bits) and crc8_table (table) -----------------------"
  ] ++ crc8Vectors.flatMap crc8Recs
    ++ [ "# Compact record: digest k is the extracted crc8 of the byte sequence 0, 1, ..., k, for k"
       , "#   from 0 to 255."
       , mkRec "crc8.incremental_prefixes" [String.intercalate " " crc8IncrementalDigests] ]

def seqNumSection : List String :=
  [ "# ---- SeqNum: the extracted new / get / succ / add / dist / lt ----------------------"
  , "# RFC 1982 serial-number arithmetic over a 16-bit space. new and get records carry the stored"
  , "#   word; succ, add and dist records carry the resulting word; lt records carry 1 or 0."
  , "# All arithmetic wraps: succ 65535 => 0, add 65530 10 => 4, dist 4 65530 => 65530."
  , "# The lt records include the NON-TRANSITIVE triple -- lt 0 20000 => 1, lt 20000 40000 => 1,"
  , "#   lt 0 40000 => 0 and lt 40000 0 => 1, a genuine three-cycle (refuted in the kernel in"
  , "#   lean/FramedChannel/Evidence/Countermodels.lean) -- and the undefined region, where 0 and"
  , "#   32768 are exactly half the space apart and lt is 0 in both directions."
  ] ++ seqNumRecs

def channelSection : List String :=
  [ "# ---- Channel: the extracted frame codec ------------------------------------------"
  , "# Per payload: the encoding, its parse, its parse with a trailing byte, one byte short and a"
  , "#   corrupted check byte. parse_frame records carry `some; <payload>; <consumed>` or `none`."
  ] ++ [[], asciiBytes "hi", asciiBytes "framed_channel", [126, 126, 126], payload126].flatMap
        frameCodecRecs
    ++ [ "# ---- Channel<Q>: the extracted state machine at both queue records ---------------"
       , "# send: `ok|err; <queued>`; deliver: `ok; <payload>; <queued>` or `err; ; <queued>`;"
       , "#   take: `some; <payload>; <queued>` or `none; ; <queued>`. wire and in_flight are private"
       , "#   on the Rust side and are not recorded."
       , "# channel.ringbuffer.*: Channel::new over the extracted RingBuffer<Vec<u8>> record."
       ] ++ chTraces "channel.ringbuffer" rbFrameRecord channel.ChannelRingBufferVecU8.new
    ++ [ "# channel.vecqueue.*: Channel::with_queue over the extracted VecQueue<Vec<u8>> record." ]
    ++ chTraces "channel.vecqueue" vqFrameRecord (channel.Channel.with_queue vqFrameRecord)

def stuffedChannelSection : List String :=
  [ "# ---- StuffedChannel: the extracted transparent frame codec -----------------------"
  , "# The transparent counterpart of the channel codec. Per payload: the stuffed frame its body"
  , "#   (varint length, payload, check byte) becomes, the parse of that frame, its parse with a"
  , "#   trailing byte, one byte short, and the frame with the byte before the terminating flag"
  , "#   bumped. parse_stuffed records carry `some; <payload>; <consumed>` or `none`, and the"
  , "#   consumed count includes the terminating flag."
  , "# The private `body` and `drop_front` carry no records: differential.rs cannot call a private"
  , "#   function, and a vector nothing consumes is the gap the coverage census exists to prevent."
  , "# Note what the encode_stuffed records show and the channel's encode_frame records cannot: the"
  , "#   flag byte 126 appears in a stuffed frame ONLY as its last byte."
  ] ++ [[], asciiBytes "hi", asciiBytes "framed_channel", [126, 126, 126], [125, 125],
        payload126].flatMap stuffedCodecRecs
    ++ [ "# ---- StuffedChannel<Q>: the extracted state machine at both queue records --------"
       , "# Same field shapes as the channel traces: send `ok|err; <queued>`; deliver"
       , "#   `ok; <payload>; <queued>` or `err; ; <queued>`; take `some; <payload>; <queued>` or"
       , "#   `none; ; <queued>`. wire and in_flight are private and are not recorded."
       , "# stuffed_channel.ringbuffer.*: StuffedChannel::new over the extracted"
       , "#   RingBuffer<Vec<u8>> record."
       ] ++ scTraces "stuffed_channel.ringbuffer" rbFrameRecord
              stuffed_channel.StuffedChannelRingBufferVecU8.new
    ++ [ "# stuffed_channel.vecqueue.*: StuffedChannel::with_queue over the extracted"
       , "#   VecQueue<Vec<u8>> record." ]
    ++ scTraces "stuffed_channel.vecqueue" vqFrameRecord
         (stuffed_channel.StuffedChannel.with_queue vqFrameRecord)

def receiverSection : List String :=
  [ "# ---- Receiver: the extracted resynchronizing receive path ------------------------"
  , "# feed: `<dropped>; <queued>` after the feed; poll: `some; <payload>; <dropped>; <queued>` or"
  , "#   `none; ; <dropped>; <queued>`. buf is private on the Rust side and is not recorded."
  , "# The private `finish_run` carries no records: differential.rs cannot call a private function,"
  , "#   and a vector nothing consumes is the gap the coverage census exists to prevent. It is"
  , "#   covered instead by its bridge row, Bridge.receiver.finish_run_refines -- the same reasoning"
  , "#   the transparent channel's `body` and the channel's `drop_front` already carry."
  , "# The wires here are not all well-formed, which is the point: corrupted check bytes, truncated"
  , "#   frames, adjacent flags, and a garbage prefix both with and without its terminating flag."
  , "# receiver.ringbuffer.*: Receiver::new over the extracted RingBuffer<Vec<u8>> record."
  ] ++ rcvTraces "receiver.ringbuffer" rbFrameRecord receiver.ReceiverRingBufferVecU8.new
    ++ [ "# receiver.vecqueue.*: Receiver::with_queue over the extracted VecQueue<Vec<u8>> record." ]
    ++ rcvTraces "receiver.vecqueue" vqFrameRecord (receiver.Receiver.with_queue vqFrameRecord)

def output (rev : String) : List String :=
  header rev ++ queueSection ++ varintSection ++ zigzagSection ++ stuffSection
    ++ crc8Section ++ seqNumSection ++ channelSection ++ stuffedChannelSection
    ++ receiverSection

end GenVectors

def main : IO Unit := do
  let rev ← GenVectors.aeneasRev
  for line in GenVectors.output rev do
    IO.println line
