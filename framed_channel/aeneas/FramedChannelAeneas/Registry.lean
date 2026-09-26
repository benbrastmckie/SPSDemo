-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Registry
import FramedChannelAeneas.Bridge.Queue.Defs
import FramedChannelAeneas.Bridge.Queue.Traits
import FramedChannelAeneas.Bridge.Queue.Transport
import FramedChannelAeneas.Bridge.RingBuffer.Defs
import FramedChannelAeneas.Bridge.RingBuffer.Refinement
import FramedChannelAeneas.Bridge.Std
import FramedChannelAeneas.Bridge.Queue.Instance
import FramedChannelAeneas.Bridge.RingBuffer.Instance
import FramedChannelAeneas.Bridge.VecQueue.Defs
import FramedChannelAeneas.Bridge.VecQueue.Refinement
import FramedChannelAeneas.Bridge.VecQueue.Instance
import FramedChannelAeneas.Bridge.Varint.Defs
import FramedChannelAeneas.Bridge.Varint.Encode
import FramedChannelAeneas.Bridge.Varint.Decode
import FramedChannelAeneas.Bridge.Varint.Instance
import FramedChannelAeneas.Bridge.Zigzag.Defs
import FramedChannelAeneas.Bridge.Zigzag.Mapping
import FramedChannelAeneas.Bridge.Zigzag.Instance
import FramedChannelAeneas.Bridge.Stuff.Defs
import FramedChannelAeneas.Bridge.Stuff.Stuff
import FramedChannelAeneas.Bridge.Stuff.Unstuff
import FramedChannelAeneas.Bridge.Stuff.Instance
import FramedChannelAeneas.Bridge.Crc8.Defs
import FramedChannelAeneas.Bridge.Crc8.Bitwise
import FramedChannelAeneas.Bridge.Crc8.Table
import FramedChannelAeneas.Bridge.Crc8.Instance
import FramedChannelAeneas.Bridge.SeqNum.Defs
import FramedChannelAeneas.Bridge.SeqNum.Instance
import FramedChannelAeneas.Bridge.Channel.Defs
import FramedChannelAeneas.Bridge.Channel.Abstraction
import FramedChannelAeneas.Bridge.Channel.Frame
import FramedChannelAeneas.Bridge.Channel.Refinement
import FramedChannelAeneas.Bridge.Channel.Composite
import FramedChannelAeneas.Bridge.Channel.Instance
import FramedChannelAeneas.Bridge.StuffedChannel.Defs
import FramedChannelAeneas.Bridge.StuffedChannel.Abstraction
import FramedChannelAeneas.Bridge.StuffedChannel.Frame
import FramedChannelAeneas.Bridge.StuffedChannel.Refinement
import FramedChannelAeneas.Bridge.StuffedChannel.Composite
import FramedChannelAeneas.Bridge.StuffedChannel.Instance
import FramedChannelAeneas.Bridge.Receiver.Defs
import FramedChannelAeneas.Bridge.Receiver.Loop
import FramedChannelAeneas.Bridge.Receiver.Refinement
import FramedChannelAeneas.Bridge.Receiver.Instance

/-!
# Registry: the bridge package's rows, and the combined bank

The bridge-layer counterpart of `lean/FramedChannel/Registry.lean`. Every certified theorem of
this package is registered here through the same `register%` macro, so each bridge row is bound
to its theorem's elaborated statement hash exactly as a core row is: silently weakening
`push_refines` or a transport theorem fails the build with a drift error, rather than keeping a
trust flag the certificate manifest still claims.

The macro is used by import, never re-declared. It is defined in core `Certify.lean`, and its
source does not parse when re-declared in a module that imports Aeneas and Mathlib.

## Namespaces

Core namespaces are UpperCamelCase Lean names (`FramedChannel.RingBuffer`); bridge namespaces
follow the snake_case names the extraction gives the Rust (`framed_channel.ring_buffer`), so a
bridge theorem sits under the name of what it is about: `FramedChannel.Bridge.ring_buffer`,
`.varint`, `.crc8`, `.channel`. The exception is `FramedChannel.Bridge.vec_queue`, named after the
`VecQueue` type rather than its module `queue`: that module also declares the `BoundedQueue`
trait, whose component-independent bridge (`QueueSim` and the transport theorems) lives in
`FramedChannel.Bridge` itself.

## What is registered

* The nine certified refinement theorems of the extracted ring buffer
  (`Bridge/RingBuffer/Refinement.lean`): error agreement and observer agreement as `E1`, the two
  refinements and the two transported laws as `E2`.
* `ring_buffer.sim`, the per-component simulation, as `E2`.
* The six generic transport theorems (`Bridge/Queue/Transport.lean`), as `E2`: each is proved
  once and holds at every simulating extracted record.
* The interface instances on extracted carriers, as `E2`: the generic
  `QueueSim.boundedQueueLaws` (`Bridge/Queue/Instance.lean`) and its two instantiations,
  `ring_buffer.instBoundedQueueLaws_extracted` and `vec_queue.instBoundedQueueLaws_extracted` --
  two extracted instances of one interface.
* The extracted list-backed queue (`Bridge/VecQueue/Refinement.lean`): error and observer
  agreement as `E1`; `push_refines`, `pop_refines` and `vec_queue.sim` as `E2`.
* The extracted varint codec (`Bridge/Varint/`): `encode_refines`, `decode_ok_refines`,
  `decode_complete`, `roundtrip_extracted` and `instCodecLaws_extracted` as `E2`, and the error
  agreement `decode_err_iff` as `E1`.
* The extracted zigzag signed varint (`Bridge/Zigzag/`), the codec interface's second value type
  at the bridge: `encode_refines`, `decode_ok_refines`, `decode_complete`, `roundtrip_extracted`
  and `instCodecLaws_extracted` as `E2`; the two scalar specifications `zigzag_spec` and
  `unzigzag_spec`, and the error agreement `decode_err_iff`, as `E1`. Every `E2` row here is the
  varint codec's own theorem plus one scalar step -- `Bridge/Zigzag/Instance.lean` unfolds no
  LEB128 loop and holds no loop lemma. Left unregistered: `decode_eq`, `bmod_small`, `i32_not_val`
  and `zz_bv`, which are steps of those proofs rather than obligations of the unit; `zz_bv` is the
  one genuinely new bit-vector fact, and it is kernel-only (no `bv_decide`, hence no `flagged`
  row).
* The extracted HDLC byte-stuffing codec (`Bridge/Stuff/`): `stuff_refines`,
  `encode_frame_refines`, `decode_ok_refines`, `decode_complete`, `roundtrip_extracted` and
  `instCodecLaws_extracted` as `E2`, and the error agreement `decode_err_iff` as `E1`. Its
  `decode_err_iff` is an exact `iff`, where the varint codec's is an implication in one direction
  only over a stricter Rust rejection.
* The extracted CRC-8 (`Bridge/Crc8/`): `crc8_refines`, `crc8_table_refines`, the extracted-level
  equivalence `crc8_table_eq_extracted` and the two `ChecksumLaws` instances as `E2`, and
  `table_agrees` as `E1`.
* The extracted RFC 1982 sequence number (`Bridge/SeqNum/`): `succ_refines`, `add_refines`,
  `dist_refines`, `lt_refines` and `instSerialLaws_extracted` as `E2`; the extracted `HALF` const
  (`HALF_val`) and the two accessor agreements `new_refines` and `get_refines` as `E1`. There are
  exactly as many rows as there are non-derived in-subset candidates, `HALF` included, because the
  extraction emits a `pub const` as its own selection candidate. Every triple is
  **hypothesis-free**: `core.num.U16.wrapping_add` / `wrapping_sub` are pure functions in Aeneas's
  library, so wraparound is the definition rather than a failure to exclude. Left unregistered:
  `half_eq`, the three abstraction-bijection lemmas (`toModel_ofModel`, `ofModel_toModel`,
  `toModel_inj`, plus `toModel_ne`), the four `ext*` lowering lemmas and `ext_iter` -- steps of the
  registered rows, not obligations. **No transitivity row**, at either level: RFC 1982's serial
  comparison has genuine three-cycles, refuted in the kernel in
  `lean/FramedChannel/Evidence/Countermodels.lean`.
* `cloneVecU8_isId` (`Bridge/Queue/Traits.lean`), as `E1`: the `CloneIsId` the ring buffer instance
  needs at the frame type, proved for the actual derived `Clone` of `Vec<u8>`.
* The extracted channel (`Bridge/Channel/`): the frame codec refinements `encode_frame_refines`
  and `parse_frame_refines`, the extracted round trip and the length-126 marker frame, as `E2`;
  the per-operation refinements over any lawful queue record, `send_refines` and
  `deliver_refines` as `E2`, `take_refines` and `queued_agrees` as `E1`; the composition theorems
  at the extracted code (`send_deliver_extracted`, `deliver_spec_extracted`, `send_inv_extracted`
  as `E2`; `send_bounded_extracted`, `send_refuses_too_long_extracted`,
  `send_discharges_not_full_extracted` as `E1`); and the substitution rows at both extracted
  queues: the idle constructors `new_idle_RB` and `with_queue_idle_VQ` as `E1`, and the `_RB`/`_VQ`
  instantiations and the constructor headlines `send_deliver_from_new_RB`/`_VQ` as `E2`.
* The extracted transparent channel (`Bridge/StuffedChannel/`), the same shape at the second
  composite: the frame codec refinements `body_refines`, `encode_stuffed_refines` and
  `parse_stuffed_refines`, the extracted round trip, and `wire_flag_free_extracted` -- the
  transparency claim on the extracted side, which is this unit's reason to exist -- all as `E2`;
  the per-operation refinements over any lawful queue record, `send_refines` and `deliver_refines`
  as `E2`, `take_refines` and `queued_agrees` as `E1`; the composition theorems at the extracted
  code, with the same `E2`/`E1` split as the channel's; and the substitution rows at both extracted
  queues. `parse_stuffed_refines`' postcondition carries exactly one divergence disjunct, the
  varint layer's, where the channel's carried the same one: the stuffing layer contributes none,
  `stuff.decode_err_iff` being an exact iff. There is no length-126 row here and none is owed: the
  marker byte in a length prefix is stuffed away, and the round trip already holds at every payload
  including marker-bearing ones with no hypothesis.
* The extracted resynchronizing receive path (`Bridge/Receiver/`), the receive-side counterpart of
  the transparent channel: `finish_run_refines`, the run judgement the scan loop calls at every flag
  and the row that covers the *private* `finish_run` (no differential vector can call it); the
  per-operation refinements over any lawful queue record, `feed_refines` and `poll_refines` as `E2`,
  `dropped_agrees` and `queued_agrees` as `E1`; and the substitution rows at both extracted queues,
  the idle constructors `new_idle_RB` and `with_queue_idle_VQ` as `E1` and the `_RB`/`_VQ`
  instantiations of `feed`/`poll` as `E2`. Eleven rows against the transparent channel's
  twenty-four, and the difference is reuse rather than omission: the run parse is
  `stuffed_channel.parse_stuffed`, already registered, so this unit's own content is the scan.
  `feed_refines` carries three hypotheses -- the buffered run's length bound, the drop counter's
  (`saturating_add` caps where the model's `Nat` does not, so panic-freedom is not value agreement)
  and `NoWideRun` -- and `certificate/receiver.yaml` records all three.

Deliberately not registered: the `Aeneas` step lemmas `set_spec`/`get_spec` and `set_opt_some`,
the `BQ` lifting lemmas `pushBQ_of_push`/`popBQ_of_pop`, `len_agrees` (an input to
`ring_buffer.sim`, whose row covers it), and `Bridge/Queue/Traits.lean`'s `cln_isId`. Likewise the
library-gap step specifications of `Bridge/Std.lean`, the lowering read-through lemmas of
`Bridge/Queue/Instance.lean`, the carrier and functionality lemmas of each queue instance, the loop
lemmas and their invariants (`encode_loop_refines`, `decode_loop_refines`, `decode_refines`,
`inner_loop_refines`, `outer_loop_refines`, `table_loop_refines`), the `Nat` and scalar arithmetic
lemmas, and the digest/step identification lemmas of `Bridge/Crc8/Instance.lean`. In the
byte-stuffing bridge the supporting set is the two loop lemmas and their invariants
(`stuff_loop_refines`/`StuffInv`, `unstuff_loop_refines`/`UnstuffInv`/`UnstuffPost`),
`unstuff_refines` (covered by the three decode rows derived from it), the extracted-constant value
lemmas (`MARKER_val`, `ESC_val`, `marker_eq`, `esc_eq`, `marker_xor`, `esc_xor`), the abstraction
lemmas (`bytesOf_length`, `bytesOf_append`, `bytesOf_drop_cons`, `bytesOf_push_reverse`,
`bytesOf_sliceOfBytes`, `sliceOfBytes_length`), the slice-index helpers (`getElem?_some_lt`,
`eq_getElem_of_getElem?`), the model-side `unstuff` equation lemmas proved bridge-locally
(`unstuff_nil`, `unstuff_marker`, `unstuff_plain`, `unstuff_esc_last`, `unstuff_esc_marker`,
`unstuff_esc_esc`, `unstuff_esc_bad`), and `stuff_out_length`, `encode_bytes_lt` and
`extEncode_eq`. The CRC-8
`inner_refines` is kept supporting too: it is the `@[step]` specification `crc8_refines` is
walked with, and `crc8_refines`'s row covers it. `decode_refines` is covered by the three decode
rows derived from it. In the channel bridge, the abstraction (`vecOfFrame`, `ofFrame_val`,
`ofFrame_bitsOf`, `frameOK_fits`, `u32_max_le_usize_max`, `bitsOf_eq_bytesOf_map`), the parser
helpers of `Bridge/Channel/Frame.lean`, `drop_front_refines`, `not_declaresWide_encodeFrame`,
`hovf_of_inv`, the generic `with_queue_idle` and each queue's `with_capacity_rel` are supporting.
The transparent channel bridge keeps the same set supporting, name for name where the name exists:
its byte and slice plumbing (`val_eq_bv_toNat`, `slice_drop_val`, `bytesOf_drop`, `bytesOf_take`,
`bytesOf_len`, `bytesOf_eq_map_toNat`, `map_ofNat_bytesOf`, `bytesOf_eq_varint_bytesOf`,
`bytesOf_cons`, `bits_of_bytes`), the three component-tag spellings (`encode_hdlc`, `decode_hdlc`,
`digest_bitwise`), the body shape lemmas (`body_eq`, `encodeStuffed_eq`, `body_length`,
`body_length_le`, `decode_body`), the model-parser equations (`parseStuffed_decode_fail`,
`parseStuffed_varint_fail`, `parseStuffed_step`), `drop_front_refines`,
`not_declaresWide_encodeStuffed`, `hovf_of_inv` and the generic `with_queue_idle`.
All of these are proved and audited, and listed under `supporting:` in the
manifests; they are not obligations.

## The combined bank

`allItems` is the core registry followed by this one, and `allBank` is its bank. Its totals are
closed by kernel `decide` below, as the core bank's are.
-/

namespace FramedChannel.Bridge

open FramedChannel.Certify

def items : List CertifiedItem :=
  [ -- The extracted ring buffer: error and observer agreement (E1)
    register% ring_buffer.push_full        ItemType.E1 1 true 1113836483
      "on a full buffer the extracted push returns Err(Full) and keeps the buffer",
    register% ring_buffer.pop_empty        ItemType.E1 1 true 2958974256
      "on an empty buffer the extracted pop returns None and keeps the buffer",
    register% ring_buffer.capacity_agrees  ItemType.E1 1 true 2543618916
      "the extracted capacity is the model's buf.length",
    register% ring_buffer.len_agrees       ItemType.E1 1 true 2859788117
      "the extracted len is the model's item count",
    register% ring_buffer.is_full_agrees   ItemType.E1 1 true 3505917002
      "the extracted is_full is the model's full",
    register% ring_buffer.is_empty_agrees  ItemType.E1 1 true 905965270
      "the extracted is_empty is the model's empty",
    -- The extracted ring buffer: refinement and transported laws (E2)
    register% ring_buffer.push_refines     ItemType.E2 2 true 959708054
      "the extracted push refines the model's push under Inv",
    register% ring_buffer.pop_refines      ItemType.E2 2 true 1387403342
      "the extracted pop refines the model's pop under Inv, assuming CloneIsId",
    register% ring_buffer.push_law_extracted ItemType.E2 2 true 3102057353
      "the extracted push preserves Inv and appends to contents",
    register% ring_buffer.pop_law_extracted ItemType.E2 2 true 1891187735
      "the extracted pop preserves Inv and removes the front of contents",
    register% ring_buffer.sim              ItemType.E2 2 true 837437747
      "the extracted BoundedQueue record simulates BQ through toModel",
    -- The generic queue transport (E2)
    register% push_law_of_sim              ItemType.E2 2 true 2977289578
      "push_law at any simulating extracted record",
    register% pop_law_of_sim               ItemType.E2 2 true 300474891
      "pop_law at any simulating extracted record",
    register% full_law_of_sim              ItemType.E2 2 true 1417183677
      "full_law at any simulating extracted record",
    register% empty_law_of_sim             ItemType.E2 2 true 1617048247
      "empty_law at any simulating extracted record",
    register% not_full_of_lt_of_sim        ItemType.E2 2 true 1867951786
      "not_full_of_lt at any simulating extracted record",
    register% push_capacity_of_sim         ItemType.E2 2 true 2381322881
      "push_capacity at any simulating extracted record",
    -- The generic extracted-carrier instance (E2)
    register% QueueSim.boundedQueueLaws    ItemType.E2 2 true 800904043
      "any simulating extracted record satisfies BoundedQueueLaws on its extracted carrier",
    -- The extracted ring buffer as an interface instance (E2)
    register% ring_buffer.instBoundedQueueLaws_extracted ItemType.E2 2 true 122899235
      "BoundedQueueLaws on the extracted ring buffer, assuming CloneIsId",
    -- The extracted list-backed queue: error and observer agreement (E1)
    register% vec_queue.push_full          ItemType.E1 1 true 339287541
      "at the bound the extracted VecQueue push returns Err(Full) and keeps the queue",
    register% vec_queue.pop_empty          ItemType.E1 1 true 532483917
      "on an empty queue the extracted VecQueue pop returns None and keeps the queue",
    register% vec_queue.capacity_agrees    ItemType.E1 1 true 2426430212
      "the extracted VecQueue capacity is the model's cap",
    register% vec_queue.len_agrees         ItemType.E1 1 true 4132236738
      "the extracted VecQueue len is the model's item count",
    register% vec_queue.is_full_agrees     ItemType.E1 1 true 488353430
      "the extracted VecQueue is_full is the model's bound check",
    register% vec_queue.is_empty_agrees    ItemType.E1 1 true 190800780
      "the extracted VecQueue is_empty is the model's emptiness check",
    -- The extracted list-backed queue: refinement, simulation and instance (E2)
    register% vec_queue.push_refines       ItemType.E2 2 true 2005838963
      "the extracted VecQueue push refines VQ.push, with no overflow hypothesis",
    register% vec_queue.pop_refines        ItemType.E2 2 true 2520379424
      "the extracted VecQueue pop refines VQ.pop",
    register% vec_queue.sim                ItemType.E2 2 true 1352021371
      "the extracted VecQueue record simulates VQ through toModel, at every Clone record",
    register% vec_queue.push_law_extracted ItemType.E2 2 true 3438597448
      "the extracted VecQueue push appends to the model's items, from the generic transport",
    register% vec_queue.pop_law_extracted  ItemType.E2 2 true 1955258610
      "the extracted VecQueue pop removes the front of the model's items, from the generic transport",
    register% vec_queue.instBoundedQueueLaws_extracted ItemType.E2 2 true 53920409
      "BoundedQueueLaws on the extracted VecQueue, with no trait assumption",
    -- The extracted varint codec (E2, and error agreement as E1)
    register% varint.encode_refines        ItemType.E2 2 true 4113882781
      "the extracted encode_u32 appends exactly the model's LEB128 encoding",
    register% varint.decode_ok_refines     ItemType.E2 2 true 2411497388
      "an extracted decode_u32 success is a model decode success",
    register% varint.decode_complete       ItemType.E2 2 true 3091262018
      "a model decode success below 2^32 is an extracted decode_u32 success",
    register% varint.decode_err_iff        ItemType.E1 1 true 3414750324
      "extracted decode_u32 errs iff the model fails or returns a value at or above 2^32",
    register% varint.roundtrip_extracted   ItemType.E2 2 true 35485382
      "the extracted decode inverts the extracted encode on every u32, no bound hypothesis",
    register% varint.instCodecLaws_extracted ItemType.E2 2 true 3731857118
      "CodecLaws on the extracted LEB128 codec over Std.U32",
    -- The extracted zigzag signed varint: the codec interface's second value type at the bridge
    -- (E2, and error agreement as E1). Every row below is varint's own theorem plus one scalar
    -- step; no LEB128 loop is reasoned about a second time.
    register% zigzag.zigzag_spec           ItemType.E1 1 true 3033183585
      "the extracted zigzag's signed shift and xor is the model's arithmetic zigzag map",
    register% zigzag.unzigzag_spec         ItemType.E1 1 true 2473696237
      "the extracted unzigzag is the model's unzigzag on every u32",
    register% zigzag.encode_refines        ItemType.E2 2 true 916046262
      "the extracted encode_i32 appends exactly the model's zigzag LEB128 encoding",
    register% zigzag.decode_ok_refines     ItemType.E2 2 true 3176892933
      "an extracted decode_i32 success is a model signed decode success",
    register% zigzag.decode_complete       ItemType.E2 2 true 1754870494
      "a model signed decode success inside the i32 range is an extracted decode_i32 success",
    register% zigzag.decode_err_iff        ItemType.E1 1 true 1411820494
      "extracted decode_i32 errs exactly when the underlying varint decode does, unchanged",
    register% zigzag.roundtrip_extracted   ItemType.E2 2 true 1675764305
      "the extracted decode inverts the extracted encode on every i32, no bound hypothesis",
    register% zigzag.instCodecLaws_extracted ItemType.E2 2 true 3742193170
      "CodecLaws on the extracted zigzag signed codec over Std.I32",
    -- The extracted HDLC byte-stuffing codec (E2, and error agreement as E1)
    register% stuff.stuff_refines          ItemType.E2 2 true 2814710957
      "the extracted stuff appends exactly the model's stuffed payload",
    register% stuff.encode_frame_refines   ItemType.E2 2 true 1328481543
      "the extracted encode_frame appends the stuffed payload and the terminating flag",
    register% stuff.decode_ok_refines      ItemType.E2 2 true 3002366595
      "an extracted unstuff success is a model decode success with the same residual",
    register% stuff.decode_complete        ItemType.E2 2 true 1976159975
      "a model decode success is an extracted unstuff success",
    register% stuff.decode_err_iff         ItemType.E1 1 true 803059870
      "extracted unstuff errs exactly when the model fails: an exact agreement",
    register% stuff.roundtrip_extracted    ItemType.E2 2 true 3256256942
      "the extracted unstuff inverts the extracted encode_frame, consuming every byte",
    register% stuff.instCodecLaws_extracted ItemType.E2 2 true 3340467780
      "CodecLaws on the extracted HDLC stuffing codec over byte lists",
    -- The extracted CRC-8 (E2, and table agreement as E1)
    register% crc8.table_agrees            ItemType.E1 1 true 3543992442
      "the extracted TABLE is the model's table",
    register% crc8.crc8_refines            ItemType.E2 2 true 1907815776
      "the extracted bitwise crc8 computes the model's crc8Bits",
    register% crc8.crc8_table_refines      ItemType.E2 2 true 1047851566
      "the extracted crc8_table computes the model's crc8Table",
    register% crc8.crc8_table_eq_extracted ItemType.E2 2 true 2401624015
      "the extracted crc8_table and crc8 agree on every slice",
    register% crc8.instChecksumLaws_extractedBitwise ItemType.E2 2 true 2485452198
      "ChecksumLaws on the extracted bitwise CRC-8",
    register% crc8.instChecksumLaws_extractedTabled ItemType.E2 2 true 3510475711
      "ChecksumLaws on the extracted table-driven CRC-8",
    -- The extracted RFC 1982 sequence number (refinements E2, the const and the two accessors E1).
    -- One row per non-derived in-subset candidate of certificate/candidates.txt, HALF_val included:
    -- the extraction emits a `pub const` as its own item, so it needs a statement about it like any
    -- function. No row for transitivity, and there never will be -- lean/FramedChannel/Evidence/
    -- Countermodels.lean refutes it in the kernel. Left unregistered: half_eq, the three
    -- abstraction-bijection lemmas, the four ext*-lowering lemmas and ext_iter, which are steps of
    -- the rows below rather than obligations of their own.
    register% seq_num.HALF_val             ItemType.E1 1 true 1948023598
      "the extracted HALF const is 2 ^ 15",
    register% seq_num.new_refines          ItemType.E1 1 true 3125499594
      "the extracted constructor stores exactly the word it is given",
    register% seq_num.get_refines          ItemType.E1 1 true 969973672
      "the extracted accessor returns exactly the stored word",
    register% seq_num.succ_refines         ItemType.E2 2 true 4279886007
      "the extracted succ is the model's succ, wraparound included, with no failure case",
    register% seq_num.add_refines          ItemType.E2 2 true 3675267517
      "the extracted add is the model's add on every increment, no range hypothesis",
    register% seq_num.dist_refines         ItemType.E2 2 true 3898242914
      "the extracted dist is the model's forward modular distance",
    register% seq_num.lt_refines           ItemType.E2 2 true 1716426734
      "the extracted zero-test-then-compare agrees with the model's serial comparison on every pair",
    register% seq_num.instSerialLaws_extracted ItemType.E2 2 true 4100308153
      "SerialLaws on the extracted 16-bit sequence number",
    -- The frame clone record (E1)
    register% cloneVecU8_isId              ItemType.E1 1 true 1020675802
      "the derived Clone of Vec<u8> returns its argument, so CloneIsId is proved, not assumed",
    -- The extracted frame codec (E2)
    register% channel.encode_frame_refines ItemType.E2 2 true 143260776
      "the extracted encode_frame appends exactly Channel.encodeFrame, via the component refinements",
    register% channel.parse_frame_refines  ItemType.E2 2 true 1250880147
      "the extracted parse_frame agrees with Channel.parseFrame, the wide-length divergence stated",
    register% channel.parse_frame_encode_frame_extracted ItemType.E2 2 true 2695668133
      "the extracted parser returns exactly an encoded payload and consumes exactly its frame",
    register% channel.parse_frame_len126_extracted ItemType.E2 2 true 1336354845
      "a 126-byte payload's frame starts with two markers and the extracted parser still returns it",
    -- The extracted channel operations, over any lawful queue record (E2, observers E1)
    register% channel.send_refines         ItemType.E2 2 true 848189739
      "the extracted send refines Channel.send over any simulating queue record",
    register% channel.deliver_refines      ItemType.E2 2 true 3801788286
      "the extracted deliver refines Channel.deliver over any simulating queue record",
    register% channel.take_refines         ItemType.E1 1 true 2427135741
      "the extracted take pops what the specification queue pops",
    register% channel.queued_agrees        ItemType.E1 1 true 3924867766
      "the extracted queued is the specification queue's length",
    -- The composition theorems at the extracted code, over any lawful queue record
    register% channel.send_deliver_extracted ItemType.E2 2 true 2524957248
      "extracted send then deliver returns exactly the payload and the channel is idle again",
    register% channel.deliver_spec_extracted ItemType.E2 2 true 3717737721
      "extracted deliver returns the oldest pending frame and keeps ChanInv",
    register% channel.send_inv_extracted   ItemType.E2 2 true 871895153
      "extracted send keeps ChanInv with the payload pending",
    register% channel.send_bounded_extracted ItemType.E1 1 true 1011535404
      "after an extracted send, queued plus in-flight is within capacity",
    register% channel.send_refuses_too_long_extracted ItemType.E1 1 true 2318995260
      "the extracted send refuses a payload longer than u32::MAX with the channel unchanged",
    register% channel.send_discharges_not_full_extracted ItemType.E1 1 true 3164780004
      "a successful extracted send leaves the record's is_full false",
    -- Substitution Channel[RB/VQ] on the extracted code, from the constructors
    register% channel.new_idle_RB          ItemType.E1 1 true 3755686700
      "Channel::new over the extracted ring buffer starts idle",
    register% channel.with_queue_idle_VQ   ItemType.E1 1 true 2549062098
      "Channel::with_queue over the extracted VecQueue starts idle",
    register% channel.send_deliver_extracted_RB ItemType.E2 2 true 1280726709
      "send_deliver_extracted at the extracted ring buffer, no trait or simulation hypothesis",
    register% channel.send_deliver_extracted_VQ ItemType.E2 2 true 1341939224
      "send_deliver_extracted at the extracted VecQueue, no reproof",
    register% channel.deliver_spec_extracted_RB ItemType.E2 2 true 3604764252
      "deliver_spec_extracted at the extracted ring buffer",
    register% channel.deliver_spec_extracted_VQ ItemType.E2 2 true 3871528595
      "deliver_spec_extracted at the extracted VecQueue, no reproof",
    register% channel.send_deliver_from_new_RB ItemType.E2 2 true 3615146268
      "from Channel::new, send then deliver returns exactly the payload and queued is 1",
    register% channel.send_deliver_from_new_VQ ItemType.E2 2 true 3003114898
      "from Channel::with_queue at VecQueue, send then deliver returns the payload and queued is 1",
    -- The extracted transparent frame codec (E2)
    register% stuffed_channel.body_refines ItemType.E2 2 true 885567149
      "the extracted body is exactly StuffedChannel.body, via the component refinements",
    register% stuffed_channel.encode_stuffed_refines ItemType.E2 2 true 1503288945
      "the extracted encode_stuffed appends exactly StuffedChannel.encodeStuffed",
    register% stuffed_channel.parse_stuffed_refines ItemType.E2 2 true 1890771692
      "the extracted parse_stuffed agrees with parseStuffed, the wide-length divergence stated",
    register% stuffed_channel.parse_stuffed_encode_stuffed_extracted ItemType.E2 2 true 1691742109
      "the extracted parser returns exactly a stuffed payload and consumes exactly its frame",
    register% stuffed_channel.wire_flag_free_extracted ItemType.E2 2 true 83924376
      "TRANSPARENCY: the extracted encoder writes the flag nowhere but at the frame terminator",
    -- The extracted transparent channel's operations, over any lawful queue record
    register% stuffed_channel.send_refines ItemType.E2 2 true 3038551081
      "the extracted send refines StuffedChannel.send over any simulating queue record",
    register% stuffed_channel.deliver_refines ItemType.E2 2 true 2682277024
      "the extracted deliver refines StuffedChannel.deliver over any simulating queue record",
    register% stuffed_channel.take_refines ItemType.E1 1 true 1050190484
      "the extracted take pops what the specification queue pops",
    register% stuffed_channel.queued_agrees ItemType.E1 1 true 274262075
      "the extracted queued is the specification queue's length",
    -- The composition theorems at the extracted code, over any lawful queue record
    register% stuffed_channel.send_deliver_extracted ItemType.E2 2 true 1467499622
      "extracted send then deliver returns exactly the payload across the transparent framing",
    register% stuffed_channel.deliver_spec_extracted ItemType.E2 2 true 1835972321
      "extracted deliver returns the oldest pending frame and keeps SChanInv",
    register% stuffed_channel.send_inv_extracted ItemType.E2 2 true 598349482
      "extracted send keeps SChanInv with the payload pending",
    register% stuffed_channel.send_bounded_extracted ItemType.E1 1 true 893343725
      "after an extracted send, queued plus in-flight is within capacity",
    register% stuffed_channel.send_refuses_too_long_extracted ItemType.E1 1 true 362613509
      "the extracted send refuses a payload longer than u32::MAX with the channel unchanged",
    register% stuffed_channel.send_discharges_not_full_extracted ItemType.E1 1 true 1226408053
      "a successful extracted send leaves the record's is_full false",
    -- Substitution StuffedChannel[RB/VQ] on the extracted code, from the constructors
    register% stuffed_channel.new_idle_RB ItemType.E1 1 true 3397868298
      "StuffedChannel::new over the extracted ring buffer starts idle",
    register% stuffed_channel.with_queue_idle_VQ ItemType.E1 1 true 2283655350
      "StuffedChannel::with_queue over the extracted VecQueue starts idle",
    register% stuffed_channel.send_deliver_extracted_RB ItemType.E2 2 true 974921122
      "send_deliver_extracted at the extracted ring buffer, no trait or simulation hypothesis",
    register% stuffed_channel.send_deliver_extracted_VQ ItemType.E2 2 true 2439099929
      "send_deliver_extracted at the extracted VecQueue, no reproof",
    register% stuffed_channel.deliver_spec_extracted_RB ItemType.E2 2 true 3276226080
      "deliver_spec_extracted at the extracted ring buffer",
    register% stuffed_channel.deliver_spec_extracted_VQ ItemType.E2 2 true 589261324
      "deliver_spec_extracted at the extracted VecQueue, no reproof",
    register% stuffed_channel.send_deliver_from_new_RB ItemType.E2 2 true 3473441069
      "from StuffedChannel::new, send then deliver returns exactly the payload and queued is 1",
    register% stuffed_channel.send_deliver_from_new_VQ ItemType.E2 2 true 4072884471
      "from StuffedChannel::with_queue at VecQueue, send then deliver returns the payload, queued 1",
    -- The extracted resynchronizing receive path: the run judgement and the scan's operations
    register% receiver.finish_run_refines ItemType.E2 2 true 2023119827
      "the extracted finish_run judges a run exactly as the model does, the wide-length divergence stated",
    register% receiver.feed_refines ItemType.E2 2 true 1645347416
      "the extracted feed refines Receiver.feed over any simulating queue record",
    register% receiver.poll_refines ItemType.E2 2 true 752336997
      "the extracted poll hands back exactly what the specification queue pops, None exactly on fail",
    register% receiver.dropped_agrees ItemType.E1 1 true 2944714371
      "the extracted dropped counter is the specification's drop count",
    register% receiver.queued_agrees ItemType.E1 1 true 1829937693
      "the extracted queued is the length of the specification queue's contents",
    -- and its substitution rows at both extracted queues
    register% receiver.new_idle_RB ItemType.E1 1 true 1199007643
      "Receiver::new starts idle at every capacity: no buffered run, no drops, nothing accepted",
    register% receiver.with_queue_idle_VQ ItemType.E1 1 true 794053247
      "Receiver::with_queue at the extracted VecQueue starts idle",
    register% receiver.feed_refines_RB ItemType.E2 2 true 211955102
      "feed_refines at the extracted ring buffer, no simulation hypothesis left",
    register% receiver.feed_refines_VQ ItemType.E2 2 true 565359218
      "feed_refines at the extracted VecQueue, no reproof",
    register% receiver.poll_refines_RB ItemType.E2 2 true 1397941225
      "poll_refines at the extracted ring buffer",
    register% receiver.poll_refines_VQ ItemType.E2 2 true 1655138489
      "poll_refines at the extracted VecQueue, no reproof" ]

/-- The bridge package's own bank. -/
def bank : List Item := toBank items

/-- Every certified row of both packages: the core registry, then the bridge's. -/
def allItems : List CertifiedItem := FramedChannel.items ++ FramedChannel.Bridge.items

/-- The combined bank the scoring machinery consumes. -/
def allBank : List Item := toBank allItems

-- As in the core registry, auditing the aggregates audits every spliced proof term at once.
#print axioms allItems
#print axioms allBank

/-- One hundred and twenty-three bridge rows. -/
example : bank.length = 123 := by decide

-- At this many rows, every `decide` over the combined bank -- not only the witness strings --
-- needs more than the default recursion depth.
set_option maxRecDepth 4096 in
/-- Two hundred and three rows across both packages. -/
example : allBank.length = 203 := by decide

set_option maxRecDepth 4096 in
/-- Every row, in both packages, names a nonvacuity witness. -/
example : allBank.all Item.hasWitness = true := by decide

/-- No open item is ever scored (free for any bank). -/
example : noOpenScored allBank := noOpenScored_all allBank

set_option maxRecDepth 4096 in
/-- The kernel-scored total over both packages. -/
example : totalScore allBank = 531 := by decide

set_option maxRecDepth 4096 in
/-- The achievable total over both packages, counting the two compiler-trusting core rows. -/
example : totalMax allBank = 535 := by decide

end FramedChannel.Bridge
