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
import FramedChannelAeneas.Bridge.Crc8.Defs
import FramedChannelAeneas.Bridge.Crc8.Bitwise
import FramedChannelAeneas.Bridge.Crc8.Table
import FramedChannelAeneas.Bridge.Crc8.Instance
import FramedChannelAeneas.Bridge.Channel.Defs
import FramedChannelAeneas.Bridge.Channel.Abstraction
import FramedChannelAeneas.Bridge.Channel.Frame
import FramedChannelAeneas.Bridge.Channel.Refinement
import FramedChannelAeneas.Bridge.Channel.Composite
import FramedChannelAeneas.Bridge.Channel.Instance

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
* The extracted CRC-8 (`Bridge/Crc8/`): `crc8_refines`, `crc8_table_refines`, the extracted-level
  equivalence `crc8_table_eq_extracted` and the two `ChecksumLaws` instances as `E2`, and
  `table_agrees` as `E1`.
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

Deliberately not registered: the `Aeneas` step lemmas `set_spec`/`get_spec` and `set_opt_some`,
the `BQ` lifting lemmas `pushBQ_of_push`/`popBQ_of_pop`, `len_agrees` (an input to
`ring_buffer.sim`, whose row covers it), and `Bridge/Queue/Traits.lean`'s `cln_isId`. Likewise the
library-gap step specifications of `Bridge/Std.lean`, the lowering read-through lemmas of
`Bridge/Queue/Instance.lean`, the carrier and functionality lemmas of each queue instance, the loop
lemmas and their invariants (`encode_loop_refines`, `decode_loop_refines`, `decode_refines`,
`inner_loop_refines`, `outer_loop_refines`, `table_loop_refines`), the `Nat` and scalar arithmetic
lemmas, and the digest/step identification lemmas of `Bridge/Crc8/Instance.lean`. The CRC-8
`inner_refines` is kept supporting too: it is the `@[step]` specification `crc8_refines` is
walked with, and `crc8_refines`'s row covers it. `decode_refines` is covered by the three decode
rows derived from it. In the channel bridge, the abstraction (`vecOfFrame`, `ofFrame_val`,
`ofFrame_bitsOf`, `frameOK_fits`, `u32_max_le_usize_max`, `bitsOf_eq_bytesOf_map`), the parser
helpers of `Bridge/Channel/Frame.lean`, `drop_front_refines`, `not_declaresWide_encodeFrame`,
`hovf_of_inv`, the generic `with_queue_idle` and each queue's `with_capacity_rel` are supporting.
They are proved and audited, and listed under `supporting:` in the
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
      "from Channel::with_queue at VecQueue, send then deliver returns the payload and queued is 1" ]

/-- The bridge package's own bank. -/
def bank : List Item := toBank items

/-- Every certified row of both packages: the core registry, then the bridge's. -/
def allItems : List CertifiedItem := FramedChannel.items ++ FramedChannel.Bridge.items

/-- The combined bank the scoring machinery consumes. -/
def allBank : List Item := toBank allItems

-- As in the core registry, auditing the aggregates audits every spliced proof term at once.
#print axioms allItems
#print axioms allBank

/-- Sixty-six bridge rows. -/
example : bank.length = 66 := by decide

/-- One hundred and five rows across both packages. -/
example : allBank.length = 105 := by decide

-- At this many rows, deciding the witness strings needs more than the default recursion depth.
set_option maxRecDepth 4096 in
/-- Every row, in both packages, names a nonvacuity witness. -/
example : allBank.all Item.hasWitness = true := by decide

/-- No open item is ever scored (free for any bank). -/
example : noOpenScored allBank := noOpenScored_all allBank

/-- The kernel-scored total over both packages. -/
example : totalScore allBank = 274 := by decide

/-- The achievable total over both packages, counting the one compiler-trusting core row. -/
example : totalMax allBank = 276 := by decide

end FramedChannel.Bridge
