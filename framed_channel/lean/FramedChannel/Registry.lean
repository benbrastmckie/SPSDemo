-- SPDX-License-Identifier: Apache-2.0
import FramedChannel.Certify
import FramedChannel.Model.RingBuffer.Theorems
import FramedChannel.Model.Varint.Theorems
import FramedChannel.Model.Crc8.Theorems
import FramedChannel.Model.Stuff.Theorems
import FramedChannel.Model.Zigzag.Theorems
import FramedChannel.Model.SeqNum.Theorems
import FramedChannel.Model.VecQueue.Theorems
import FramedChannel.Composition.Channel.Theorems
import FramedChannel.Composition.Channel.Instances
import FramedChannel.Composition.StuffedChannel.Theorems
import FramedChannel.Composition.StuffedChannel.Instances

/-!
# Registry: the example's rows in the verified component library

The core package's certified theorems -- the seven components', the second queue instance's and the
channel composite's -- are registered as `CertifiedItem` rows through `Certify.lean`'s `register%`.
The macro resolves each name at elaboration and splices its proof term into the row, and it binds
the row to the structural hash of the theorem's elaborated statement, so a row cannot name a
missing theorem and a changed statement fails the build with a drift error
(`scripts/refresh-hashes.sh` regenerates the column). The bank is scored by kernel `decide`. The bridge
package's rows are registered the same way in `aeneas/FramedChannelAeneas/Registry.lean`, whose
`allBank` concatenates both. Rows use item types `E1` (error agreement, bounds, step facts) and
`E2` (invariants, refinement, composition, lemma nodes), defined with the tier weights in
`Certify.lean`; `verified := true` only where `certificate/axioms.txt` shows the trusted axiom set,
which `check.sh` cross-checks (`certificate/README.md`).

## Edges

```
refines        RingBuffer -> BoundedQueue   (RingBuffer.instBoundedQueueLaws; Rust RingBuffer<T>)
refines        VQ         -> BoundedQueue   (VecQueue.instBoundedQueueLaws;   Rust VecQueue<T>)
refines        Varint     -> CodecLaws      (Varint.instCodecLaws)
refines        Stuff      -> CodecLaws      (Stuff.instCodecLaws)
refines        Crc8       -> ChecksumLaws   (Crc8.instChecksumLawsBitwise, ...Tabled)
refines        Zigzag     -> CodecLaws      (Zigzag.instCodecLaws; alpha = Int)
refines        Serial     -> SerialLaws     (SeqNum.instSerialLaws; RFC 1982 serial arithmetic)
distilled_from inv_preserve   <- {push_inv, pop_inv}
distilled_from refine_commute <- {push_contents, pop_contents}
distilled_from Zigzag.zigzag_roundtrip  <- CodecLaws.round_trip at Leb128 (retrieval rung)
distilled_from Zigzag.encode_length_le <- CodecLaws.length_le  at Leb128 (retrieval rung)
lemma_node     idx_ne <- push_contents
composition    Channel.send_deliver <- {parseFrame_encodeFrame, varint_roundtrip,
                                        crc8_table_eq_bits, push_law, not_full_of_lt,
                                        push_capacity}
composition    StuffedChannel.send_deliver <- {Transparent.decode_append, varint_roundtrip,
                                        ChecksumModel.digest, push_law, not_full_of_lt,
                                        push_capacity}
refines        Stuff -> Transparent        (StuffedChannel.instTransparentHdlc; composition layer)
substitution   Channel[VQ/BQ]  (deliver_spec_RB, deliver_spec_VQ: one proof, two instances)
substitution   StuffedChannel[VQ/BQ]  (deliver_spec_RB, deliver_spec_VQ at the second composite)
equivalence    crc8_step_linear_kernel ≃ crc8_step_linear  (kernel replay of the bv_decide row)
equivalence    SeqNum.lt_eq_ltRFC_kernel ≃ SeqNum.lt_eq_ltRFC  (kernel replay of the bv_decide row)
refuted        transitivity of SeqNum.lt  (Evidence/Countermodels.lean; no SerialLaws field)
```

The edges are documentation, not a Lean object. `crc8_step_linear` carries a native `bv_decide`
helper axiom, so its row is `verified := false` and scores `0`; `crc8_step_linear_kernel` is
registered beside it.
-/

namespace FramedChannel

open FramedChannel.Certify

def items : List CertifiedItem :=
  [ -- RingBuffer: error agreement (E1)
    register% RingBuffer.push_ok       ItemType.E1 1 true 1192943376 "push on a non-full buffer",
    register% RingBuffer.push_fail     ItemType.E1 1 true 518357034 "push on a full buffer",
    register% RingBuffer.pop_ok        ItemType.E1 1 true 1577812817 "pop on a non-empty buffer",
    register% RingBuffer.pop_fail      ItemType.E1 1 true 1891848527 "pop on an empty buffer",
    -- RingBuffer: invariant preservation and refinement (E2)
    register% RingBuffer.push_inv      ItemType.E2 2 true 1577302354 "Inv preserved by push",
    register% RingBuffer.pop_inv       ItemType.E2 2 true 1303702960 "Inv preserved by pop",
    register% RingBuffer.push_contents ItemType.E2 2 true 1661877327 "contents ++ [x] under push",
    register% RingBuffer.pop_contents  ItemType.E2 2 true 3848959537 "x :: contents under pop",
    register% RingBuffer.idx_ne        ItemType.E2 1 true 1027401513 "modular-index lemma node",
    register% RingBuffer.push_bounded  ItemType.E1 1 true 1786983105
      "push keeps occupancy inside the backing store",
    register% RingBuffer.push_spec     ItemType.E2 2 true 1139391421
      "the step-shaped push postcondition: success, Inv and contents ++ [x] together",
    register% RingBuffer.pop_spec      ItemType.E2 2 true 1558365123
      "the step-shaped pop postcondition: success, Inv and x :: contents together",
    register% RingBuffer.instBoundedQueueLaws ItemType.E2 2 true 3257214348
      "BQ satisfies the six bounded-queue laws",
    -- Crc8
    register% Crc8.crc8_step_linear    ItemType.E1 1 false 3899763328
      "bv_decide: native helper axiom present; compiler-trusting, not counted as verified",
    register% Crc8.crc8_step_linear_kernel ItemType.E1 1 true 3899763328
      "kernel replay of crc8_step_linear, no bv_decide",
    register% Crc8.crc8_table_eq_bits  ItemType.E2 2 true 226738400 "table lookup = bitwise loop",
    register% Crc8.stepTable_index_in_range ItemType.E1 1 true 2241815235
      "the table index is always in range, so the getD default is unreachable",
    register% Crc8.instChecksumLawsBitwise ItemType.E2 2 true 2304322707
      "the bitwise loop satisfies the checksum laws",
    register% Crc8.instChecksumLawsTabled ItemType.E2 2 true 1805334493
      "the table implementation satisfies the same checksum laws",
    -- Varint
    register% Varint.varint_roundtrip  ItemType.E2 2 true 792785387
      "decode (encode n) for n < 2^32",
    register% Varint.encode_length_le  ItemType.E1 1 true 1332426029
      "the encoding fits in five bytes on the u32 domain",
    register% Varint.instCodecLaws     ItemType.E2 2 true 3510309193
      "LEB128 satisfies the codec laws",
    -- Zigzag: the signed varint, the codec interface's second value type
    register% Zigzag.zigzag_lt         ItemType.E1 1 true 2039420113
      "on the i32 range the zigzag image lies in the varint's u32 domain",
    register% Zigzag.unzigzag_zigzag   ItemType.E2 2 true 462946453
      "unzigzag inverts zigzag on all of Int, hypothesis-free",
    register% Zigzag.zigzag_unzigzag   ItemType.E1 1 true 4057087783
      "zigzag inverts unzigzag on all of Nat, hypothesis-free",
    register% Zigzag.decode_fail_iff   ItemType.E1 1 true 1025070864
      "the signed decode fails exactly when the underlying LEB128 decode fails",
    register% Zigzag.zigzag_roundtrip  ItemType.E2 2 true 1979916437
      "decode (encode n) on the i32 range, retrieved from CodecLaws at Leb128",
    register% Zigzag.encode_length_le  ItemType.E1 1 true 1980960392
      "the signed encoding fits in five bytes, retrieved from the varint's own bound",
    register% Zigzag.instCodecLaws     ItemType.E2 2 true 1653379488
      "the zigzag signed varint satisfies the codec laws at alpha = Int",
    -- Stuff: HDLC-style byte stuffing
    register% Stuff.stuff_marker_free  ItemType.E1 1 true 4085196778
      "a stuffed payload contains no frame boundary byte",
    register% Stuff.stuff_roundtrip    ItemType.E2 2 true 4090422188
      "decode (encode p) for every payload, with nothing left over",
    register% Stuff.stuff_length_le    ItemType.E1 1 true 3415623517
      "stuffing at most doubles the payload",
    register% Stuff.encode_length_le   ItemType.E1 1 true 1319576769
      "the framed encoding is at most twice the payload plus the flag",
    register% Stuff.instCodecLaws      ItemType.E2 2 true 677937794
      "HDLC byte stuffing satisfies the codec laws",
    -- SeqNum: RFC 1982 serial-number arithmetic over a 16-bit space
    register% SeqNum.lt_irrefl         ItemType.E1 1 true 1076733227
      "no sequence number is serially before itself",
    register% SeqNum.lt_succ           ItemType.E1 1 true 15704829
      "every sequence number is serially before its successor",
    register% SeqNum.lt_add            ItemType.E1 1 true 1017918142
      "advancing by a positive increment below half the space lands strictly after",
    register% SeqNum.lt_eq_ltRFC       ItemType.E1 1 false 563281444
      "bv_decide: native helper axiom present; compiler-trusting, not counted as verified",
    register% SeqNum.lt_eq_ltRFC_kernel ItemType.E1 1 true 563281444
      "kernel replay of lt_eq_ltRFC, no bv_decide",
    register% SeqNum.iter_ne_of_pos_lt ItemType.E1 1 true 1706830143
      "fewer than space successor steps never return to the start",
    register% SeqNum.dist_add          ItemType.E2 2 true 253958028
      "the forward distance recovers the increment",
    register% SeqNum.iter_space        ItemType.E2 2 true 2753338996
      "space successor steps return to where they started",
    register% SeqNum.lt_total_of_defined ItemType.E2 2 true 1940534923
      "distinct numbers outside the undefined region are ordered one way or the other",
    register% SeqNum.lt_translation_invariant ItemType.E2 2 true 186798179
      "advancing both arguments leaves the comparison unchanged",
    register% SeqNum.instSerialLaws    ItemType.E2 2 true 4260512589
      "the canonical 16-bit model satisfies the serial-number laws",
    -- VecQueue: the second bounded-queue instance (E2)
    register% VecQueue.instBoundedQueueLaws ItemType.E2 2 true 2688892127
      "VQ satisfies the six laws",
    register% VecQueue.push_bounded    ItemType.E1 1 true 1894308572
      "a successful VQ push keeps the item count within cap",
    -- Channel: the composite, generic over BoundedQueueLaws (E1, E2)
    register% Channel.send_discharges_not_full ItemType.E1 1 true 1161670808
      "send's capacity check discharges push's not-full assumption",
    register% Channel.parseFrame_encodeFrame   ItemType.E2 2 true 3776725821
      "frame round trip from varint_roundtrip",
    register% Channel.deliver_spec             ItemType.E2 2 true 2919652787
      "deliver pushes exactly the oldest pending frame",
    register% Channel.send_deliver             ItemType.E2 2 true 1684866014
      "send then deliver pushes exactly p",
    register% Channel.send_bounded             ItemType.E1 1 true 2349956348
      "after a successful send, queued plus in-flight is still within capacity",
    register% Channel.send_inv                 ItemType.E2 2 true 2247583546
      "send preserves the channel invariant, adding the frame to the pending list",
    register% Channel.send_refuses_too_long    ItemType.E1 1 true 2720528573
      "send refuses every payload of 2^32 bytes or more",
    register% Channel.encodeFrameTable_eq      ItemType.E2 2 true 435906632
      "the table-driven frame encoder equals the bitwise one",
    register% Channel.deliver_spec_RB          ItemType.E2 2 true 3048722796
      "deliver_spec at the ring buffer, no reproof",
    register% Channel.deliver_spec_VQ          ItemType.E2 2 true 3997164531
      "deliver_spec at the list-backed queue, no reproof",
    -- StuffedChannel: the transparent composite, generic over three interfaces (E1, E2)
    register% StuffedChannel.parseStuffed_encodeStuffed ItemType.E2 2 true 3041772710
      "one frame recovered off a stuffed wire, marker-bearing payloads included",
    register% StuffedChannel.wire_flag_free_of_send ItemType.E2 2 true 4224761467
      "no byte written but the frame terminator is the flag: the theorem Channel cannot have",
    register% StuffedChannel.instTransparentHdlc ItemType.E2 2 true 1718778575
      "HDLC stuffing satisfies the composition-layer transparency bundle",
    register% StuffedChannel.send_discharges_not_full ItemType.E1 1 true 3372159519
      "send's capacity check discharges push's not-full assumption",
    register% StuffedChannel.send_bounded      ItemType.E1 1 true 10753178
      "after a successful send, queued plus in-flight is still within capacity",
    register% StuffedChannel.send_refuses_too_long ItemType.E1 1 true 3680170140
      "send refuses every payload of 2^32 bytes or more",
    register% StuffedChannel.send_inv          ItemType.E2 2 true 2903275266
      "send preserves the invariant, adding the frame to the pending list",
    register% StuffedChannel.deliver_spec      ItemType.E2 2 true 2072346319
      "deliver pushes exactly the oldest pending frame off the stuffed wire",
    register% StuffedChannel.send_deliver      ItemType.E2 2 true 4186265589
      "send then deliver pushes exactly p across the transparent framing",
    register% StuffedChannel.deliver_spec_RB   ItemType.E2 2 true 3039473024
      "deliver_spec at the ring buffer, HDLC framing, bitwise CRC-8, no reproof",
    register% StuffedChannel.deliver_spec_VQ   ItemType.E2 2 true 3830547097
      "deliver_spec at the list-backed queue, no reproof" ]

/-- The example's bank, in the shape the scoring machinery consumes. -/
def bank : List Item := toBank items

-- Auditing `items` audits every spliced proof term at once: each row's `cert` field IS the
-- registered theorem's proof, so this one record covers the whole bank's dependency set.
#print axioms items
#print axioms bank

/-- Sixty-eight rows. -/
example : bank.length = 68 := by decide

/-- Every row names a nonvacuity witness. -/
example : bank.all Item.hasWitness = true := by decide

/-- No open item is ever scored (free for any bank). -/
example : noOpenScored bank := noOpenScored_all bank

/-- The kernel-scored total. -/
example : totalScore bank = 170 := by decide

/-- The achievable total, counting the two compiler-trusting rows. -/
example : totalMax bank = 174 := by decide

/-! ## Coverage: what is deliberately not registered

Every component has at minimum an error-agreement or bounds row (`E1`) and a refinement row
(`E2`). Left out on purpose:

* `RingBuffer.push_inv_grind`, `push_inv_tac`, `push_contents_tac`, `pop_contents_tac` --
  automation measurements, not obligations. They are proved and audited; they earn no bank row.
* (Stuff leaves nothing out either: all four of its theorems and its `CodecLaws` instance are
  registered. The supporting lemmas -- the xor identities, the `stuffByte` equations, the decoder's
  generalized loop invariant `unstuff_stuff`, and `stuff_bytes_lt` -- are steps of those five
  proofs, not obligations of their own, so they earn no bank row.)
* (Crc8 leaves nothing out: BOTH `ChecksumLaws` instances are registered.
  `instChecksumLawsTabled` used to be excluded as double-counting `crc8_table_eq_bits`, but the
  bridge registers both of ITS extracted `ChecksumLaws` instances, so excluding the core's second
  one was an asymmetry between the two packages rather than a principle.)
* `Zigzag.encode_eq` -- the `rfl` bridge between the projection spelling of `encode` and
  `Varint.encode (zigzag n)`. It is a spelling identity the bridge package rewrites with, not an
  obligation of the codec, so it earns no bank row. Everything else the unit proves is registered:
  the bound, both directions of the bijection, error agreement, the two retrieved laws and the
  `CodecLaws` instance.

* `StuffedChannel.send_out` -- that `send` does not touch the output queue. It is a step of
  `send_deliver`, not an obligation of its own, and `Channel` does not register its analogue
  either. Every other theorem the unit proves is registered: the transparency round trip, the
  marker-free wire, the `Transparent` instance, both bounds rows, the length refusal, the
  invariant, `deliver_spec`, `send_deliver` and the two queue instantiations.

Per-component coverage, item by item, is in the `coverage:` block of each manifest under
`certificate/`. -/

end FramedChannel
