-- SPDX-License-Identifier: Apache-2.0
import FramedChannelAeneasChallenge.Queue
import FramedChannelAeneasChallenge.RingBuffer
import FramedChannelAeneasChallenge.VecQueue
import FramedChannelAeneasChallenge.Varint
import FramedChannelAeneasChallenge.Zigzag
import FramedChannelAeneasChallenge.Stuff
import FramedChannelAeneasChallenge.Crc8
import FramedChannelAeneasChallenge.SeqNum
import FramedChannelAeneasChallenge.Channel

/-!
# FramedChannelAeneasChallenge: the bridge package's approved specification

The bridge package's statement-only Challenge library, and Comparator's `challenge_module` for it:
one module per component, plus `Queue` for the component-independent queue transport theorems and
the `Clone` assumption, each restating its registered theorems of
`aeneas/FramedChannelAeneas/Registry.lean` with `:= sorry`. What such a library is and how the gate
checks it is described once, in `lean/FramedChannelChallenge.lean`.
-/
