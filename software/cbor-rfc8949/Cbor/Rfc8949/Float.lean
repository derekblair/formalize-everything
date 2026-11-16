/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Float.IEEE754
import Cbor.Rfc8949.Float.Narrowing
import Cbor.Rfc8949.Float.DataModel
import Cbor.Rfc8949.Float.Vectors

/-!
# RFC 8949 Milestone 2: IEEE 754 Floating-Point Slice (FE #126)

Aggregates the four Milestone 2 IEEE 754 floating-point modules extending the
Milestone 1 float-free CBOR formalization to all of RFC 8949 major type 7
additional information 25/26/27 (`0xf9` `binary16`, `0xfa` `binary32`,
`0xfb` `binary64`):

* `Cbor.Rfc8949.Float.IEEE754` — explicit bit-level `Float16` / `Float32` /
  `Float64` / `CborFloat` layouts, wire encoders and decoders (`0xf9`/`0xfa`/`0xfb`),
  in-kernel round-trip and prefix-uniqueness proofs, 5-way IEEE 754 value
  classifications, exact `IEEEValue` valuation, and RFC 8949 Appendix D
  half-precision bit-extraction correspondence;
* `Cbor.Rfc8949.Float.Narrowing` — value-preserving widenings and stepwise
  `binary64 → binary32 → binary16` narrowings (`narrow64To32?`, `narrow32To16?`,
  `narrow64To16?`), §4.1 preferred shortest-float serialization (`preferredFloat`,
  `encodeFloatPreferred_shortest`, `decodeFloatPreferred`), §4.2.1 / §4.2.2 core
  deterministic NaN canonicalization to `0xf97e00` (`canonicalFloatDet`,
  `decodeFloatDeterministic`), IEEE 754 RNE lossy narrowing (`round64To32`,
  `round32To16`), and boundary theorems (signed zero, `±Infinity`, NaN payloads,
  subnormals, and lossy precision narrowing / overflow / underflow);
* `Cbor.Rfc8949.Float.DataModel` — §2 / §5.6.1 float data-model equivalence
  (`FloatEquiv`, `canonFloatKey`, `FullItem.Equiv`), full CBOR wire grammar
  (`FullHead`, `FullRawItem`, `FullItem`, `parseFullRaw_eq_some_iff`),
  conservative extension over Milestone 1, and refusal of all 94 Appendix F.1
  malformed byte sequences (including Group 1's 3 truncated float heads)
  alongside acceptance of complete 2/4/8-byte float heads;
* `Cbor.Rfc8949.Float.Vectors` — bidirectional in-kernel verification of all
  **23** float-containing RFC 8949 Appendix A rows (`19..40` and row `49`,
  `1(1363896240.5)`) and the complete **81**-row Appendix A partition (`58 + 23 = 81`).
-/
