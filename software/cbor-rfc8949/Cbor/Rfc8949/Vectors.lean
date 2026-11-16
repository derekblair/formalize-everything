/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Vectors.AppendixA
import Cbor.Rfc8949.Vectors.AppendixF1
import Cbor.Rfc8949.Vectors.Ordering

/-!
# RFC 8949 Milestone 1 In-Kernel Conformance Vector Suite

Aggregates the three RFC 8949 test-vector suites required by ticket #34
deliverable 6 (as amended by comment 6460668308):

* `Cbor.Rfc8949.Vectors.AppendixA` — all **58** float-free Appendix A rows
  verified in both directions (23 float-containing rows `19..40` and `49`
  belong to Milestone 2);
* `Cbor.Rfc8949.Vectors.AppendixF1` — all **94** Appendix F.1 not-well-formed
  byte sequences refused across all decoders;
* `Cbor.Rfc8949.Vectors.Ordering` — all **8** keys from the §4.2.1 / §4.2.3
  map-key ordering example verified across Core, Length-first, and CTAP2.
-/
