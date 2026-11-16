/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Ordering

/-!
# RFC 8949 §4.2.1 vs §4.2.3 vs CTAP2: the 8-key ordering vector suite

RFC 8949 §4.2.1 and §4.2.3 illustrate deterministic map-key ordering on the
same 8-key example set:

| Key diagnostic | Deterministic hex | Length | Major |
|----------------|-------------------|--------|-------|
| `10`           | `0a`              | 1      | 0     |
| `100`          | `18 64`           | 2      | 0     |
| `-1`           | `20`              | 1      | 1     |
| `"z"`          | `61 7a`           | 2      | 3     |
| `"aa"`         | `62 61 61`        | 3      | 3     |
| `[100]`        | `81 18 64`        | 3      | 4     |
| `[-1]`         | `81 20`           | 2      | 4     |
| `false`        | `f4`              | 1      | 7     |

The three profiles sort these 8 keys into three distinct total orders:

* **Core bytewise order (§4.2.1, `coreKeyOrder`):**
  `[10, 100, -1, "z", "aa", [100], [-1], false]`
* **Length-first order (§4.2.3 / RFC 7049 §3.9, `lengthFirstKeyOrder`):**
  `[10, -1, false, 100, "z", [-1], "aa", [100]]`
* **CTAP2 canonical CBOR order (FIDO CTAP2 §6, `ctap2KeyOrder`):**
  `[10, 100, -1, "z", "aa", [-1], [100], false]`
  (identical to §4.2.1 on the 6 atomic keys, reversed on `[100]` vs `[-1]`).
-/

namespace Cbor.Rfc8949.Vectors

/-- Named keys from the 8-key ordering table in RFC 8949 §4.2.1 and §4.2.3. -/
def ordKey10 : Item := .uint 10
def ordKey100 : Item := .uint 100
def ordKeyNeg1 : Item := .nint 0
def ordKeyZ : Item := .text [0x7a]
def ordKeyAA : Item := .text [0x61, 0x61]
def ordKeyArr100 : Item := .array [.uint 100]
def ordKeyArrNeg1 : Item := .array [.nint 0]
def ordKeyFalse : Item := Item.false_

/-- Expected RFC 8949 §4.2.1 (core bytewise-lexicographic) key list. -/
def rfc421CoreKeys : List Item := [
  ordKey10, ordKey100, ordKeyNeg1, ordKeyZ,
  ordKeyAA, ordKeyArr100, ordKeyArrNeg1, ordKeyFalse
]

/-- Expected RFC 8949 §4.2.3 (length-first / RFC 7049 §3.9) key list. -/
def rfc423LengthFirstKeys : List Item := [
  ordKey10, ordKeyNeg1, ordKeyFalse, ordKey100,
  ordKeyZ, ordKeyArrNeg1, ordKeyAA, ordKeyArr100
]

/-- Expected FIDO CTAP2 canonical CBOR key list on the same 8 keys. -/
def ctap2CanonicalKeys : List Item := [
  ordKey10, ordKey100, ordKeyNeg1, ordKeyZ,
  ordKeyAA, ordKeyArrNeg1, ordKeyArr100, ordKeyFalse
]

/-- Expected deterministic wire encodings in §4.2.1 order. -/
def rfc421CoreWires : List (List UInt8) := [
  [0x0a],
  [0x18, 0x64],
  [0x20],
  [0x61, 0x7a],
  [0x62, 0x61, 0x61],
  [0x81, 0x18, 0x64],
  [0x81, 0x20],
  [0xf4]
]

/-- Expected deterministic wire encodings in §4.2.3 length-first order. -/
def rfc423LengthFirstWires : List (List UInt8) := [
  [0x0a],
  [0x20],
  [0xf4],
  [0x18, 0x64],
  [0x61, 0x7a],
  [0x81, 0x20],
  [0x62, 0x61, 0x61],
  [0x81, 0x18, 0x64]
]

theorem rfc421CoreKeys_length : rfc421CoreKeys.length = 8 := rfl

theorem rfc423LengthFirstKeys_length : rfc423LengthFirstKeys.length = 8 := rfl

theorem ctap2CanonicalKeys_length : ctap2CanonicalKeys.length = 8 := rfl

/-- Bidirectional `encodeDeterministic` / `decodeDeterministic` verification
on all 8 ordering vectors in §4.2.1 order. -/
theorem rfc421CoreKeys_bidirectional :
    rfc421CoreKeys.map encodeDeterministic = rfc421CoreWires ∧
    rfc421CoreWires.map decodeDeterministic = rfc421CoreKeys.map some :=
  ⟨rfl, rfl⟩

/-- Bidirectional `encodeDeterministic` / `decodeDeterministic` verification
on all 8 ordering vectors in §4.2.3 order. -/
theorem rfc423LengthFirstKeys_bidirectional :
    rfc423LengthFirstKeys.map encodeDeterministic = rfc423LengthFirstWires ∧
    rfc423LengthFirstWires.map decodeDeterministic = rfc423LengthFirstKeys.map some :=
  ⟨rfl, rfl⟩

/-- Sorting the §4.2.3 list under `coreKeyOrder` recovers the exact §4.2.1 list. -/
theorem sortBy_core_from_lengthFirst :
    sortBy coreKeyOrder rfc423LengthFirstKeys = rfc421CoreKeys := rfl

/-- Sorting the §4.2.1 list under `lengthFirstKeyOrder` recovers the exact §4.2.3 list. -/
theorem sortBy_lengthFirst_from_core :
    sortBy lengthFirstKeyOrder rfc421CoreKeys = rfc423LengthFirstKeys := rfl

/-- Sorting either RFC list under `ctap2KeyOrder` yields `ctap2CanonicalKeys`
(swapping `[100]` and `[-1]` relative to §4.2.1 while keeping all 6 atomic
keys in the same order). -/
theorem sortBy_ctap2_from_core_and_lengthFirst :
    sortBy ctap2KeyOrder rfc421CoreKeys = ctap2CanonicalKeys ∧
    sortBy ctap2KeyOrder rfc423LengthFirstKeys = ctap2CanonicalKeys :=
  ⟨rfl, rfl⟩

/-- On the 6 atomic keys of the RFC 8-key set, core order and CTAP2 order
produce the exact same sorted list. -/
theorem sortBy_core_eq_ctap2_on_rfc_atomic_subset :
    let atomic6 := [ordKeyFalse, ordKeyAA, ordKeyZ, ordKeyNeg1, ordKey100, ordKey10]
    sortBy coreKeyOrder atomic6 = sortBy ctap2KeyOrder atomic6 ∧
    sortBy coreKeyOrder atomic6 =
      [ordKey10, ordKey100, ordKeyNeg1, ordKeyZ, ordKeyAA, ordKeyFalse] :=
  ⟨rfl, rfl⟩

/-- All three profile lists are pairwise distinct on the full 8-key set. -/
theorem ordering_profiles_pairwise_distinct :
    rfc421CoreKeys ≠ rfc423LengthFirstKeys ∧
    rfc421CoreKeys ≠ ctap2CanonicalKeys ∧
    rfc423LengthFirstKeys ≠ ctap2CanonicalKeys := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- Map normalisation (`Item.normalise`) reorders a map keyed in §4.2.3 order
into exact §4.2.1 core deterministic key order. -/
theorem normalise_map_lengthFirst_to_core :
    (Item.map (rfc423LengthFirstKeys.map fun k => (k, .uint 0))).normalise =
      Item.map (rfc421CoreKeys.map fun k => (k, .uint 0)) := rfl

end Cbor.Rfc8949.Vectors
