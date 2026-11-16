/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Float.DataModel
import Cbor.Rfc8949.Vectors.AppendixA

/-!
# RFC 8949 Appendix A: All 23 Floating-Point Conformance Vectors + Complete 81-Row Partition

RFC 8949 Appendix A contains **81** example rows (`1..81` in table order):
* **58 float-free rows** (`1..18`, `41..48`, `50..81`) — verified in Milestone 1
  (`Cbor.Rfc8949.Vectors.AppendixA`);
* **23 float-containing rows** (`19..40` and `49`) — verified bidirectionally in
  this module, following `Vectors/AppendixA.lean`'s exact pattern:
  - **17 preferred / core-deterministic rows** (`19..34` and `49`):
    11 `binary16` rows (`19..21, 23..24, 28..30, 32..34`),
    2 `binary32` rows (`25..26`), and
    4 `binary64` rows (`22, 27, 31` bare + row `49` tag-1 `1(1363896240.5)`);
  - **6 well-formed non-preferred rows** (`35..40`):
    `binary32` and `binary64` `Infinity`, `NaN`, and `-Infinity` — verified
    bidirectionally at the wire-grammar level (`parseFullRaw` / `FullRawItem.encode`),
    proved rejected by `decodeFullDeterministic`, `decodeFloatPreferred`, and
    `decodeFloatDeterministic`, and proved to narrow to Rows `32..34` (`0xf97c00`,
    `0xf97e00`, `0xf9fc00`) under `encodeFullPreferred` and `encodeFullDeterministic`.

Finally, `appendixA_complete_81_rows` proves that the 58 M1 float-free rows and
the 23 M2 float rows partition `{1..81}` cleanly (`58 + 23 = 81`, disjoint,
covering every `1 ≤ r ≤ 81`), and every one of the 81 rows round-trips through
the unified full CBOR parser/encoder.
-/

namespace Cbor.Rfc8949.Vectors

/-- One floating-point test vector from RFC 8949 Appendix A (`19..40` and `49`). -/
structure AppendixAFloatVector where
  /-- 1-based row number in RFC 8949 Appendix A (`1..81`). -/
  row : Nat
  /-- Diagnostic notation from RFC 8949 Appendix A. -/
  diagnostic : String
  /-- Exact wire bytes from RFC 8949 Appendix A. -/
  wire : List UInt8
  /-- Exact wire-level `FullRawItem` AST (preserving width of non-preferred rows `35..40`). -/
  rawItem : FullRawItem
  /-- Parsed `FullItem` AST. -/
  item : FullItem
  /-- Canonical §4.1 / §4.2.1 shortest-form wire encoding of `item`. -/
  preferredWire : List UInt8
  /-- Whether `wire` already uses §4.1 / §4.2.1 preferred shortest serialization. -/
  isPreferred : Bool
  deriving Repr

/-- Appendix A row 19: `0.0` (`f90000`). -/
def appendixARow19 : AppendixAFloatVector where
  row := 19
  diagnostic := "0.0"
  wire := [0xf9, 0x00, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x0000))
  item := .float (.half (Float16.ofBits 0x0000))
  preferredWire := [0xf9, 0x00, 0x00]
  isPreferred := true

/-- Appendix A row 20: `-0.0` (`f98000`). -/
def appendixARow20 : AppendixAFloatVector where
  row := 20
  diagnostic := "-0.0"
  wire := [0xf9, 0x80, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x8000))
  item := .float (.half (Float16.ofBits 0x8000))
  preferredWire := [0xf9, 0x80, 0x00]
  isPreferred := true

/-- Appendix A row 21: `1.0` (`f93c00`). -/
def appendixARow21 : AppendixAFloatVector where
  row := 21
  diagnostic := "1.0"
  wire := [0xf9, 0x3c, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x3c00))
  item := .float (.half (Float16.ofBits 0x3c00))
  preferredWire := [0xf9, 0x3c, 0x00]
  isPreferred := true

/-- Appendix A row 22: `1.1` (`fb3ff199999999999a`). -/
def appendixARow22 : AppendixAFloatVector where
  row := 22
  diagnostic := "1.1"
  wire := [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a]
  rawItem := .float (.double (Float64.ofBits 0x3ff199999999999a))
  item := .float (.double (Float64.ofBits 0x3ff199999999999a))
  preferredWire := [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a]
  isPreferred := true

/-- Appendix A row 23: `1.5` (`f93e00`). -/
def appendixARow23 : AppendixAFloatVector where
  row := 23
  diagnostic := "1.5"
  wire := [0xf9, 0x3e, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x3e00))
  item := .float (.half (Float16.ofBits 0x3e00))
  preferredWire := [0xf9, 0x3e, 0x00]
  isPreferred := true

/-- Appendix A row 24: `65504.0` (`f97bff`). -/
def appendixARow24 : AppendixAFloatVector where
  row := 24
  diagnostic := "65504.0"
  wire := [0xf9, 0x7b, 0xff]
  rawItem := .float (.half (Float16.ofBits 0x7bff))
  item := .float (.half (Float16.ofBits 0x7bff))
  preferredWire := [0xf9, 0x7b, 0xff]
  isPreferred := true

/-- Appendix A row 25: `100000.0` (`fa47c35000`). -/
def appendixARow25 : AppendixAFloatVector where
  row := 25
  diagnostic := "100000.0"
  wire := [0xfa, 0x47, 0xc3, 0x50, 0x00]
  rawItem := .float (.single (Float32.ofBits 0x47c35000))
  item := .float (.single (Float32.ofBits 0x47c35000))
  preferredWire := [0xfa, 0x47, 0xc3, 0x50, 0x00]
  isPreferred := true

/-- Appendix A row 26: `3.4028234663852886e+38` (`fa7f7fffff`). -/
def appendixARow26 : AppendixAFloatVector where
  row := 26
  diagnostic := "3.4028234663852886e+38"
  wire := [0xfa, 0x7f, 0x7f, 0xff, 0xff]
  rawItem := .float (.single (Float32.ofBits 0x7f7fffff))
  item := .float (.single (Float32.ofBits 0x7f7fffff))
  preferredWire := [0xfa, 0x7f, 0x7f, 0xff, 0xff]
  isPreferred := true

/-- Appendix A row 27: `1.0e+300` (`fb7e37e43c8800759c`). -/
def appendixARow27 : AppendixAFloatVector where
  row := 27
  diagnostic := "1.0e+300"
  wire := [0xfb, 0x7e, 0x37, 0xe4, 0x3c, 0x88, 0x00, 0x75, 0x9c]
  rawItem := .float (.double (Float64.ofBits 0x7e37e43c8800759c))
  item := .float (.double (Float64.ofBits 0x7e37e43c8800759c))
  preferredWire := [0xfb, 0x7e, 0x37, 0xe4, 0x3c, 0x88, 0x00, 0x75, 0x9c]
  isPreferred := true

/-- Appendix A row 28: `5.960464477539063e-8` (`f90001`, smallest positive `binary16` subnormal). -/
def appendixARow28 : AppendixAFloatVector where
  row := 28
  diagnostic := "5.960464477539063e-8"
  wire := [0xf9, 0x00, 0x01]
  rawItem := .float (.half (Float16.ofBits 0x0001))
  item := .float (.half (Float16.ofBits 0x0001))
  preferredWire := [0xf9, 0x00, 0x01]
  isPreferred := true

/-- Appendix A row 29: `0.00006103515625` (`f90400`, smallest positive `binary16` normal). -/
def appendixARow29 : AppendixAFloatVector where
  row := 29
  diagnostic := "0.00006103515625"
  wire := [0xf9, 0x04, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x0400))
  item := .float (.half (Float16.ofBits 0x0400))
  preferredWire := [0xf9, 0x04, 0x00]
  isPreferred := true

/-- Appendix A row 30: `-4.0` (`f9c400`). -/
def appendixARow30 : AppendixAFloatVector where
  row := 30
  diagnostic := "-4.0"
  wire := [0xf9, 0xc4, 0x00]
  rawItem := .float (.half (Float16.ofBits 0xc400))
  item := .float (.half (Float16.ofBits 0xc400))
  preferredWire := [0xf9, 0xc4, 0x00]
  isPreferred := true

/-- Appendix A row 31: `-4.1` (`fbc010666666666666`). -/
def appendixARow31 : AppendixAFloatVector where
  row := 31
  diagnostic := "-4.1"
  wire := [0xfb, 0xc0, 0x10, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66]
  rawItem := .float (.double (Float64.ofBits 0xc010666666666666))
  item := .float (.double (Float64.ofBits 0xc010666666666666))
  preferredWire := [0xfb, 0xc0, 0x10, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66]
  isPreferred := true

/-- Appendix A row 32: `Infinity` (`f97c00`). -/
def appendixARow32 : AppendixAFloatVector where
  row := 32
  diagnostic := "Infinity"
  wire := [0xf9, 0x7c, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x7c00))
  item := .float (.half (Float16.ofBits 0x7c00))
  preferredWire := [0xf9, 0x7c, 0x00]
  isPreferred := true

/-- Appendix A row 33: `NaN` (`f97e00`). -/
def appendixARow33 : AppendixAFloatVector where
  row := 33
  diagnostic := "NaN"
  wire := [0xf9, 0x7e, 0x00]
  rawItem := .float (.half (Float16.ofBits 0x7e00))
  item := .float (.half (Float16.ofBits 0x7e00))
  preferredWire := [0xf9, 0x7e, 0x00]
  isPreferred := true

/-- Appendix A row 34: `-Infinity` (`f9fc00`). -/
def appendixARow34 : AppendixAFloatVector where
  row := 34
  diagnostic := "-Infinity"
  wire := [0xf9, 0xfc, 0x00]
  rawItem := .float (.half (Float16.ofBits 0xfc00))
  item := .float (.half (Float16.ofBits 0xfc00))
  preferredWire := [0xf9, 0xfc, 0x00]
  isPreferred := true

/-- Appendix A row 35: `Infinity` (`fa7f800000`, non-preferred `binary32` `+∞`). -/
def appendixARow35 : AppendixAFloatVector where
  row := 35
  diagnostic := "Infinity"
  wire := [0xfa, 0x7f, 0x80, 0x00, 0x00]
  rawItem := .float (.single (Float32.ofBits 0x7f800000))
  item := .float (.single (Float32.ofBits 0x7f800000))
  preferredWire := [0xf9, 0x7c, 0x00]
  isPreferred := false

/-- Appendix A row 36: `NaN` (`fa7fc00000`, non-preferred `binary32` quiet NaN). -/
def appendixARow36 : AppendixAFloatVector where
  row := 36
  diagnostic := "NaN"
  wire := [0xfa, 0x7f, 0xc0, 0x00, 0x00]
  rawItem := .float (.single (Float32.ofBits 0x7fc00000))
  item := .float (.single (Float32.ofBits 0x7fc00000))
  preferredWire := [0xf9, 0x7e, 0x00]
  isPreferred := false

/-- Appendix A row 37: `-Infinity` (`faff800000`, non-preferred `binary32` `-∞`). -/
def appendixARow37 : AppendixAFloatVector where
  row := 37
  diagnostic := "-Infinity"
  wire := [0xfa, 0xff, 0x80, 0x00, 0x00]
  rawItem := .float (.single (Float32.ofBits 0xff800000))
  item := .float (.single (Float32.ofBits 0xff800000))
  preferredWire := [0xf9, 0xfc, 0x00]
  isPreferred := false

/-- Appendix A row 38: `Infinity` (`fb7ff0000000000000`, non-preferred `binary64` `+∞`). -/
def appendixARow38 : AppendixAFloatVector where
  row := 38
  diagnostic := "Infinity"
  wire := [0xfb, 0x7f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  rawItem := .float (.double (Float64.ofBits 0x7ff0000000000000))
  item := .float (.double (Float64.ofBits 0x7ff0000000000000))
  preferredWire := [0xf9, 0x7c, 0x00]
  isPreferred := false

/-- Appendix A row 39: `NaN` (`fb7ff8000000000000`, non-preferred `binary64` quiet NaN). -/
def appendixARow39 : AppendixAFloatVector where
  row := 39
  diagnostic := "NaN"
  wire := [0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  rawItem := .float (.double (Float64.ofBits 0x7ff8000000000000))
  item := .float (.double (Float64.ofBits 0x7ff8000000000000))
  preferredWire := [0xf9, 0x7e, 0x00]
  isPreferred := false

/-- Appendix A row 40: `-Infinity` (`fbfff0000000000000`, non-preferred `binary64` `-∞`). -/
def appendixARow40 : AppendixAFloatVector where
  row := 40
  diagnostic := "-Infinity"
  wire := [0xfb, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  rawItem := .float (.double (Float64.ofBits 0xfff0000000000000))
  item := .float (.double (Float64.ofBits 0xfff0000000000000))
  preferredWire := [0xf9, 0xfc, 0x00]
  isPreferred := false

/-- Appendix A row 49: `1(1363896240.5)` (`c1fb41d452d9ec200000`, tag 1 wrapping `binary64`). -/
def appendixARow49 : AppendixAFloatVector where
  row := 49
  diagnostic := "1(1363896240.5)"
  wire := [0xc1, 0xfb, 0x41, 0xd4, 0x52, 0xd9, 0xec, 0x20, 0x00, 0x00]
  rawItem := .tag .inline 1 (.float (.double (Float64.ofBits 0x41d452d9ec200000)))
  item := .tag 1 (.float (.double (Float64.ofBits 0x41d452d9ec200000)))
  preferredWire := [0xc1, 0xfb, 0x41, 0xd4, 0x52, 0xd9, 0xec, 0x20, 0x00, 0x00]
  isPreferred := true

/-- Complete list of all **23** float-containing RFC 8949 Appendix A vectors (`19..40` and `49`). -/
def appendixAFloatVectors : List AppendixAFloatVector :=
  [appendixARow19, appendixARow20, appendixARow21, appendixARow22, appendixARow23,
   appendixARow24, appendixARow25, appendixARow26, appendixARow27, appendixARow28,
   appendixARow29, appendixARow30, appendixARow31, appendixARow32, appendixARow33,
   appendixARow34, appendixARow35, appendixARow36, appendixARow37, appendixARow38,
   appendixARow39, appendixARow40, appendixARow49]

theorem appendixAFloatVectors_length : appendixAFloatVectors.length = 23 := rfl

theorem appendixAFloatVectors_preferred_count :
    (appendixAFloatVectors.filter AppendixAFloatVector.isPreferred).length = 17 := rfl

theorem appendixAFloatVectors_nonPreferred_count :
    (appendixAFloatVectors.filter (fun v => !v.isPreferred)).length = 6 := rfl

theorem appendixAFloatVectors_rows :
    appendixAFloatVectors.map AppendixAFloatVector.row =
      [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
       35, 36, 37, 38, 39, 40, 49] := rfl

/-! ## Per-row bidirectional kernel verification (all 23 float rows, zero `decide`) -/

/-- Bidirectional kernel specification for an Appendix A float row:
* exact wire-grammar round-trip (`parseFullRaw v.wire = some v.rawItem` and
  `v.rawItem.encode = v.wire`);
* well-formed item parse (`parseFullWellFormed v.wire = some v.item`);
* preferred and deterministic shortest-form serialization (`encodeFullPreferred`
  and `encodeFullDeterministic` both produce `v.preferredWire`);
* if `v.isPreferred`, `v.preferredWire = v.wire` and `decodeFullDeterministic v.wire = some v.item`;
* if `!v.isPreferred`, `decodeFullDeterministic v.wire = none`, `decodeFloatPreferred v.wire = none`,
  `decodeFloatDeterministic v.wire = none`, and `parseFullWellFormed v.preferredWire`
  yields an item `FullItem.Equiv` to `v.item`. -/
def FloatRowBidirectional (v : AppendixAFloatVector) : Prop :=
  parseFullRaw v.wire = some v.rawItem ∧
  v.rawItem.encode = v.wire ∧
  parseFullWellFormed v.wire = some v.item ∧
  encodeFullPreferred v.item = v.preferredWire ∧
  encodeFullDeterministic v.item = v.preferredWire ∧
  if v.isPreferred then
    v.preferredWire = v.wire ∧
    decodeFullDeterministic v.wire = some v.item
  else
    decodeFullDeterministic v.wire = none ∧
    decodeFloatPreferred v.wire = none ∧
    decodeFloatDeterministic v.wire = none ∧
    ∃ y, parseFullWellFormed v.preferredWire = some y ∧ FullItem.Equiv v.item y

theorem appendixARow19_bidirectional : FloatRowBidirectional appendixARow19 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow20_bidirectional : FloatRowBidirectional appendixARow20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow21_bidirectional : FloatRowBidirectional appendixARow21 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow22_bidirectional : FloatRowBidirectional appendixARow22 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow23_bidirectional : FloatRowBidirectional appendixARow23 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow24_bidirectional : FloatRowBidirectional appendixARow24 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow25_bidirectional : FloatRowBidirectional appendixARow25 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow26_bidirectional : FloatRowBidirectional appendixARow26 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow27_bidirectional : FloatRowBidirectional appendixARow27 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow28_bidirectional : FloatRowBidirectional appendixARow28 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow29_bidirectional : FloatRowBidirectional appendixARow29 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow30_bidirectional : FloatRowBidirectional appendixARow30 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow31_bidirectional : FloatRowBidirectional appendixARow31 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow32_bidirectional : FloatRowBidirectional appendixARow32 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow33_bidirectional : FloatRowBidirectional appendixARow33 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow34_bidirectional : FloatRowBidirectional appendixARow34 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem appendixARow35_bidirectional : FloatRowBidirectional appendixARow35 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow32.item, rfl, rfl⟩⟩

theorem appendixARow36_bidirectional : FloatRowBidirectional appendixARow36 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow33.item, rfl, rfl⟩⟩

theorem appendixARow37_bidirectional : FloatRowBidirectional appendixARow37 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow34.item, rfl, rfl⟩⟩

theorem appendixARow38_bidirectional : FloatRowBidirectional appendixARow38 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow32.item, rfl, rfl⟩⟩

theorem appendixARow39_bidirectional : FloatRowBidirectional appendixARow39 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow33.item, rfl, rfl⟩⟩

theorem appendixARow40_bidirectional : FloatRowBidirectional appendixARow40 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨appendixARow34.item, rfl, rfl⟩⟩

theorem appendixARow49_bidirectional : FloatRowBidirectional appendixARow49 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Universal Appendix A float theorem:** all **23** float-containing RFC 8949
Appendix A rows (`19..40` and `49`) satisfy `FloatRowBidirectional`. -/
theorem appendixAFloat_all_bidirectional :
    ∀ v ∈ appendixAFloatVectors, FloatRowBidirectional v := by
  intro v hv
  simp only [appendixAFloatVectors, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact appendixARow19_bidirectional
  · exact appendixARow20_bidirectional
  · exact appendixARow21_bidirectional
  · exact appendixARow22_bidirectional
  · exact appendixARow23_bidirectional
  · exact appendixARow24_bidirectional
  · exact appendixARow25_bidirectional
  · exact appendixARow26_bidirectional
  · exact appendixARow27_bidirectional
  · exact appendixARow28_bidirectional
  · exact appendixARow29_bidirectional
  · exact appendixARow30_bidirectional
  · exact appendixARow31_bidirectional
  · exact appendixARow32_bidirectional
  · exact appendixARow33_bidirectional
  · exact appendixARow34_bidirectional
  · exact appendixARow35_bidirectional
  · exact appendixARow36_bidirectional
  · exact appendixARow37_bidirectional
  · exact appendixARow38_bidirectional
  · exact appendixARow39_bidirectional
  · exact appendixARow40_bidirectional
  · exact appendixARow49_bidirectional

/-! ## Complete 81-Row RFC 8949 Appendix A Partition (`58 + 23 = 81`) -/

private def noDupNat : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && noDupNat xs

private theorem noDupNat_sound : ∀ {l : List Nat}, noDupNat l = true → l.Nodup
  | [], _ => .nil
  | x :: xs, h => by
    simp only [noDupNat, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hnot : ∀ y ∈ xs, x ≠ y := fun y hy hxy => by
      have : xs.contains x = true := List.contains_iff_mem.mpr (hxy ▸ hy)
      rw [h.1] at this; cases this
    exact List.Pairwise.cons hnot (noDupNat_sound h.2)

theorem appendixAFloatVectors_rows_nodup :
    (appendixAFloatVectors.map AppendixAFloatVector.row).Nodup :=
  noDupNat_sound (l := appendixAFloatVectors.map AppendixAFloatVector.row) rfl

private theorem all81_noDup_and_cover :
    let ff := appendixAFloatFreeVectors.map AppendixAVector.row
    let fl := appendixAFloatVectors.map AppendixAFloatVector.row
    noDupNat (ff ++ fl) = true ∧
    ((List.range 81).map (· + 1)).all (fun r => (ff ++ fl).contains r) = true :=
  ⟨rfl, rfl⟩

/-- **Complete 81-row RFC 8949 Appendix A partition and unified round-trip:**
* `58` float-free rows + `23` float rows = `81` distinct rows;
* every row index `1 ≤ r ≤ 81` belongs to either `appendixAFloatFreeVectors`
  or `appendixAFloatVectors` (and never both);
* every one of the 58 float-free rows AND every one of the 23 float rows
  round-trips bidirectionally through `parseFullRaw` / `FullRawItem.encode`. -/
theorem appendixA_complete_81_rows :
    let ff := appendixAFloatFreeVectors.map AppendixAVector.row
    let fl := appendixAFloatVectors.map AppendixAFloatVector.row
    appendixAFloatFreeVectors.length = 58 ∧
    appendixAFloatVectors.length = 23 ∧
    (ff ++ fl).length = 81 ∧
    (ff ++ fl).Nodup ∧
    (∀ r, 1 ≤ r ∧ r ≤ 81 → r ∈ ff ∨ r ∈ fl) ∧
    (∀ v ∈ appendixAFloatFreeVectors,
      ∃ r : FullRawItem, parseFullRaw v.wire = some r ∧ r.encode = v.wire) ∧
    (∀ v ∈ appendixAFloatVectors,
      parseFullRaw v.wire = some v.rawItem ∧ v.rawItem.encode = v.wire) := by
  refine ⟨rfl, rfl, rfl, noDupNat_sound all81_noDup_and_cover.1, ?_, ?_, ?_⟩
  · intro r ⟨hr1, hr81⟩
    have hmem : r ∈ (List.range 81).map (· + 1) := by
      rw [List.mem_map]
      exact ⟨r - 1, List.mem_range.mpr (by omega), by omega⟩
    have hcont : ((appendixAFloatFreeVectors.map AppendixAVector.row ++
        appendixAFloatVectors.map AppendixAFloatVector.row).contains r) = true :=
      (List.all_eq_true.mp all81_noDup_and_cover.2) r hmem
    exact List.mem_append.mp (List.contains_iff_mem.mp hcont)
  · intro v hv
    have hb := (appendixAFloatFree_all_bidirectional v hv).1
    obtain ⟨r, hwf, henc, _⟩ := parseWellFormed_eq_some_iff.mp hb
    have hpr : parseRaw v.wire = some r := parseRaw_eq_some_iff.mpr ⟨hwf, henc⟩
    exact ⟨FullRawItem.ofRawItem r, parseFullRaw_of_parseRaw hpr,
      (FullRawItem.encode_ofRawItem r).trans henc⟩
  · intro v hv
    have hb := appendixAFloat_all_bidirectional v hv
    exact ⟨hb.1, hb.2.1⟩

end Cbor.Rfc8949.Vectors
