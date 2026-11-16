/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Head

/-!
# RFC 8949 §3.3 & Appendix D: Bit-Level IEEE 754 Binary Floating-Point Formats

Lean 4 core exposes `Float` as an opaque runtime type with no kernel bit-level
specification. Per Milestone 2 scope (FE #126 §2.1), this module defines the
three IEEE 754 binary interchange formats carried by CBOR major type 7
(RFC 8949 §3.3, Table 3; Appendix D) explicitly at the bit level:

* `Float16` (`binary16`, half-precision, 16 bits): additional information `25`
  (initial byte `0xf9` + 2 big-endian payload bytes; 1-bit sign, 5-bit biased
  exponent with bias `15`, 10-bit trailing significand);
* `Float32` (`binary32`, single-precision, 32 bits): additional information `26`
  (initial byte `0xfa` + 4 big-endian payload bytes; 1-bit sign, 8-bit biased
  exponent with bias `127`, 23-bit trailing significand);
* `Float64` (`binary64`, double-precision, 64 bits): additional information `27`
  (initial byte `0xfb` + 8 big-endian payload bytes; 1-bit sign, 11-bit biased
  exponent with bias `1023`, 52-bit trailing significand).

We prove:
1. Exact bit-packing / unpacking bijections (`toBits` / `ofBits`) for all three
   widths (`< 2^16`, `< 2^32`, `< 2^64`);
2. In-kernel wire encode/decode round-trip, soundness/completeness, injectivity,
   and self-delimiting prefix uniqueness for `Float16`, `Float32`, `Float64`,
   and the sum type `CborFloat`;
3. IEEE 754 value-class partitions (signed zero, subnormal, normal, ±infinity,
   quiet vs. signaling NaN);
4. Exact symbolic IEEE 754 valuation `IEEEValue` (scaled by `2^1074` so every
   finite nonzero value across all three widths has an exact `Nat` numerator
   with zero rounding or division), `Float64.toIEEEValue_injective`, and exact
   correspondence with RFC 8949 Appendix D's half-precision decoder layout.
-/

namespace Cbor.Rfc8949

/-! ## Width metadata (§3.3, Table 3) -/

/-- IEEE 754 floating-point widths carried by CBOR major type 7 (§3.3). -/
inductive FloatWidth where
  | f16
  | f32
  | f64
  deriving DecidableEq, Repr, Inhabited

namespace FloatWidth

/-- 5-bit additional-information code in major type 7 (§3.3 Table 3). -/
def ai : FloatWidth → Nat
  | f16 => 25
  | f32 => 26
  | f64 => 27

/-- Initial head byte `0b111_xxxxx = 7 * 32 + ai` (`0xf9`, `0xfa`, `0xfb`). -/
def initialByte : FloatWidth → UInt8
  | f16 => 0xf9
  | f32 => 0xfa
  | f64 => 0xfb

/-- Number of big-endian IEEE 754 payload bytes following the initial byte. -/
def payloadBytes : FloatWidth → Nat
  | f16 => 2
  | f32 => 4
  | f64 => 8

/-- Total CBOR wire length (`1 + payloadBytes`: 3, 5, or 9 bytes). -/
def wireLength (w : FloatWidth) : Nat := 1 + w.payloadBytes

theorem initialByte_eq_major7 (w : FloatWidth) :
    w.initialByte = UInt8.ofNat (7 * 32 + w.ai) := by
  cases w <;> rfl

end FloatWidth

/-! ## Explicit bit-level IEEE 754 structures -/

/-- IEEE 754 `binary16` (half-precision, 16-bit) floating-point bit layout
(RFC 8949 §3.3, Appendix D):
bit 15 = `sign`, bits 14..10 = `exp` (`< 32`, bias 15), bits 9..0 = `mant` (`< 1024`). -/
structure Float16 where
  sign : Bool
  exp : Nat
  mant : Nat
  hexp : exp < 32
  hmant : mant < 1024
  deriving DecidableEq, Repr

/-- IEEE 754 `binary32` (single-precision, 32-bit) floating-point bit layout
(RFC 8949 §3.3):
bit 31 = `sign`, bits 30..23 = `exp` (`< 256`, bias 127), bits 22..0 = `mant` (`< 2^23`). -/
structure Float32 where
  sign : Bool
  exp : Nat
  mant : Nat
  hexp : exp < 256
  hmant : mant < 8388608
  deriving DecidableEq, Repr

/-- IEEE 754 `binary64` (double-precision, 64-bit) floating-point bit layout
(RFC 8949 §3.3):
bit 63 = `sign`, bits 62..52 = `exp` (`< 2048`, bias 1023), bits 51..0 = `mant` (`< 2^52`). -/
structure Float64 where
  sign : Bool
  exp : Nat
  mant : Nat
  hexp : exp < 2048
  hmant : mant < 4503599627370496
  deriving DecidableEq, Repr

instance : Inhabited Float16 := ⟨⟨false, 0, 0, by omega, by omega⟩⟩
instance : Inhabited Float32 := ⟨⟨false, 0, 0, by omega, by omega⟩⟩
instance : Inhabited Float64 := ⟨⟨false, 0, 0, by omega, by omega⟩⟩

theorem Float16.ext {a b : Float16}
    (hs : a.sign = b.sign) (he : a.exp = b.exp) (hm : a.mant = b.mant) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact ⟨hs, he, hm⟩

theorem Float32.ext {a b : Float32}
    (hs : a.sign = b.sign) (he : a.exp = b.exp) (hm : a.mant = b.mant) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact ⟨hs, he, hm⟩

theorem Float64.ext {a b : Float64}
    (hs : a.sign = b.sign) (he : a.exp = b.exp) (hm : a.mant = b.mant) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact ⟨hs, he, hm⟩

/-- A CBOR floating-point item carrying its explicit serialization width (§3.3). -/
inductive CborFloat where
  | half (v : Float16)
  | single (v : Float32)
  | double (v : Float64)
  deriving DecidableEq, Repr, Inhabited

namespace CborFloat

/-- The serialization width of a `CborFloat`. -/
def width : CborFloat → FloatWidth
  | .half _ => .f16
  | .single _ => .f32
  | .double _ => .f64

end CborFloat

/-! ## Bit-packing and unpacking bijections (`< 2^16`, `< 2^32`, `< 2^64`) -/

namespace Float16

/-- Pack `Float16` fields into a 16-bit unsigned integer (`0 .. 65535`). -/
def toBits (f : Float16) : Nat :=
  (if f.sign then 32768 else 0) + f.exp * 1024 + f.mant

/-- Unpack the low 16 bits of `n` into `Float16` (`sign | exp | mant`). -/
def ofBits (n : Nat) : Float16 :=
  let w := n % 65536
  { sign := (w / 32768 == 1)
    exp := (w / 1024) % 32
    mant := w % 1024
    hexp := by omega
    hmant := by omega }

theorem toBits_lt (f : Float16) : f.toBits < 65536 := by
  have he := f.hexp
  have hm := f.hmant
  unfold toBits
  cases f.sign <;> simp <;> omega

theorem ofBits_toBits (f : Float16) : ofBits f.toBits = f := by
  have he := f.hexp
  have hm := f.hmant
  apply Float16.ext
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega

theorem toBits_ofBits (n : Nat) : (ofBits n).toBits = n % 65536 := by
  unfold ofBits toBits
  by_cases h : (n % 65536) / 32768 = 1
  · have hb : ((n % 65536 / 32768 == 1) = true) := beq_iff_eq.mpr h
    simp only [hb, ↓reduceIte]
    omega
  · have hb : ((n % 65536 / 32768 == 1) = false) := beq_false_of_ne h
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    omega

theorem toBits_ofBits_of_lt {n : Nat} (h : n < 65536) : (ofBits n).toBits = n := by
  rw [toBits_ofBits, Nat.mod_eq_of_lt h]

theorem toBits_injective : Function.Injective toBits := fun a b h => by
  have := congrArg ofBits h
  simpa [ofBits_toBits] using this

end Float16

namespace Float32

/-- Pack `Float32` fields into a 32-bit unsigned integer (`0 .. 2^32 - 1`). -/
def toBits (f : Float32) : Nat :=
  (if f.sign then 2147483648 else 0) + f.exp * 8388608 + f.mant

/-- Unpack the low 32 bits of `n` into `Float32` (`sign | exp | mant`). -/
def ofBits (n : Nat) : Float32 :=
  let w := n % 4294967296
  { sign := (w / 2147483648 == 1)
    exp := (w / 8388608) % 256
    mant := w % 8388608
    hexp := by omega
    hmant := by omega }

theorem toBits_lt (f : Float32) : f.toBits < 4294967296 := by
  have he := f.hexp
  have hm := f.hmant
  unfold toBits
  cases f.sign <;> simp <;> omega

theorem ofBits_toBits (f : Float32) : ofBits f.toBits = f := by
  have he := f.hexp
  have hm := f.hmant
  apply Float32.ext
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega

theorem toBits_ofBits (n : Nat) : (ofBits n).toBits = n % 4294967296 := by
  unfold ofBits toBits
  by_cases h : (n % 4294967296) / 2147483648 = 1
  · have hb : ((n % 4294967296 / 2147483648 == 1) = true) := beq_iff_eq.mpr h
    simp only [hb, ↓reduceIte]
    omega
  · have hb : ((n % 4294967296 / 2147483648 == 1) = false) := beq_false_of_ne h
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    omega

theorem toBits_ofBits_of_lt {n : Nat} (h : n < 4294967296) : (ofBits n).toBits = n := by
  rw [toBits_ofBits, Nat.mod_eq_of_lt h]

theorem toBits_injective : Function.Injective toBits := fun a b h => by
  have := congrArg ofBits h
  simpa [ofBits_toBits] using this

end Float32

namespace Float64

/-- Pack `Float64` fields into a 64-bit unsigned integer (`0 .. 2^64 - 1`). -/
def toBits (f : Float64) : Nat :=
  (if f.sign then 9223372036854775808 else 0) + f.exp * 4503599627370496 + f.mant

/-- Unpack the low 64 bits of `n` into `Float64` (`sign | exp | mant`). -/
def ofBits (n : Nat) : Float64 :=
  let w := n % 18446744073709551616
  { sign := (w / 9223372036854775808 == 1)
    exp := (w / 4503599627370496) % 2048
    mant := w % 4503599627370496
    hexp := by omega
    hmant := by omega }

theorem toBits_lt (f : Float64) : f.toBits < 18446744073709551616 := by
  have he := f.hexp
  have hm := f.hmant
  unfold toBits
  cases f.sign <;> simp <;> omega

theorem ofBits_toBits (f : Float64) : ofBits f.toBits = f := by
  have he := f.hexp
  have hm := f.hmant
  apply Float64.ext
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega
  · unfold ofBits toBits
    cases f.sign <;> simp <;> omega

theorem toBits_ofBits (n : Nat) : (ofBits n).toBits = n % 18446744073709551616 := by
  unfold ofBits toBits
  by_cases h : (n % 18446744073709551616) / 9223372036854775808 = 1
  · have hb : ((n % 18446744073709551616 / 9223372036854775808 == 1) = true) := beq_iff_eq.mpr h
    simp only [hb, ↓reduceIte]
    omega
  · have hb : ((n % 18446744073709551616 / 9223372036854775808 == 1) = false) := beq_false_of_ne h
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    omega

theorem toBits_ofBits_of_lt {n : Nat} (h : n < 18446744073709551616) :
    (ofBits n).toBits = n := by
  rw [toBits_ofBits, Nat.mod_eq_of_lt h]

theorem toBits_injective : Function.Injective toBits := fun a b h => by
  have := congrArg ofBits h
  simpa [ofBits_toBits] using this

end Float64

/-! ## Wire encoding, decoding, and round-trip theorems (§3.3) -/

/-- Encode a `Float16` as CBOR major type 7, AI 25 (`0xf9` + 2 big-endian bytes). -/
def encodeFloat16 (f : Float16) : List UInt8 :=
  0xf9 :: beBytes 2 f.toBits

/-- Encode a `Float32` as CBOR major type 7, AI 26 (`0xfa` + 4 big-endian bytes). -/
def encodeFloat32 (f : Float32) : List UInt8 :=
  0xfa :: beBytes 4 f.toBits

/-- Encode a `Float64` as CBOR major type 7, AI 27 (`0xfb` + 8 big-endian bytes). -/
def encodeFloat64 (f : Float64) : List UInt8 :=
  0xfb :: beBytes 8 f.toBits

/-- Encode any `CborFloat` in its carried width (`0xf9` / `0xfa` / `0xfb`). -/
def encodeFloat : CborFloat → List UInt8
  | .half f => encodeFloat16 f
  | .single f => encodeFloat32 f
  | .double f => encodeFloat64 f

/-- Decode a `Float16` prefix (`0xf9` followed by 2 payload bytes). -/
def decodeFloat16Prefix : List UInt8 → Option (Float16 × List UInt8)
  | b :: rest =>
    if b = 0xf9 then
      match readArg 2 rest with
      | some (n, rest') => some (Float16.ofBits n, rest')
      | none => none
    else none
  | [] => none

/-- Decode a `Float32` prefix (`0xfa` followed by 4 payload bytes). -/
def decodeFloat32Prefix : List UInt8 → Option (Float32 × List UInt8)
  | b :: rest =>
    if b = 0xfa then
      match readArg 4 rest with
      | some (n, rest') => some (Float32.ofBits n, rest')
      | none => none
    else none
  | [] => none

/-- Decode a `Float64` prefix (`0xfb` followed by 8 payload bytes). -/
def decodeFloat64Prefix : List UInt8 → Option (Float64 × List UInt8)
  | b :: rest =>
    if b = 0xfb then
      match readArg 8 rest with
      | some (n, rest') => some (Float64.ofBits n, rest')
      | none => none
    else none
  | [] => none

/-- Decode one CBOR floating-point item from the front of `bs` (§3.3). -/
def decodeFloatPrefix : List UInt8 → Option (CborFloat × List UInt8)
  | b :: rest =>
    if b = 0xf9 then
      match readArg 2 rest with
      | some (n, rest') => some (.half (Float16.ofBits n), rest')
      | none => none
    else if b = 0xfa then
      match readArg 4 rest with
      | some (n, rest') => some (.single (Float32.ofBits n), rest')
      | none => none
    else if b = 0xfb then
      match readArg 8 rest with
      | some (n, rest') => some (.double (Float64.ofBits n), rest')
      | none => none
    else none
  | [] => none

/-- Exact whole-buffer `Float16` decoder (requires no trailing bytes). -/
def decodeFloat16 (bs : List UInt8) : Option Float16 :=
  match decodeFloat16Prefix bs with
  | some (f, []) => some f
  | _ => none

/-- Exact whole-buffer `Float32` decoder (requires no trailing bytes). -/
def decodeFloat32 (bs : List UInt8) : Option Float32 :=
  match decodeFloat32Prefix bs with
  | some (f, []) => some f
  | _ => none

/-- Exact whole-buffer `Float64` decoder (requires no trailing bytes). -/
def decodeFloat64 (bs : List UInt8) : Option Float64 :=
  match decodeFloat64Prefix bs with
  | some (f, []) => some f
  | _ => none

/-- Exact whole-buffer `CborFloat` decoder (requires no trailing bytes). -/
def decodeFloat (bs : List UInt8) : Option CborFloat :=
  match decodeFloatPrefix bs with
  | some (f, []) => some f
  | _ => none

theorem encodeFloat16_length (f : Float16) : (encodeFloat16 f).length = 3 := by
  simp [encodeFloat16, beBytes_length]

theorem encodeFloat32_length (f : Float32) : (encodeFloat32 f).length = 5 := by
  simp [encodeFloat32, beBytes_length]

theorem encodeFloat64_length (f : Float64) : (encodeFloat64 f).length = 9 := by
  simp [encodeFloat64, beBytes_length]

theorem encodeFloat_length (f : CborFloat) : (encodeFloat f).length = f.width.wireLength := by
  cases f <;> simp [encodeFloat, CborFloat.width, FloatWidth.wireLength, FloatWidth.payloadBytes,
    encodeFloat16_length, encodeFloat32_length, encodeFloat64_length]

theorem decodeFloat16Prefix_encode (f : Float16) (rest : List UInt8) :
    decodeFloat16Prefix (encodeFloat16 f ++ rest) = some (f, rest) := by
  have hlt : f.toBits < 256 ^ 2 := f.toBits_lt
  simp [encodeFloat16, decodeFloat16Prefix, readArg_beBytes hlt, Float16.ofBits_toBits]

theorem decodeFloat32Prefix_encode (f : Float32) (rest : List UInt8) :
    decodeFloat32Prefix (encodeFloat32 f ++ rest) = some (f, rest) := by
  have hlt : f.toBits < 256 ^ 4 := f.toBits_lt
  simp [encodeFloat32, decodeFloat32Prefix, readArg_beBytes hlt, Float32.ofBits_toBits]

theorem decodeFloat64Prefix_encode (f : Float64) (rest : List UInt8) :
    decodeFloat64Prefix (encodeFloat64 f ++ rest) = some (f, rest) := by
  have hlt : f.toBits < 256 ^ 8 := f.toBits_lt
  simp [encodeFloat64, decodeFloat64Prefix, readArg_beBytes hlt, Float64.ofBits_toBits]

theorem decodeFloat16Prefix_sound {bs rest : List UInt8} {f : Float16}
    (h : decodeFloat16Prefix bs = some (f, rest)) : bs = encodeFloat16 f ++ rest := by
  match bs with
  | [] => simp [decodeFloat16Prefix] at h
  | b :: tl =>
    simp only [decodeFloat16Prefix] at h
    split at h
    · rename_i hb
      subst hb
      split at h
      · rename_i n rest' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, htl⟩ := readArg_sound hr
        have hbits : (Float16.ofBits n).toBits = n := Float16.toBits_ofBits_of_lt hn
        simp [encodeFloat16, hbits, htl]
      · simp at h
    · simp at h

theorem decodeFloat32Prefix_sound {bs rest : List UInt8} {f : Float32}
    (h : decodeFloat32Prefix bs = some (f, rest)) : bs = encodeFloat32 f ++ rest := by
  match bs with
  | [] => simp [decodeFloat32Prefix] at h
  | b :: tl =>
    simp only [decodeFloat32Prefix] at h
    split at h
    · rename_i hb
      subst hb
      split at h
      · rename_i n rest' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, htl⟩ := readArg_sound hr
        have hbits : (Float32.ofBits n).toBits = n := Float32.toBits_ofBits_of_lt hn
        simp [encodeFloat32, hbits, htl]
      · simp at h
    · simp at h

theorem decodeFloat64Prefix_sound {bs rest : List UInt8} {f : Float64}
    (h : decodeFloat64Prefix bs = some (f, rest)) : bs = encodeFloat64 f ++ rest := by
  match bs with
  | [] => simp [decodeFloat64Prefix] at h
  | b :: tl =>
    simp only [decodeFloat64Prefix] at h
    split at h
    · rename_i hb
      subst hb
      split at h
      · rename_i n rest' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, htl⟩ := readArg_sound hr
        have hbits : (Float64.ofBits n).toBits = n := Float64.toBits_ofBits_of_lt hn
        simp [encodeFloat64, hbits, htl]
      · simp at h
    · simp at h

/-- **Binary16 (`0xf9`) round-trip:** every 16-bit IEEE 754 float encodes to 3 bytes
and decodes back to itself. -/
theorem decodeFloat16_encodeFloat16 (f : Float16) :
    decodeFloat16 (encodeFloat16 f) = some f := by
  have h := decodeFloat16Prefix_encode f []
  simp only [List.append_nil] at h
  simp [decodeFloat16, h]

theorem decodeFloat16_eq_some_iff {bs : List UInt8} {f : Float16} :
    decodeFloat16 bs = some f ↔ bs = encodeFloat16 f := by
  constructor
  · intro h
    unfold decodeFloat16 at h
    cases hp : decodeFloat16Prefix bs with
    | none => simp [hp] at h
    | some pr =>
      obtain ⟨g, rest⟩ := pr
      cases rest with
      | nil =>
        simp only [hp, Option.some.injEq] at h
        subst h
        simpa using decodeFloat16Prefix_sound hp
      | cons _ _ => simp [hp] at h
  · rintro rfl
    exact decodeFloat16_encodeFloat16 f

/-- **Binary32 (`0xfa`) round-trip:** every 32-bit IEEE 754 float encodes to 5 bytes
and decodes back to itself. -/
theorem decodeFloat32_encodeFloat32 (f : Float32) :
    decodeFloat32 (encodeFloat32 f) = some f := by
  have h := decodeFloat32Prefix_encode f []
  simp only [List.append_nil] at h
  simp [decodeFloat32, h]

theorem decodeFloat32_eq_some_iff {bs : List UInt8} {f : Float32} :
    decodeFloat32 bs = some f ↔ bs = encodeFloat32 f := by
  constructor
  · intro h
    unfold decodeFloat32 at h
    cases hp : decodeFloat32Prefix bs with
    | none => simp [hp] at h
    | some pr =>
      obtain ⟨g, rest⟩ := pr
      cases rest with
      | nil =>
        simp only [hp, Option.some.injEq] at h
        subst h
        simpa using decodeFloat32Prefix_sound hp
      | cons _ _ => simp [hp] at h
  · rintro rfl
    exact decodeFloat32_encodeFloat32 f

/-- **Binary64 (`0xfb`) round-trip:** every 64-bit IEEE 754 float encodes to 9 bytes
and decodes back to itself. -/
theorem decodeFloat64_encodeFloat64 (f : Float64) :
    decodeFloat64 (encodeFloat64 f) = some f := by
  have h := decodeFloat64Prefix_encode f []
  simp only [List.append_nil] at h
  simp [decodeFloat64, h]

theorem decodeFloat64_eq_some_iff {bs : List UInt8} {f : Float64} :
    decodeFloat64 bs = some f ↔ bs = encodeFloat64 f := by
  constructor
  · intro h
    unfold decodeFloat64 at h
    cases hp : decodeFloat64Prefix bs with
    | none => simp [hp] at h
    | some pr =>
      obtain ⟨g, rest⟩ := pr
      cases rest with
      | nil =>
        simp only [hp, Option.some.injEq] at h
        subst h
        simpa using decodeFloat64Prefix_sound hp
      | cons _ _ => simp [hp] at h
  · rintro rfl
    exact decodeFloat64_encodeFloat64 f

theorem decodeFloatPrefix_encodeFloat (f : CborFloat) (rest : List UInt8) :
    decodeFloatPrefix (encodeFloat f ++ rest) = some (f, rest) := by
  cases f with
  | half v =>
    have hlt : v.toBits < 256 ^ 2 := v.toBits_lt
    simp [encodeFloat, encodeFloat16, decodeFloatPrefix, readArg_beBytes hlt, Float16.ofBits_toBits]
  | single v =>
    have hlt : v.toBits < 256 ^ 4 := v.toBits_lt
    have hne : (0xfa : UInt8) ≠ 0xf9 := by intro h; cases h
    simp [encodeFloat, encodeFloat32, decodeFloatPrefix, hne,
      readArg_beBytes hlt, Float32.ofBits_toBits]
  | double v =>
    have hlt : v.toBits < 256 ^ 8 := v.toBits_lt
    have hne1 : (0xfb : UInt8) ≠ 0xf9 := by intro h; cases h
    have hne2 : (0xfb : UInt8) ≠ 0xfa := by intro h; cases h
    simp [encodeFloat, encodeFloat64, decodeFloatPrefix, hne1, hne2,
      readArg_beBytes hlt, Float64.ofBits_toBits]

theorem decodeFloatPrefix_sound {bs rest : List UInt8} {f : CborFloat}
    (h : decodeFloatPrefix bs = some (f, rest)) : bs = encodeFloat f ++ rest := by
  match bs with
  | [] => simp [decodeFloatPrefix] at h
  | b :: tl =>
    simp only [decodeFloatPrefix] at h
    split at h
    · rename_i hb
      subst hb
      split at h
      · rename_i n rest' hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hn, htl⟩ := readArg_sound hr
        simp [encodeFloat, encodeFloat16, Float16.toBits_ofBits_of_lt hn, htl]
      · simp at h
    · split at h
      · rename_i _ hb
        subst hb
        split at h
        · rename_i n rest' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hn, htl⟩ := readArg_sound hr
          simp [encodeFloat, encodeFloat32, Float32.toBits_ofBits_of_lt hn, htl]
        · simp at h
      · split at h
        · rename_i _ _ hb
          subst hb
          split at h
          · rename_i n rest' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hn, htl⟩ := readArg_sound hr
            simp [encodeFloat, encodeFloat64, Float64.toBits_ofBits_of_lt hn, htl]
          · simp at h
        · simp at h

theorem decodeFloatPrefix_eq_some_iff {bs rest : List UInt8} {f : CborFloat} :
    decodeFloatPrefix bs = some (f, rest) ↔ bs = encodeFloat f ++ rest :=
  ⟨decodeFloatPrefix_sound, fun h => h ▸ decodeFloatPrefix_encodeFloat f rest⟩

/-- **Unified `CborFloat` round-trip** across all three widths (`0xf9`, `0xfa`, `0xfb`). -/
theorem decodeFloat_encodeFloat (f : CborFloat) :
    decodeFloat (encodeFloat f) = some f := by
  have h := decodeFloatPrefix_encodeFloat f []
  simp only [List.append_nil] at h
  simp [decodeFloat, h]

theorem decodeFloat_eq_some_iff {bs : List UInt8} {f : CborFloat} :
    decodeFloat bs = some f ↔ bs = encodeFloat f := by
  constructor
  · intro h
    unfold decodeFloat at h
    cases hp : decodeFloatPrefix bs with
    | none => simp [hp] at h
    | some pr =>
      obtain ⟨g, rest⟩ := pr
      cases rest with
      | nil =>
        simp only [hp, Option.some.injEq] at h
        subst h
        simpa using decodeFloatPrefix_sound hp
      | cons _ _ => simp [hp] at h
  · rintro rfl
    exact decodeFloat_encodeFloat f

/-- **Self-delimiting prefix uniqueness** for CBOR float encodings. -/
theorem encodeFloat_prefix_unique {f₁ f₂ : CborFloat} {r₁ r₂ : List UInt8}
    (h : encodeFloat f₁ ++ r₁ = encodeFloat f₂ ++ r₂) : f₁ = f₂ ∧ r₁ = r₂ := by
  have h₁ := decodeFloatPrefix_encodeFloat f₁ r₁
  rw [h, decodeFloatPrefix_encodeFloat] at h₁
  simp only [Option.some.injEq, Prod.mk.injEq] at h₁
  exact ⟨h₁.1.symm, h₁.2.symm⟩

theorem encodeFloat_injective : Function.Injective encodeFloat := fun f₁ f₂ h =>
  (encodeFloat_prefix_unique (r₁ := []) (r₂ := []) (by simpa using h)).1

/-- Truncated float heads are rejected whenever fewer than 2/4/8 payload bytes follow. -/
theorem decodeFloatPrefix_truncated_f16 {rest : List UInt8} (h : rest.length < 2) :
    decodeFloatPrefix (0xf9 :: rest) = none := by
  have hnot : ¬ (2 ≤ rest.length) := by omega
  simp [decodeFloatPrefix, readArg, hnot]

theorem decodeFloatPrefix_truncated_f32 {rest : List UInt8} (h : rest.length < 4) :
    decodeFloatPrefix (0xfa :: rest) = none := by
  have hne : (0xfa : UInt8) ≠ 0xf9 := by intro e; cases e
  have hnot : ¬ (4 ≤ rest.length) := by omega
  simp [decodeFloatPrefix, hne, readArg, hnot]

theorem decodeFloatPrefix_truncated_f64 {rest : List UInt8} (h : rest.length < 8) :
    decodeFloatPrefix (0xfb :: rest) = none := by
  have hne1 : (0xfb : UInt8) ≠ 0xf9 := by intro e; cases e
  have hne2 : (0xfb : UInt8) ≠ 0xfa := by intro e; cases e
  have hnot : ¬ (8 ≤ rest.length) := by omega
  simp [decodeFloatPrefix, hne1, hne2, readArg, hnot]

/-! ## IEEE 754 value classifications and distinguished constants -/

namespace Float16

def isZero (f : Float16) : Bool := f.exp == 0 && f.mant == 0
def isPosZero (f : Float16) : Bool := !f.sign && f.exp == 0 && f.mant == 0
def isNegZero (f : Float16) : Bool := f.sign && f.exp == 0 && f.mant == 0
def isSubnormal (f : Float16) : Bool := f.exp == 0 && f.mant != 0
def isNormal (f : Float16) : Bool := 1 ≤ f.exp && f.exp ≤ 30
def isFinite (f : Float16) : Bool := f.exp < 31
def isInf (f : Float16) : Bool := f.exp == 31 && f.mant == 0
def isPosInf (f : Float16) : Bool := !f.sign && f.exp == 31 && f.mant == 0
def isNegInf (f : Float16) : Bool := f.sign && f.exp == 31 && f.mant == 0
def isNaN (f : Float16) : Bool := f.exp == 31 && f.mant != 0
def isQuietNaN (f : Float16) : Bool := f.exp == 31 && 512 ≤ f.mant
def isSignalingNaN (f : Float16) : Bool := f.exp == 31 && 1 ≤ f.mant && f.mant < 512

def posZero : Float16 := ⟨false, 0, 0, by omega, by omega⟩
def negZero : Float16 := ⟨true, 0, 0, by omega, by omega⟩
def posInf : Float16 := ⟨false, 31, 0, by omega, by omega⟩
def negInf : Float16 := ⟨true, 31, 0, by omega, by omega⟩
/-- Canonical deterministic quiet NaN (`0x7e00`, wire `0xf97e00`, §4.2.1 / §4.2.2). -/
def canonicalNaN : Float16 := ⟨false, 31, 512, by omega, by omega⟩
/-- Smallest positive `binary16` subnormal (`2^-24`, `0x0001`, Appendix A Row 28). -/
def minPosSubnormal : Float16 := ⟨false, 0, 1, by omega, by omega⟩
/-- Largest positive `binary16` subnormal (`1023 * 2^-24`, `0x03ff`). -/
def maxPosSubnormal : Float16 := ⟨false, 0, 1023, by omega, by omega⟩
/-- Smallest positive `binary16` normal (`2^-14`, `0x0400`, Appendix A Row 29). -/
def minPosNormal : Float16 := ⟨false, 1, 0, by omega, by omega⟩
/-- Largest finite `binary16` (`65504.0`, `0x7bff`, Appendix A Row 24). -/
def maxFinite : Float16 := ⟨false, 30, 1023, by omega, by omega⟩

theorem classify_partition (f : Float16) :
    (f.isZero = true ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = true ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = true ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = true ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = true) := by
  have he := f.hexp
  by_cases he0 : f.exp = 0
  · by_cases hm0 : f.mant = 0
    · exact Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
    · exact Or.inr <| Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
  · by_cases he31 : f.exp = 31
    · by_cases hm0 : f.mant = 0
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he31, hm0])
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he31, hm0])
    · exact Or.inr <| Or.inr <| Or.inl
        (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, he31]; omega)

theorem nan_iff_quiet_or_signaling (f : Float16) :
    f.isNaN = true ↔ (f.isQuietNaN = true ∨ f.isSignalingNaN = true) := by
  simp only [isNaN, isQuietNaN, isSignalingNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, decide_eq_true_eq]
  omega

end Float16

namespace Float32

def isZero (f : Float32) : Bool := f.exp == 0 && f.mant == 0
def isPosZero (f : Float32) : Bool := !f.sign && f.exp == 0 && f.mant == 0
def isNegZero (f : Float32) : Bool := f.sign && f.exp == 0 && f.mant == 0
def isSubnormal (f : Float32) : Bool := f.exp == 0 && f.mant != 0
def isNormal (f : Float32) : Bool := 1 ≤ f.exp && f.exp ≤ 254
def isFinite (f : Float32) : Bool := f.exp < 255
def isInf (f : Float32) : Bool := f.exp == 255 && f.mant == 0
def isPosInf (f : Float32) : Bool := !f.sign && f.exp == 255 && f.mant == 0
def isNegInf (f : Float32) : Bool := f.sign && f.exp == 255 && f.mant == 0
def isNaN (f : Float32) : Bool := f.exp == 255 && f.mant != 0
def isQuietNaN (f : Float32) : Bool := f.exp == 255 && 4194304 ≤ f.mant
def isSignalingNaN (f : Float32) : Bool := f.exp == 255 && 1 ≤ f.mant && f.mant < 4194304

def posZero : Float32 := ⟨false, 0, 0, by omega, by omega⟩
def negZero : Float32 := ⟨true, 0, 0, by omega, by omega⟩
def posInf : Float32 := ⟨false, 255, 0, by omega, by omega⟩
def negInf : Float32 := ⟨true, 255, 0, by omega, by omega⟩
def quietNaN : Float32 := ⟨false, 255, 4194304, by omega, by omega⟩
def minPosSubnormal : Float32 := ⟨false, 0, 1, by omega, by omega⟩
def maxFinite : Float32 := ⟨false, 254, 8388607, by omega, by omega⟩

theorem classify_partition (f : Float32) :
    (f.isZero = true ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = true ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = true ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = true ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = true) := by
  have he := f.hexp
  by_cases he0 : f.exp = 0
  · by_cases hm0 : f.mant = 0
    · exact Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
    · exact Or.inr <| Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
  · by_cases he255 : f.exp = 255
    · by_cases hm0 : f.mant = 0
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he255, hm0])
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he255, hm0])
    · exact Or.inr <| Or.inr <| Or.inl
        (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, he255]; omega)

end Float32

namespace Float64

def isZero (f : Float64) : Bool := f.exp == 0 && f.mant == 0
def isPosZero (f : Float64) : Bool := !f.sign && f.exp == 0 && f.mant == 0
def isNegZero (f : Float64) : Bool := f.sign && f.exp == 0 && f.mant == 0
def isSubnormal (f : Float64) : Bool := f.exp == 0 && f.mant != 0
def isNormal (f : Float64) : Bool := 1 ≤ f.exp && f.exp ≤ 2046
def isFinite (f : Float64) : Bool := f.exp < 2047
def isInf (f : Float64) : Bool := f.exp == 2047 && f.mant == 0
def isPosInf (f : Float64) : Bool := !f.sign && f.exp == 2047 && f.mant == 0
def isNegInf (f : Float64) : Bool := f.sign && f.exp == 2047 && f.mant == 0
def isNaN (f : Float64) : Bool := f.exp == 2047 && f.mant != 0
def isQuietNaN (f : Float64) : Bool := f.exp == 2047 && 2251799813685248 ≤ f.mant
def isSignalingNaN (f : Float64) : Bool := f.exp == 2047 && 1 ≤ f.mant && f.mant < 2251799813685248

def posZero : Float64 := ⟨false, 0, 0, by omega, by omega⟩
def negZero : Float64 := ⟨true, 0, 0, by omega, by omega⟩
def posInf : Float64 := ⟨false, 2047, 0, by omega, by omega⟩
def negInf : Float64 := ⟨true, 2047, 0, by omega, by omega⟩
def quietNaN : Float64 := ⟨false, 2047, 2251799813685248, by omega, by omega⟩
def minPosSubnormal : Float64 := ⟨false, 0, 1, by omega, by omega⟩

theorem classify_partition (f : Float64) :
    (f.isZero = true ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = true ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = true ∧ f.isInf = false ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = true ∧ f.isNaN = false) ∨
    (f.isZero = false ∧ f.isSubnormal = false ∧ f.isNormal = false ∧ f.isInf = false ∧ f.isNaN = true) := by
  have he := f.hexp
  by_cases he0 : f.exp = 0
  · by_cases hm0 : f.mant = 0
    · exact Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
    · exact Or.inr <| Or.inl (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, hm0])
  · by_cases he2047 : f.exp = 2047
    · by_cases hm0 : f.mant = 0
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he2047, hm0])
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr
          (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he2047, hm0])
    · exact Or.inr <| Or.inr <| Or.inl
        (by simp [isZero, isSubnormal, isNormal, isInf, isNaN, he0, he2047]; omega)

end Float64

namespace CborFloat

def isZero : CborFloat → Bool
  | .half f => f.isZero
  | .single f => f.isZero
  | .double f => f.isZero

def isNegZero : CborFloat → Bool
  | .half f => f.isNegZero
  | .single f => f.isNegZero
  | .double f => f.isNegZero

def isSubnormal : CborFloat → Bool
  | .half f => f.isSubnormal
  | .single f => f.isSubnormal
  | .double f => f.isSubnormal

def isNormal : CborFloat → Bool
  | .half f => f.isNormal
  | .single f => f.isNormal
  | .double f => f.isNormal

def isInf : CborFloat → Bool
  | .half f => f.isInf
  | .single f => f.isInf
  | .double f => f.isInf

def isNaN : CborFloat → Bool
  | .half f => f.isNaN
  | .single f => f.isNaN
  | .double f => f.isNaN

end CborFloat

/-! ## Exact symbolic IEEE 754 mathematical valuation (`IEEEValue`) -/

/-- Exact IEEE 754 value across `binary16`, `binary32`, and `binary64`,
preserving signed zero and NaN sign + 52-bit right-zero-extended significand
(for §4.1 preferred-serialization value reconstitution).

For finite nonzero floats, `scaledMag` is the exact positive integer
`|value| * 2^1074`:
* `Float16`: subnormal `mant * 2^-24` → `mant * 2^1050`;
             normal `(1024 + mant) * 2^(exp - 25)` → `(1024 + mant) * 2^(exp + 1049)`;
* `Float32`: subnormal `mant * 2^-149` → `mant * 2^925`;
             normal `(2^23 + mant) * 2^(exp - 150)` → `(2^23 + mant) * 2^(exp + 924)`;
* `Float64`: subnormal `mant * 2^-1074` → `mant`;
             normal `(2^52 + mant) * 2^(exp - 1075)` → `(2^52 + mant) * 2^(exp - 1)`. -/
inductive IEEEValue where
  | zero (sign : Bool)
  | finiteNz (sign : Bool) (scaledMag : Nat)
  | inf (sign : Bool)
  | nan (sign : Bool) (sig52 : Nat)
  deriving DecidableEq, Repr

/-- Direct IEEE 754 / Appendix D valuation of `Float16`. -/
def Float16.toIEEEValue (f : Float16) : IEEEValue :=
  if f.exp = 0 then
    if f.mant = 0 then .zero f.sign
    else .finiteNz f.sign (f.mant * 2 ^ 1050)
  else if f.exp = 31 then
    if f.mant = 0 then .inf f.sign
    else .nan f.sign (f.mant * 2 ^ 42)
  else
    .finiteNz f.sign ((1024 + f.mant) * 2 ^ (f.exp + 1049))

/-- Direct IEEE 754 valuation of `Float32`. -/
def Float32.toIEEEValue (f : Float32) : IEEEValue :=
  if f.exp = 0 then
    if f.mant = 0 then .zero f.sign
    else .finiteNz f.sign (f.mant * 2 ^ 925)
  else if f.exp = 255 then
    if f.mant = 0 then .inf f.sign
    else .nan f.sign (f.mant * 2 ^ 29)
  else
    .finiteNz f.sign ((8388608 + f.mant) * 2 ^ (f.exp + 924))

/-- Direct IEEE 754 valuation of `Float64`. -/
def Float64.toIEEEValue (f : Float64) : IEEEValue :=
  if f.exp = 0 then
    if f.mant = 0 then .zero f.sign
    else .finiteNz f.sign f.mant
  else if f.exp = 2047 then
    if f.mant = 0 then .inf f.sign
    else .nan f.sign f.mant
  else
    .finiteNz f.sign ((4503599627370496 + f.mant) * 2 ^ (f.exp - 1))

/-- Direct IEEE 754 valuation of any `CborFloat`. -/
def CborFloat.toIEEEValue : CborFloat → IEEEValue
  | .half f => f.toIEEEValue
  | .single f => f.toIEEEValue
  | .double f => f.toIEEEValue

private theorem normal_scaled_eq_imp {B m₁ m₂ k₁ k₂ : Nat}
    (_hB : 0 < B) (hm₁ : m₁ < B) (hm₂ : m₂ < B)
    (heq : (B + m₁) * 2 ^ k₁ = (B + m₂) * 2 ^ k₂) : k₁ = k₂ ∧ m₁ = m₂ := by
  have hk : k₁ = k₂ :=
    if hlt : k₁ < k₂ then
      False.elim <| by
        obtain ⟨d, rfl⟩ : ∃ d, k₂ = k₁ + (d + 1) := ⟨k₂ - k₁ - 1, by omega⟩
        have hd : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
        have hpow : 2 ^ (k₁ + (d + 1)) = 2 * 2 ^ d * 2 ^ k₁ := by
          rw [Nat.pow_add, Nat.pow_succ]
          exact (Nat.mul_comm _ _).trans (by rw [Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc])
        rw [hpow] at heq
        have hge : 2 * B * 2 ^ k₁ ≤ (B + m₂) * (2 * 2 ^ d * 2 ^ k₁) := by
          have h1 : 2 * B ≤ (B + m₂) * (2 * 2 ^ d) := by
            have : 2 * B ≤ B * (2 * 2 ^ d) := by
              have : 2 ≤ 2 * 2 ^ d := by omega
              exact Nat.mul_comm 2 B ▸ Nat.mul_le_mul_left B this
            have : B * (2 * 2 ^ d) ≤ (B + m₂) * (2 * 2 ^ d) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right (2 ^ k₁) h1
        have hlt2 : (B + m₁) * 2 ^ k₁ < 2 * B * 2 ^ k₁ :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
        omega
    else if hgt : k₂ < k₁ then
      False.elim <| by
        obtain ⟨d, rfl⟩ : ∃ d, k₁ = k₂ + (d + 1) := ⟨k₁ - k₂ - 1, by omega⟩
        have hd : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
        have hpow : 2 ^ (k₂ + (d + 1)) = 2 * 2 ^ d * 2 ^ k₂ := by
          rw [Nat.pow_add, Nat.pow_succ]
          exact (Nat.mul_comm _ _).trans (by rw [Nat.mul_comm (2 ^ d) 2, Nat.mul_assoc])
        rw [hpow] at heq
        have hge : 2 * B * 2 ^ k₂ ≤ (B + m₁) * (2 * 2 ^ d * 2 ^ k₂) := by
          have h1 : 2 * B ≤ (B + m₁) * (2 * 2 ^ d) := by
            have : 2 * B ≤ B * (2 * 2 ^ d) := by
              have : 2 ≤ 2 * 2 ^ d := by omega
              exact Nat.mul_comm 2 B ▸ Nat.mul_le_mul_left B this
            have : B * (2 * 2 ^ d) ≤ (B + m₁) * (2 * 2 ^ d) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right (2 ^ k₂) h1
        have hlt2 : (B + m₂) * 2 ^ k₂ < 2 * B * 2 ^ k₂ :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega))
        omega
    else by omega
  subst hk
  have hpos : 0 < 2 ^ k₁ := Nat.pow_pos (by omega)
  have hbm : B + m₁ = B + m₂ := Nat.eq_of_mul_eq_mul_right hpos heq
  exact ⟨rfl, by omega⟩

/-- **Representation uniqueness in `binary64`:** distinct `Float64` bit patterns
never share the same `IEEEValue`. -/
theorem Float64.toIEEEValue_injective : Function.Injective Float64.toIEEEValue := by
  intro a b h
  have hae := a.hexp; have ham := a.hmant
  have hbe := b.hexp; have hbm := b.hmant
  unfold Float64.toIEEEValue at h
  by_cases ha0 : a.exp = 0 <;> by_cases hb0 : b.exp = 0
  · by_cases ham0 : a.mant = 0 <;> by_cases hbm0 : b.mant = 0
    · simp [ha0, hb0, ham0, hbm0] at h
      exact Float64.ext h (by omega) (by omega)
    · simp [ha0, hb0, ham0, hbm0] at h
    · simp [ha0, hb0, ham0, hbm0] at h
    · simp [ha0, hb0, ham0, hbm0] at h
      exact Float64.ext h.1 (by omega) h.2
  · by_cases ham0 : a.mant = 0
    · by_cases hb2047 : b.exp = 2047
      · by_cases hbm0 : b.mant = 0 <;> simp [ha0, ham0, hb2047, hbm0] at h
      · simp [ha0, hb0, ham0, hb2047] at h
    · by_cases hb2047 : b.exp = 2047
      · by_cases hbm0 : b.mant = 0 <;> simp [ha0, ham0, hb2047, hbm0] at h
      · simp [ha0, hb0, ham0, hb2047] at h
        have h1 : 1 ≤ 2 ^ (b.exp - 1) := Nat.one_le_pow _ 2 (by omega)
        have h2 : 4503599627370496 ≤ (4503599627370496 + b.mant) * 2 ^ (b.exp - 1) := by
          have := Nat.mul_le_mul_left (4503599627370496 + b.mant) h1
          omega
        omega
  · by_cases hbm0 : b.mant = 0
    · by_cases ha2047 : a.exp = 2047
      · by_cases ham0 : a.mant = 0 <;> simp [hb0, ham0, ha2047, hbm0] at h
      · simp [ha0, hb0, ha2047, hbm0] at h
    · by_cases ha2047 : a.exp = 2047
      · by_cases ham0 : a.mant = 0 <;> simp [hb0, ham0, ha2047, hbm0] at h
      · simp [ha0, hb0, hbm0, ha2047] at h
        have h1 : 1 ≤ 2 ^ (a.exp - 1) := Nat.one_le_pow _ 2 (by omega)
        have h2 : 4503599627370496 ≤ (4503599627370496 + a.mant) * 2 ^ (a.exp - 1) := by
          have := Nat.mul_le_mul_left (4503599627370496 + a.mant) h1
          omega
        omega
  · by_cases ha2047 : a.exp = 2047 <;> by_cases hb2047 : b.exp = 2047
    · by_cases ham0 : a.mant = 0 <;> by_cases hbm0 : b.mant = 0
      · simp [ha2047, hb2047, ham0, hbm0] at h
        exact Float64.ext h (by omega) (by omega)
      · simp [ha2047, hb2047, ham0, hbm0] at h
      · simp [ha2047, hb2047, ham0, hbm0] at h
      · simp [ha2047, hb2047, ham0, hbm0] at h
        exact Float64.ext h.1 (by omega) h.2
    · by_cases ham0 : a.mant = 0 <;> simp [hb0, ha2047, hb2047, ham0] at h
    · by_cases hbm0 : b.mant = 0 <;> simp [ha0, ha2047, hb2047, hbm0] at h
    · simp [ha0, hb0, ha2047, hb2047] at h
      obtain ⟨hs, hmag⟩ := h
      obtain ⟨hk, hm⟩ := normal_scaled_eq_imp (B := 4503599627370496) (by omega) ham hbm hmag
      exact Float64.ext hs (by omega) hm

/-! ## RFC 8949 Appendix D half-precision bit-extraction correspondence -/

/-- RFC 8949 Appendix D Figure 3 C bit-extraction from the 2 big-endian payload
bytes `b₀, b₁` following `0xf9`:
`half = (b₀ << 8) + b₁`, `sign = (half & 0x8000) != 0`,
`exp = (half >> 10) & 0x1f`, `mant = half & 0x3ff`. -/
def appendixDHalfFields (b₀ b₁ : UInt8) : Bool × Nat × Nat :=
  let half := (b₀.toNat <<< 8) + b₁.toNat
  ((half &&& 0x8000) != 0, (half >>> 10) &&& 0x1f, half &&& 0x3ff)

/-- **Appendix D correspondence:** decoding `[0xf9, b₀, b₁]` yields a `Float16`
whose `(sign, exp, mant)` fields equal RFC 8949 Appendix D Figure 3's bit-mask
extraction on `(b₀ << 8) + b₁`. -/
theorem decodeFloat16_eq_appendixD (b₀ b₁ : UInt8) :
    ∃ f : Float16,
      decodeFloat16 [0xf9, b₀, b₁] = some f ∧
      (f.sign, f.exp, f.mant) = appendixDHalfFields b₀ b₁ := by
  have hb₀ : b₀.toNat < 256 := b₀.toNat_lt
  have hb₁ : b₁.toNat < 256 := b₁.toNat_lt
  let half := b₀.toNat * 256 + b₁.toNat
  refine ⟨Float16.ofBits half, ?_, ?_⟩
  · simp [decodeFloat16, decodeFloat16Prefix, readArg, beValue, half]
  · have hshl : b₀.toNat <<< 8 = b₀.toNat * 256 := Nat.shiftLeft_eq b₀.toNat 8
    have hlt : half < 65536 := by omega
    have hmod : half % 65536 = half := Nat.mod_eq_of_lt hlt
    have hshr : half >>> 10 = half / 1024 := Nat.shiftRight_eq_div_pow half 10
    have hand31 : (half / 1024) &&& 0x1f = (half / 1024) % 32 :=
      Nat.and_two_pow_sub_one_eq_mod (half / 1024) 5
    have hand1023 : half &&& 0x3ff = half % 1024 :=
      Nat.and_two_pow_sub_one_eq_mod half 10
    have hsign : ((half / 32768 == 1) = ((half &&& 0x8000) != 0)) := by
      have h15 : (half &&& 0x8000) = ((half / 32768) % 2) * 32768 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        by_cases hi : i = 15
        · subst hi
          by_cases hge : 32768 ≤ half
          · have hd : half / 32768 = 1 := by omega
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
          · have hd : half / 32768 = 0 := by omega
            simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hd]
        · have h0x8000 : (0x8000 : Nat).testBit i = false := by
            simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
            by_cases hlt15 : i < 15
            · obtain ⟨d, hd15⟩ : ∃ d, 15 = i + (d + 1) := ⟨14 - i, by omega⟩
              have hp : (0x8000 : Nat) = 2 ^ (i + (d + 1)) := by
                rw [← hd15]
              rw [hp, Nat.pow_add, Nat.mul_div_cancel_left _ (Nat.pow_pos (by omega)),
                Nat.pow_succ, Nat.and_comm, Nat.and_one_is_mod]
              simp
            · have hgt : 16 ≤ i := by omega
              have hle : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hgt
              have hdiv0 : 0x8000 / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
              simp [hdiv0]
          rw [h0x8000, Bool.and_false]
          by_cases hge : 32768 ≤ half
          · have hd : half / 32768 = 1 := by omega
            rw [hd]; simp only [Nat.one_mod, Nat.one_mul]
            exact h0x8000.symm
          · have hd : half / 32768 = 0 := by omega
            rw [hd]; simp
      rw [h15]
      by_cases hge : 32768 ≤ half
      · have hd1 : half / 32768 = 1 := by omega
        simp [hd1]
      · have hd0 : half / 32768 = 0 := by omega
        simp [hd0]
    unfold appendixDHalfFields Float16.ofBits
    simp only [hshl, hmod, hshr, hand31, hand1023, hsign, half]

end Cbor.Rfc8949
