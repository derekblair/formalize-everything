/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Float.IEEE754

/-!
# RFC 8949 §4.1, §4.2.1 & §4.2.2: Shortest-Float Narrowing, NaN Canonicalization, and Boundary Cases

This module formalizes:

1. **Exact value-preserving widening (`widen16To32`, `widen32To64`, `widen16To64`):**
   proved to preserve `IEEEValue` across all normal, subnormal, signed-zero,
   `±Infinity`, and NaN payload bit patterns.
2. **Exact value-preserving narrowing (`narrow64To32?`, `narrow32To16?`, `narrow64To16?`):**
   proved sound and complete (`narrow64To32? d = some s ↔ s.toIEEEValue = d.toIEEEValue`
   and `narrow32To16? s = some h ↔ h.toIEEEValue = s.toIEEEValue`), including the
   normal-to-subnormal cross-width boundary (`exp64 ∈ 874..896` and `exp32 ∈ 103..112`)
   and §4.1 NaN right-zero-padded significand reconstitution.
3. **Preferred serialization (§4.1: `preferredFloat`, `isPreferredFloat`,
   `encodeFloatPreferred`, `decodeFloatPreferred`):**
   stepwise `binary64 → binary32 → binary16` narrowing proved to achieve the
   unique minimum wire length among all `CborFloat` encodings with the same
   `IEEEValue`.
4. **Core deterministic float serialization (§4.2.1 / §4.2.2: `canonicalFloatDet`,
   `isDeterministicFloat`, `encodeFloatDeterministic`, `decodeFloatDeterministic`):**
   shortest value-preserving width for all non-NaN floats (preserving `-0.0` =
   `0xf98000` vs. `0.0` = `0xf90000` and narrowing `±Infinity` to `0xf97c00` /
   `0xf9fc00`) plus canonicalization of every NaN (regardless of sign, quiet /
   signaling bit, or payload) to quiet half-precision `0xf97e00`.
5. **IEEE 754 round-to-nearest-even lossy narrowing (`round64To32`, `round32To16`)
   and boundary cases (§2.4):**
   signed zeros, `±Infinity`, quiet vs. signaling NaNs and NaN payloads,
   subnormals across all three widths, and proved witnesses of values that do
   not round-trip through narrower widths (naming the exact loss: precision
   narrowing, exponent overflow to `±Infinity`, or exponent underflow to `±0.0`).
-/

namespace Cbor.Rfc8949

/-! ## Structurally recursive most-significant-bit index for subnormal normalization -/

/-- Fuel-bounded index of the highest set bit of a positive natural number.
Defined by structural recursion on `fuel` so kernel reduction (`rfl`) avoids
`WellFounded.fix`. -/
def msbAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n ≤ 1 then 0 else msbAux fuel (n / 2) + 1

theorem pow_msbAux_le : ∀ (fuel n : Nat), 0 < n → 2 ^ msbAux fuel n ≤ n
  | 0, _, hn => by simp [msbAux]; omega
  | fuel + 1, n, _ => by
    simp only [msbAux]
    split
    · simp; omega
    · have hle := pow_msbAux_le fuel (n / 2) (by omega)
      rw [Nat.pow_succ]
      omega

theorem lt_pow_succ_msbAux : ∀ (fuel n : Nat), n < 2 ^ (fuel + 1) → n < 2 ^ (msbAux fuel n + 1)
  | 0, n, hlt => by simp [msbAux] at hlt ⊢; omega
  | fuel + 1, n, hlt => by
    simp only [msbAux]
    split
    · simp; omega
    · have hdiv : n / 2 < 2 ^ (fuel + 1) := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := lt_pow_succ_msbAux fuel (n / 2) hdiv
      rw [Nat.pow_succ]
      omega

theorem msbAux_lt_of_lt_pow {fuel n k : Nat} (hn : 0 < n) (h : n < 2 ^ k) :
    msbAux fuel n < k :=
  if hlt : msbAux fuel n < k then hlt
  else False.elim <| by
    have h1 : 2 ^ k ≤ 2 ^ msbAux fuel n := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ msbAux fuel n ≤ n := pow_msbAux_le fuel n hn
    omega

/-! ## Exact IEEE 754 widening (`Float16 ↪ Float32 ↪ Float64`) -/

/-- Exact IEEE 754 widening from `binary16` to `binary32`.
Every `binary16` subnormal (`exp = 0, mant > 0`) becomes a `binary32` normal
with `exp ∈ 103..112`. -/
def widen16To32 (h : Float16) : Float32 :=
  if _he0 : h.exp = 0 then
    if hm0 : h.mant = 0 then
      ⟨h.sign, 0, 0, by omega, by omega⟩
    else
      let k := msbAux 10 h.mant
      have hk10 : k < 10 := msbAux_lt_of_lt_pow (by omega) h.hmant
      have hlt : h.mant < 2 ^ (k + 1) :=
        lt_pow_succ_msbAux 10 h.mant (by have := h.hmant; omega)
      have hmant32 : (h.mant - 2 ^ k) * 2 ^ (23 - k) < 8388608 := by
        have hrem : h.mant - 2 ^ k < 2 ^ k := by
          rw [Nat.pow_succ] at hlt; omega
        have hmul := Nat.mul_lt_mul_of_pos_right hrem (Nat.pow_pos (a := 2) (n := 23 - k) (by omega))
        have hpow : 2 ^ k * 2 ^ (23 - k) = 8388608 := by
          rw [← Nat.pow_add, show k + (23 - k) = 23 by omega]
        omega
      ⟨h.sign, k + 103, (h.mant - 2 ^ k) * 2 ^ (23 - k), by omega, hmant32⟩
  else if _he31 : h.exp = 31 then
    if _hm0 : h.mant = 0 then
      ⟨h.sign, 255, 0, by omega, by omega⟩
    else
      ⟨h.sign, 255, h.mant * 8192, by omega, by have := h.hmant; omega⟩
  else
    ⟨h.sign, h.exp + 112, h.mant * 8192, by have := h.hexp; omega, by have := h.hmant; omega⟩

/-- Exact IEEE 754 widening from `binary32` to `binary64`.
Every `binary32` subnormal (`exp = 0, mant > 0`) becomes a `binary64` normal
with `exp ∈ 874..896`. -/
def widen32To64 (s : Float32) : Float64 :=
  if _he0 : s.exp = 0 then
    if hm0 : s.mant = 0 then
      ⟨s.sign, 0, 0, by omega, by omega⟩
    else
      let k := msbAux 23 s.mant
      have hk23 : k < 23 := msbAux_lt_of_lt_pow (by omega) s.hmant
      have hlt : s.mant < 2 ^ (k + 1) :=
        lt_pow_succ_msbAux 23 s.mant (by have := s.hmant; omega)
      have hmant64 : (s.mant - 2 ^ k) * 2 ^ (52 - k) < 4503599627370496 := by
        have hrem : s.mant - 2 ^ k < 2 ^ k := by
          rw [Nat.pow_succ] at hlt; omega
        have hmul := Nat.mul_lt_mul_of_pos_right hrem (Nat.pow_pos (a := 2) (n := 52 - k) (by omega))
        have hpow : 2 ^ k * 2 ^ (52 - k) = 4503599627370496 := by
          rw [← Nat.pow_add, show k + (52 - k) = 52 by omega]
        omega
      ⟨s.sign, k + 874, (s.mant - 2 ^ k) * 2 ^ (52 - k), by omega, hmant64⟩
  else if _he255 : s.exp = 255 then
    if _hm0 : s.mant = 0 then
      ⟨s.sign, 2047, 0, by omega, by omega⟩
    else
      ⟨s.sign, 2047, s.mant * 536870912, by omega, by have := s.hmant; omega⟩
  else
    ⟨s.sign, s.exp + 896, s.mant * 536870912, by have := s.hexp; omega, by have := s.hmant; omega⟩

/-- Exact IEEE 754 widening from `binary16` to `binary64`. -/
def widen16To64 (h : Float16) : Float64 :=
  widen32To64 (widen16To32 h)

/-- Embed any `CborFloat` losslessly into `Float64`. -/
def CborFloat.toFloat64 : CborFloat → Float64
  | .half h => widen16To64 h
  | .single s => widen32To64 s
  | .double d => d

private theorem widen16To32_fields_sub {h : Float16} (he0 : h.exp = 0) (hm0 : h.mant ≠ 0) :
    (widen16To32 h).sign = h.sign ∧
    (widen16To32 h).exp = msbAux 10 h.mant + 103 ∧
    (widen16To32 h).mant = (h.mant - 2 ^ msbAux 10 h.mant) * 2 ^ (23 - msbAux 10 h.mant) := by
  simp [widen16To32, he0, hm0]

private theorem widen16To32_fields_nan {h : Float16} (he31 : h.exp = 31) (hm0 : h.mant ≠ 0) :
    (widen16To32 h).sign = h.sign ∧
    (widen16To32 h).exp = 255 ∧
    (widen16To32 h).mant = h.mant * 8192 := by
  simp [widen16To32, he31, hm0]

private theorem widen16To32_fields_norm {h : Float16} (he0 : h.exp ≠ 0) (he31 : h.exp ≠ 31) :
    (widen16To32 h).sign = h.sign ∧
    (widen16To32 h).exp = h.exp + 112 ∧
    (widen16To32 h).mant = h.mant * 8192 := by
  simp [widen16To32, he0, he31]

private theorem widen32To64_fields_sub {s : Float32} (he0 : s.exp = 0) (hm0 : s.mant ≠ 0) :
    (widen32To64 s).sign = s.sign ∧
    (widen32To64 s).exp = msbAux 23 s.mant + 874 ∧
    (widen32To64 s).mant = (s.mant - 2 ^ msbAux 23 s.mant) * 2 ^ (52 - msbAux 23 s.mant) := by
  simp [widen32To64, he0, hm0]

private theorem widen32To64_fields_nan {s : Float32} (he255 : s.exp = 255) (hm0 : s.mant ≠ 0) :
    (widen32To64 s).sign = s.sign ∧
    (widen32To64 s).exp = 2047 ∧
    (widen32To64 s).mant = s.mant * 536870912 := by
  simp [widen32To64, he255, hm0]

private theorem widen32To64_fields_norm {s : Float32} (he0 : s.exp ≠ 0) (he255 : s.exp ≠ 255) :
    (widen32To64 s).sign = s.sign ∧
    (widen32To64 s).exp = s.exp + 896 ∧
    (widen32To64 s).mant = s.mant * 536870912 := by
  simp [widen32To64, he0, he255]

theorem widen16To32_toIEEEValue (h : Float16) :
    (widen16To32 h).toIEEEValue = h.toIEEEValue := by
  have he := h.hexp; have hm := h.hmant
  by_cases he0 : h.exp = 0
  · by_cases hm0 : h.mant = 0
    · simp [-Nat.reducePow, widen16To32, Float32.toIEEEValue, Float16.toIEEEValue, he0, hm0]
    · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_sub he0 hm0
      let k := msbAux 10 h.mant
      have hk10 : k < 10 := msbAux_lt_of_lt_pow (by omega) hm
      have hle : 2 ^ k ≤ h.mant := pow_msbAux_le 10 h.mant (by omega)
      have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
      have he32_255 : (widen16To32 h).exp ≠ 255 := by omega
      unfold Float32.toIEEEValue Float16.toIEEEValue
      simp only [he32_0, he32_255, he0, hm0, ↓reduceIte, IEEEValue.finiteNz.injEq]
      refine ⟨hs, ?_⟩
      rw [hexp, hmant]
      have hpow23 : (8388608 : Nat) = 2 ^ k * 2 ^ (23 - k) := by
        rw [← Nat.pow_add, show k + (23 - k) = 23 by omega]
      have hsig : 8388608 + (h.mant - 2 ^ k) * 2 ^ (23 - k) = h.mant * 2 ^ (23 - k) := by
        rw [hpow23, ← Nat.add_mul, Nat.add_sub_of_le hle]
      change (8388608 + (h.mant - 2 ^ k) * 2 ^ (23 - k)) * 2 ^ (k + 103 + 924) = h.mant * 2 ^ 1050
      have h1050 : (1050 : Nat) = (23 - k) + (k + 103 + 924) := by omega
      rw [hsig, h1050, Nat.pow_add 2 (23 - k) (k + 103 + 924), Nat.mul_assoc]
  · by_cases he31 : h.exp = 31
    · by_cases hm0 : h.mant = 0
      · simp [-Nat.reducePow, widen16To32, Float32.toIEEEValue, Float16.toIEEEValue, he31, hm0]
      · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_nan he31 hm0
        have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
        have hm32 : (widen16To32 h).mant ≠ 0 := by omega
        unfold Float32.toIEEEValue Float16.toIEEEValue
        simp only [he32_0, hm32, he0, hm0, ↓reduceIte]
        simp only [he31, hexp, ↓reduceIte, IEEEValue.nan.injEq]
        refine ⟨hs, ?_⟩
        rw [hmant]
        have h42 : (42 : Nat) = 13 + 29 := rfl
        have h8192 : (8192 : Nat) = 2 ^ 13 := rfl
        rw [h42, Nat.pow_add, h8192, Nat.mul_assoc]
    · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_norm he0 he31
      have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
      have he32_255 : (widen16To32 h).exp ≠ 255 := by omega
      unfold Float32.toIEEEValue Float16.toIEEEValue
      simp only [he32_0, he32_255, he0, he31, ↓reduceIte, IEEEValue.finiteNz.injEq]
      refine ⟨hs, ?_⟩
      rw [hexp, hmant]
      have hsig : 8388608 + h.mant * 8192 = (1024 + h.mant) * 2 ^ 13 := by
        change 8388608 + h.mant * 8192 = (1024 + h.mant) * 8192; omega
      rw [hsig, Nat.mul_assoc, (Nat.pow_add 2 13 (h.exp + 112 + 924)).symm,
        show 13 + (h.exp + 112 + 924) = h.exp + 1049 by omega]

theorem widen32To64_toIEEEValue (s : Float32) :
    (widen32To64 s).toIEEEValue = s.toIEEEValue := by
  have he := s.hexp; have hm := s.hmant
  by_cases he0 : s.exp = 0
  · by_cases hm0 : s.mant = 0
    · simp [-Nat.reducePow, widen32To64, Float64.toIEEEValue, Float32.toIEEEValue, he0, hm0]
    · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_sub he0 hm0
      let k := msbAux 23 s.mant
      have hk23 : k < 23 := msbAux_lt_of_lt_pow (by omega) hm
      have hle : 2 ^ k ≤ s.mant := pow_msbAux_le 23 s.mant (by omega)
      have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
      have he64_2047 : (widen32To64 s).exp ≠ 2047 := by omega
      unfold Float64.toIEEEValue Float32.toIEEEValue
      simp only [he64_0, he64_2047, he0, hm0, ↓reduceIte, IEEEValue.finiteNz.injEq]
      refine ⟨hs, ?_⟩
      rw [hexp, hmant]
      have hpow52 : (4503599627370496 : Nat) = 2 ^ k * 2 ^ (52 - k) := by
        rw [← Nat.pow_add, show k + (52 - k) = 52 by omega]
      have hsig : 4503599627370496 + (s.mant - 2 ^ k) * 2 ^ (52 - k) = s.mant * 2 ^ (52 - k) := by
        rw [hpow52, ← Nat.add_mul, Nat.add_sub_of_le hle]
      change (4503599627370496 + (s.mant - 2 ^ k) * 2 ^ (52 - k)) * 2 ^ (k + 874 - 1) = s.mant * 2 ^ 925
      rw [hsig, Nat.mul_assoc, (Nat.pow_add 2 (52 - k) (k + 874 - 1)).symm,
        show 52 - k + (k + 874 - 1) = 925 by omega]
  · by_cases he255 : s.exp = 255
    · by_cases hm0 : s.mant = 0
      · simp [-Nat.reducePow, widen32To64, Float64.toIEEEValue, Float32.toIEEEValue, he255, hm0]
      · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_nan he255 hm0
        have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
        have hm64 : (widen32To64 s).mant ≠ 0 := by omega
        unfold Float64.toIEEEValue Float32.toIEEEValue
        simp only [he64_0, hm64, he0, hm0, ↓reduceIte]
        simp only [he255, hexp, ↓reduceIte, IEEEValue.nan.injEq]
        exact ⟨hs, hmant⟩
    · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_norm he0 he255
      have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
      have he64_2047 : (widen32To64 s).exp ≠ 2047 := by omega
      unfold Float64.toIEEEValue Float32.toIEEEValue
      simp only [he64_0, he64_2047, he0, he255, ↓reduceIte, IEEEValue.finiteNz.injEq]
      refine ⟨hs, ?_⟩
      rw [hexp, hmant]
      have hsig : 4503599627370496 + s.mant * 536870912 = (8388608 + s.mant) * 2 ^ 29 := by
        change 4503599627370496 + s.mant * 536870912 = (8388608 + s.mant) * 536870912; omega
      rw [hsig, Nat.mul_assoc, (Nat.pow_add 2 29 (s.exp + 896 - 1)).symm,
        show 29 + (s.exp + 896 - 1) = s.exp + 924 by omega]

theorem widen16To64_toIEEEValue (h : Float16) :
    (widen16To64 h).toIEEEValue = h.toIEEEValue := by
  rw [widen16To64, widen32To64_toIEEEValue, widen16To32_toIEEEValue]

theorem CborFloat.toFloat64_toIEEEValue (f : CborFloat) :
    f.toFloat64.toIEEEValue = f.toIEEEValue := by
  cases f with
  | half h => exact widen16To64_toIEEEValue h
  | single s => exact widen32To64_toIEEEValue s
  | double d => rfl

/-! ## Exact value-preserving narrowing (`binary64 → binary32 → binary16`, §4.1 / §4.2.1) -/

/-- Exact value-preserving narrowing from `binary32` to `binary16` (§4.1 / §4.2.1).
Returns `some h` iff `h` has the exact same `IEEEValue` as `s` (including signed
zeros and NaN payloads whose low 13 significand bits are zero). -/
def narrow32To16? (s : Float32) : Option Float16 :=
  if s.exp = 0 then
    if s.mant = 0 then some ⟨s.sign, 0, 0, by omega, by omega⟩
    else none
  else if s.exp = 255 then
    if s.mant = 0 then some ⟨s.sign, 31, 0, by omega, by omega⟩
    else if s.mant % 8192 = 0 then
      some ⟨s.sign, 31, s.mant / 8192, by omega, by have := s.hmant; omega⟩
    else none
  else if hsub : 103 ≤ s.exp ∧ s.exp ≤ 112 then
    if (8388608 + s.mant) % (2 ^ (126 - s.exp)) = 0 then
      have hpow14 : 16384 ≤ 2 ^ (126 - s.exp) := by
        change 2 ^ 14 ≤ 2 ^ (126 - s.exp)
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hdiv_lt : (8388608 + s.mant) / (2 ^ (126 - s.exp)) < 1024 :=
        Nat.div_lt_of_lt_mul (by have := s.hmant; omega)
      some ⟨s.sign, 0, (8388608 + s.mant) / (2 ^ (126 - s.exp)), by omega, hdiv_lt⟩
    else none
  else if hnorm : 113 ≤ s.exp ∧ s.exp ≤ 142 then
    if s.mant % 8192 = 0 then
      some ⟨s.sign, s.exp - 112, s.mant / 8192, by omega, by have := s.hmant; omega⟩
    else none
  else none

/-- Exact value-preserving narrowing from `binary64` to `binary32` (§4.1 / §4.2.1).
Returns `some s` iff `s` has the exact same `IEEEValue` as `d` (including signed
zeros and NaN payloads whose low 29 significand bits are zero). -/
def narrow64To32? (d : Float64) : Option Float32 :=
  if d.exp = 0 then
    if d.mant = 0 then some ⟨d.sign, 0, 0, by omega, by omega⟩
    else none
  else if d.exp = 2047 then
    if d.mant = 0 then some ⟨d.sign, 255, 0, by omega, by omega⟩
    else if d.mant % 536870912 = 0 then
      some ⟨d.sign, 255, d.mant / 536870912, by omega, by have := d.hmant; omega⟩
    else none
  else if hsub : 874 ≤ d.exp ∧ d.exp ≤ 896 then
    if (4503599627370496 + d.mant) % (2 ^ (926 - d.exp)) = 0 then
      have hpow30 : 1073741824 ≤ 2 ^ (926 - d.exp) := by
        change 2 ^ 30 ≤ 2 ^ (926 - d.exp)
        exact Nat.pow_le_pow_right (by omega) (by omega)
      have hdiv_lt : (4503599627370496 + d.mant) / (2 ^ (926 - d.exp)) < 8388608 :=
        Nat.div_lt_of_lt_mul (by have := d.hmant; omega)
      some ⟨d.sign, 0, (4503599627370496 + d.mant) / (2 ^ (926 - d.exp)), by omega, hdiv_lt⟩
    else none
  else if hnorm : 897 ≤ d.exp ∧ d.exp ≤ 1150 then
    if d.mant % 536870912 = 0 then
      some ⟨d.sign, d.exp - 896, d.mant / 536870912, by omega, by have := d.hmant; omega⟩
    else none
  else none

/-- Stepwise narrowing `binary64 → binary32 → binary16` (§4.2.1). -/
def narrow64To16? (d : Float64) : Option Float16 :=
  (narrow64To32? d).bind narrow32To16?

/-- **Left inverse (`binary16 → binary32 → binary16`):** widening then narrowing
recovers every `Float16` bit-for-bit. -/
theorem narrow32To16?_widen16To32 (h : Float16) :
    narrow32To16? (widen16To32 h) = some h := by
  have he := h.hexp; have hm := h.hmant
  by_cases he0 : h.exp = 0
  · by_cases hm0 : h.mant = 0
    · simp only [widen16To32, narrow32To16?, he0, hm0, ↓reduceDIte, ↓reduceIte, Option.some.injEq]
      exact Float16.ext rfl he0.symm hm0.symm
    · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_sub he0 hm0
      let k := msbAux 10 h.mant
      have hk10 : k < 10 := msbAux_lt_of_lt_pow (by omega) hm
      have hle : 2 ^ k ≤ h.mant := pow_msbAux_le 10 h.mant (by omega)
      have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
      have he32_255 : (widen16To32 h).exp ≠ 255 := by omega
      have hsub : 103 ≤ (widen16To32 h).exp ∧ (widen16To32 h).exp ≤ 112 := by omega
      have hpow23 : (8388608 : Nat) = 2 ^ k * 2 ^ (23 - k) := by
        rw [← Nat.pow_add, show k + (23 - k) = 23 by omega]
      have hsh : 126 - (widen16To32 h).exp = 23 - k := by omega
      have hsig : 8388608 + (widen16To32 h).mant = h.mant * 2 ^ (23 - k) := by
        rw [hmant, hpow23, ← Nat.add_mul, Nat.add_sub_of_le hle]
      have hmod : (8388608 + (widen16To32 h).mant) % 2 ^ (126 - (widen16To32 h).exp) = 0 := by
        rw [hsig, hsh, Nat.mul_mod_left]
      have hdiv : (8388608 + (widen16To32 h).mant) / 2 ^ (126 - (widen16To32 h).exp) = h.mant := by
        rw [hsig, hsh, Nat.mul_div_cancel _ (Nat.pow_pos (by omega))]
      unfold narrow32To16?
      simp only [he32_0, he32_255, hsub, and_self, hmod, ↓reduceDIte, ↓reduceIte, Option.some.injEq]
      exact Float16.ext hs he0.symm hdiv
  · by_cases he31 : h.exp = 31
    · by_cases hm0 : h.mant = 0
      · simp [widen16To32, narrow32To16?, he31, hm0]
        exact Float16.ext rfl he31.symm hm0.symm
      · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_nan he31 hm0
        have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
        have hm32 : (widen16To32 h).mant ≠ 0 := by omega
        have hmod : (widen16To32 h).mant % 8192 = 0 := by rw [hmant, Nat.mul_mod_left]
        unfold narrow32To16?
        simp only [he32_0, hm32, hmod, ↓reduceIte]
        simp only [hexp, ↓reduceIte, Option.some.injEq]
        apply Float16.ext
        · exact hs
        · exact he31.symm
        · simp only; omega
    · obtain ⟨hs, hexp, hmant⟩ := widen16To32_fields_norm he0 he31
      have he32_0 : (widen16To32 h).exp ≠ 0 := by omega
      have he32_255 : (widen16To32 h).exp ≠ 255 := by omega
      have hnot_sub : ¬ (103 ≤ (widen16To32 h).exp ∧ (widen16To32 h).exp ≤ 112) := by omega
      have hnorm : 113 ≤ (widen16To32 h).exp ∧ (widen16To32 h).exp ≤ 142 := by omega
      have hmod : (widen16To32 h).mant % 8192 = 0 := by rw [hmant, Nat.mul_mod_left]
      unfold narrow32To16?
      simp only [he32_0, he32_255, hnot_sub, hnorm, and_self, hmod, ↓reduceDIte, ↓reduceIte,
        Option.some.injEq]
      apply Float16.ext
      · exact hs
      · simp only; omega
      · simp only; omega

/-- **Left inverse (`binary32 → binary64 → binary32`):** widening then narrowing
recovers every `Float32` bit-for-bit. -/
theorem narrow64To32?_widen32To64 (s : Float32) :
    narrow64To32? (widen32To64 s) = some s := by
  have he := s.hexp; have hm := s.hmant
  by_cases he0 : s.exp = 0
  · by_cases hm0 : s.mant = 0
    · simp only [widen32To64, narrow64To32?, he0, hm0, ↓reduceDIte, ↓reduceIte, Option.some.injEq]
      exact Float32.ext rfl he0.symm hm0.symm
    · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_sub he0 hm0
      let k := msbAux 23 s.mant
      have hk23 : k < 23 := msbAux_lt_of_lt_pow (by omega) hm
      have hle : 2 ^ k ≤ s.mant := pow_msbAux_le 23 s.mant (by omega)
      have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
      have he64_2047 : (widen32To64 s).exp ≠ 2047 := by omega
      have hsub : 874 ≤ (widen32To64 s).exp ∧ (widen32To64 s).exp ≤ 896 := by omega
      have hpow52 : (4503599627370496 : Nat) = 2 ^ k * 2 ^ (52 - k) := by
        rw [← Nat.pow_add, show k + (52 - k) = 52 by omega]
      have hsh : 926 - (widen32To64 s).exp = 52 - k := by omega
      have hsig : 4503599627370496 + (widen32To64 s).mant = s.mant * 2 ^ (52 - k) := by
        rw [hmant, hpow52, ← Nat.add_mul, Nat.add_sub_of_le hle]
      have hmod : (4503599627370496 + (widen32To64 s).mant) % 2 ^ (926 - (widen32To64 s).exp) = 0 := by
        rw [hsig, hsh, Nat.mul_mod_left]
      have hdiv : (4503599627370496 + (widen32To64 s).mant) / 2 ^ (926 - (widen32To64 s).exp) = s.mant := by
        rw [hsig, hsh, Nat.mul_div_cancel _ (Nat.pow_pos (by omega))]
      unfold narrow64To32?
      simp only [he64_0, he64_2047, hsub, and_self, hmod, ↓reduceDIte, ↓reduceIte, Option.some.injEq]
      exact Float32.ext hs he0.symm hdiv
  · by_cases he255 : s.exp = 255
    · by_cases hm0 : s.mant = 0
      · simp [widen32To64, narrow64To32?, he255, hm0]
        exact Float32.ext rfl he255.symm hm0.symm
      · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_nan he255 hm0
        have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
        have hm64 : (widen32To64 s).mant ≠ 0 := by omega
        have hmod : (widen32To64 s).mant % 536870912 = 0 := by rw [hmant, Nat.mul_mod_left]
        unfold narrow64To32?
        simp only [he64_0, hm64, hmod, ↓reduceIte]
        simp only [hexp, ↓reduceIte, Option.some.injEq]
        apply Float32.ext
        · exact hs
        · exact he255.symm
        · simp only; omega
    · obtain ⟨hs, hexp, hmant⟩ := widen32To64_fields_norm he0 he255
      have he64_0 : (widen32To64 s).exp ≠ 0 := by omega
      have he64_2047 : (widen32To64 s).exp ≠ 2047 := by omega
      have hnot_sub : ¬ (874 ≤ (widen32To64 s).exp ∧ (widen32To64 s).exp ≤ 896) := by omega
      have hnorm : 897 ≤ (widen32To64 s).exp ∧ (widen32To64 s).exp ≤ 1150 := by omega
      have hmod : (widen32To64 s).mant % 536870912 = 0 := by rw [hmant, Nat.mul_mod_left]
      unfold narrow64To32?
      simp only [he64_0, he64_2047, hnot_sub, hnorm, and_self, hmod, ↓reduceDIte, ↓reduceIte,
        Option.some.injEq]
      apply Float32.ext
      · exact hs
      · simp only; omega
      · simp only; omega

theorem widen16To32_injective : Function.Injective widen16To32 := fun a b h => by
  have := congrArg narrow32To16? h
  simpa [narrow32To16?_widen16To32] using this

theorem widen32To64_injective : Function.Injective widen32To64 := fun a b h => by
  have := congrArg narrow64To32? h
  simpa [narrow64To32?_widen32To64] using this

theorem widen16To64_injective : Function.Injective widen16To64 :=
  widen32To64_injective.comp widen16To32_injective

theorem narrow64To16?_widen16To64 (h : Float16) :
    narrow64To16? (widen16To64 h) = some h := by
  simp [narrow64To16?, widen16To64, narrow64To32?_widen32To64, narrow32To16?_widen16To32]

/-- **Representation uniqueness in `binary32`:** distinct `Float32` bit patterns
never share an `IEEEValue`. -/
theorem Float32.toIEEEValue_injective : Function.Injective Float32.toIEEEValue := fun a b h =>
  widen32To64_injective <| Float64.toIEEEValue_injective <| by
    rw [widen32To64_toIEEEValue, widen32To64_toIEEEValue, h]

/-- **Representation uniqueness in `binary16`:** distinct `Float16` bit patterns
never share an `IEEEValue`. -/
theorem Float16.toIEEEValue_injective : Function.Injective Float16.toIEEEValue := fun a b h =>
  widen16To32_injective <| Float32.toIEEEValue_injective <| by
    rw [widen16To32_toIEEEValue, widen16To32_toIEEEValue, h]

/-- **Soundness of `narrow32To16?`:** whenever `narrow32To16? s = some h`,
`h` preserves `s`'s exact `IEEEValue`. -/
theorem narrow32To16?_sound {s : Float32} {h : Float16}
    (hn : narrow32To16? s = some h) : h.toIEEEValue = s.toIEEEValue := by
  have he := s.hexp; have hm := s.hmant
  unfold narrow32To16? at hn
  by_cases he0 : s.exp = 0
  · simp only [he0, ↓reduceIte] at hn
    by_cases hm0 : s.mant = 0
    · simp only [hm0, ↓reduceIte, Option.some.injEq] at hn
      subst hn; simp [-Nat.reducePow, Float16.toIEEEValue, Float32.toIEEEValue, he0, hm0]
    · simp [hm0] at hn
  · by_cases he255 : s.exp = 255
    · by_cases hm0 : s.mant = 0
      · simp [he255, hm0] at hn
        subst hn; simp [-Nat.reducePow, Float16.toIEEEValue, Float32.toIEEEValue, he255, hm0]
      · by_cases hmod : s.mant % 8192 = 0
        · simp [he255, hm0, hmod] at hn
          subst hn
          have hdiv_pos : s.mant / 8192 ≠ 0 := fun hzero => by
            have := Nat.div_add_mod s.mant 8192; omega
          have hmul : (s.mant / 8192) * 8192 = s.mant := by
            have := Nat.div_add_mod s.mant 8192; omega
          have h42 : (2 : Nat) ^ 42 = 8192 * 2 ^ 29 := rfl
          simp [-Nat.reducePow, Float16.toIEEEValue, Float32.toIEEEValue, he255, hm0, hdiv_pos]
          rw [h42, ← Nat.mul_assoc, hmul]
        · simp [he255, hm0, hmod] at hn
    · by_cases hsub : 103 ≤ s.exp ∧ s.exp ≤ 112
      · simp only [he0, he255, hsub, and_self, ↓reduceIte, ↓reduceDIte] at hn
        by_cases hmod : (8388608 + s.mant) % (2 ^ (126 - s.exp)) = 0
        · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
          subst hn
          have hpow_le : 2 ^ (126 - s.exp) ≤ 8388608 := by
            change 2 ^ (126 - s.exp) ≤ 2 ^ 23
            exact Nat.pow_le_pow_right (by omega) (by omega)
          have hdiv_pos : (8388608 + s.mant) / 2 ^ (126 - s.exp) ≠ 0 := fun hz => by
            have := Nat.lt_of_div_eq_zero (Nat.pow_pos (by omega)) hz; omega
          have hmul : ((8388608 + s.mant) / 2 ^ (126 - s.exp)) * 2 ^ (126 - s.exp) = 8388608 + s.mant := by
            have hdm := Nat.div_add_mod (8388608 + s.mant) (2 ^ (126 - s.exp))
            rw [hmod, Nat.add_zero, Nat.mul_comm] at hdm
            exact hdm
          have h1050 : (2 : Nat) ^ 1050 = 2 ^ (126 - s.exp) * 2 ^ (s.exp + 924) := by
            rw [(Nat.pow_add 2 (126 - s.exp) (s.exp + 924)).symm,
              show 126 - s.exp + (s.exp + 924) = 1050 by omega]
          unfold Float16.toIEEEValue Float32.toIEEEValue
          simp only [he0, he255, ↓reduceIte]
          simp only [hdiv_pos, ↓reduceIte, IEEEValue.finiteNz.injEq, true_and]
          rw [h1050, ← Nat.mul_assoc, hmul]
        · simp [hmod] at hn
      · by_cases hnorm : 113 ≤ s.exp ∧ s.exp ≤ 142
        · simp only [he0, he255, hsub, hnorm, and_self, ↓reduceIte, ↓reduceDIte] at hn
          by_cases hmod : s.mant % 8192 = 0
          · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            have he16_0 : s.exp - 112 ≠ 0 := by omega
            have he16_31 : s.exp - 112 ≠ 31 := by omega
            unfold Float16.toIEEEValue Float32.toIEEEValue
            simp only [he0, he255, ↓reduceIte]
            simp only [he16_0, he16_31, ↓reduceIte, IEEEValue.finiteNz.injEq, true_and]
            have hcoef : (1024 + s.mant / 8192) * 8192 = 8388608 + s.mant := by omega
            have hpow : (2 : Nat) ^ (s.exp - 112 + 1049) = 8192 * 2 ^ (s.exp + 924) := by
              have hexp_eq : s.exp - 112 + 1049 = 13 + (s.exp + 924) := by omega
              rw [hexp_eq, Nat.pow_add]
            rw [hpow, ← Nat.mul_assoc, hcoef]
          · simp [hmod] at hn
        · simp [he0, he255, hsub, hnorm] at hn

/-- **Soundness of `narrow64To32?`:** whenever `narrow64To32? d = some s`,
`s` preserves `d`'s exact `IEEEValue`. -/
theorem narrow64To32?_sound {d : Float64} {s : Float32}
    (hn : narrow64To32? d = some s) : s.toIEEEValue = d.toIEEEValue := by
  have he := d.hexp; have hm := d.hmant
  unfold narrow64To32? at hn
  by_cases he0 : d.exp = 0
  · simp only [he0, ↓reduceIte] at hn
    by_cases hm0 : d.mant = 0
    · simp only [hm0, ↓reduceIte, Option.some.injEq] at hn
      subst hn; simp [-Nat.reducePow, Float32.toIEEEValue, Float64.toIEEEValue, he0, hm0]
    · simp [hm0] at hn
  · by_cases he2047 : d.exp = 2047
    · by_cases hm0 : d.mant = 0
      · simp [he2047, hm0] at hn
        subst hn; simp [-Nat.reducePow, Float32.toIEEEValue, Float64.toIEEEValue, he2047, hm0]
      · by_cases hmod : d.mant % 536870912 = 0
        · simp [he2047, hm0, hmod] at hn
          subst hn
          have hdiv_pos : d.mant / 536870912 ≠ 0 := fun hzero => by
            have := Nat.div_add_mod d.mant 536870912; omega
          simp [-Nat.reducePow, Float32.toIEEEValue, Float64.toIEEEValue, he2047, hm0, hdiv_pos]
          have := Nat.div_add_mod d.mant 536870912
          have h29 : (2 : Nat) ^ 29 = 536870912 := rfl
          rw [h29]; omega
        · simp [he2047, hm0, hmod] at hn
    · by_cases hsub : 874 ≤ d.exp ∧ d.exp ≤ 896
      · simp only [he0, he2047, hsub, and_self, ↓reduceIte, ↓reduceDIte] at hn
        by_cases hmod : (4503599627370496 + d.mant) % (2 ^ (926 - d.exp)) = 0
        · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
          subst hn
          have hpow_le : 2 ^ (926 - d.exp) ≤ 4503599627370496 := by
            change 2 ^ (926 - d.exp) ≤ 2 ^ 52
            exact Nat.pow_le_pow_right (by omega) (by omega)
          have hdiv_pos : (4503599627370496 + d.mant) / 2 ^ (926 - d.exp) ≠ 0 := fun hz => by
            have := Nat.lt_of_div_eq_zero (Nat.pow_pos (by omega)) hz; omega
          have hmul : ((4503599627370496 + d.mant) / 2 ^ (926 - d.exp)) * 2 ^ (926 - d.exp) =
              4503599627370496 + d.mant := by
            have hdm := Nat.div_add_mod (4503599627370496 + d.mant) (2 ^ (926 - d.exp))
            rw [hmod, Nat.add_zero, Nat.mul_comm] at hdm
            exact hdm
          have h925 : (2 : Nat) ^ 925 = 2 ^ (926 - d.exp) * 2 ^ (d.exp - 1) := by
            rw [(Nat.pow_add 2 (926 - d.exp) (d.exp - 1)).symm,
              show 926 - d.exp + (d.exp - 1) = 925 by omega]
          unfold Float32.toIEEEValue Float64.toIEEEValue
          simp only [he0, he2047, ↓reduceIte]
          simp only [hdiv_pos, ↓reduceIte, IEEEValue.finiteNz.injEq, true_and]
          rw [h925, ← Nat.mul_assoc, hmul]
        · simp [hmod] at hn
      · by_cases hnorm : 897 ≤ d.exp ∧ d.exp ≤ 1150
        · simp only [he0, he2047, hsub, hnorm, and_self, ↓reduceIte, ↓reduceDIte] at hn
          by_cases hmod : d.mant % 536870912 = 0
          · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            have he32_0 : d.exp - 896 ≠ 0 := by omega
            have he32_255 : d.exp - 896 ≠ 255 := by omega
            unfold Float32.toIEEEValue Float64.toIEEEValue
            simp only [he0, he2047, ↓reduceIte]
            simp only [he32_0, he32_255, ↓reduceIte, IEEEValue.finiteNz.injEq, true_and]
            have hcoef : (8388608 + d.mant / 536870912) * 536870912 = 4503599627370496 + d.mant := by omega
            have hpow : (2 : Nat) ^ (d.exp - 896 + 924) = 536870912 * 2 ^ (d.exp - 1) := by
              have hexp_eq : d.exp - 896 + 924 = 29 + (d.exp - 1) := by omega
              rw [hexp_eq, Nat.pow_add]
            rw [hpow, ← Nat.mul_assoc, hcoef]
          · simp [hmod] at hn
        · simp [he0, he2047, hsub, hnorm] at hn

/-- **Exact characterization of `narrow32To16?`:** `narrow32To16? s = some h`
iff `h` has the same `IEEEValue` as `s` (equivalently `widen16To32 h = s`). -/
theorem narrow32To16?_eq_some_iff {s : Float32} {h : Float16} :
    narrow32To16? s = some h ↔ h.toIEEEValue = s.toIEEEValue := by
  constructor
  · exact narrow32To16?_sound
  · intro hv
    have hs : s = widen16To32 h :=
      Float32.toIEEEValue_injective (by rw [widen16To32_toIEEEValue, hv])
    rw [hs, narrow32To16?_widen16To32]

theorem narrow32To16?_eq_none_iff {s : Float32} :
    narrow32To16? s = none ↔ ∀ h : Float16, h.toIEEEValue ≠ s.toIEEEValue := by
  cases hn : narrow32To16? s with
  | none =>
    simp only [true_iff]
    intro h hv
    have := narrow32To16?_eq_some_iff.mpr hv
    rw [hn] at this; cases this
  | some h₀ =>
    simp only [reduceCtorEq, false_iff]
    intro hall
    exact hall h₀ (narrow32To16?_sound hn)

/-- **Exact characterization of `narrow64To32?`:** `narrow64To32? d = some s`
iff `s` has the same `IEEEValue` as `d` (equivalently `widen32To64 s = d`). -/
theorem narrow64To32?_eq_some_iff {d : Float64} {s : Float32} :
    narrow64To32? d = some s ↔ s.toIEEEValue = d.toIEEEValue := by
  constructor
  · exact narrow64To32?_sound
  · intro hv
    have hd : d = widen32To64 s :=
      Float64.toIEEEValue_injective (by rw [widen32To64_toIEEEValue, hv])
    rw [hd, narrow64To32?_widen32To64]

theorem narrow64To32?_eq_none_iff {d : Float64} :
    narrow64To32? d = none ↔ ∀ s : Float32, s.toIEEEValue ≠ d.toIEEEValue := by
  cases hn : narrow64To32? d with
  | none =>
    simp only [true_iff]
    intro s hv
    have := narrow64To32?_eq_some_iff.mpr hv
    rw [hn] at this; cases this
  | some s₀ =>
    simp only [reduceCtorEq, false_iff]
    intro hall
    exact hall s₀ (narrow64To32?_sound hn)

/-- **Exact characterization of stepwise `narrow64To16?` (§4.2.1):**
`narrow64To16? d = some h` iff `h.toIEEEValue = d.toIEEEValue`. -/
theorem narrow64To16?_eq_some_iff {d : Float64} {h : Float16} :
    narrow64To16? d = some h ↔ h.toIEEEValue = d.toIEEEValue := by
  constructor
  · intro hn
    unfold narrow64To16? Option.bind at hn
    cases hs : narrow64To32? d with
    | none => simp [hs] at hn
    | some s =>
      simp only [hs] at hn
      exact (narrow32To16?_sound hn).trans (narrow64To32?_sound hs)
  · intro hv
    have hd : d = widen16To64 h :=
      Float64.toIEEEValue_injective (by rw [widen16To64_toIEEEValue, hv])
    rw [hd, narrow64To16?_widen16To64]

/-! ## §4.1 Preferred Float Serialization (shortest width preserving `IEEEValue`) -/

/-- Select the shortest IEEE 754 representation preserving `f.toIEEEValue`
via RFC 8949 §4.1 / §4.2.1 stepwise `binary64 → binary32 → binary16` narrowing. -/
def preferredFloat : CborFloat → CborFloat
  | .half h => .half h
  | .single s =>
    match narrow32To16? s with
    | some h => .half h
    | none => .single s
  | .double d =>
    match narrow64To32? d with
    | some s =>
      match narrow32To16? s with
      | some h => .half h
      | none => .single s
    | none => .double d

/-- Whether `f` is already in §4.1 preferred shortest-float form. -/
def isPreferredFloat (f : CborFloat) : Bool :=
  match f with
  | .half _ => true
  | .single s => (narrow32To16? s).isNone
  | .double d => (narrow64To32? d).isNone

/-- Encode a float in §4.1 preferred shortest-width form. -/
def encodeFloatPreferred (f : CborFloat) : List UInt8 :=
  encodeFloat (preferredFloat f)

/-- Decode a float requiring §4.1 preferred shortest-width serialization
(rejects non-canonical float widths). -/
def decodeFloatPreferred (bs : List UInt8) : Option CborFloat :=
  match decodeFloat bs with
  | some f => if isPreferredFloat f then some f else none
  | none => none

theorem preferredFloat_toIEEEValue (f : CborFloat) :
    (preferredFloat f).toIEEEValue = f.toIEEEValue := by
  cases f with
  | half h => rfl
  | single s =>
    simp only [preferredFloat]
    cases hn : narrow32To16? s with
    | none => rfl
    | some h => exact narrow32To16?_sound hn
  | double d =>
    simp only [preferredFloat]
    cases hn64 : narrow64To32? d with
    | none => rfl
    | some s =>
      simp only
      cases hn32 : narrow32To16? s with
      | none => exact narrow64To32?_sound hn64
      | some h => exact (narrow32To16?_sound hn32).trans (narrow64To32?_sound hn64)

theorem isPreferredFloat_preferredFloat (f : CborFloat) :
    isPreferredFloat (preferredFloat f) = true := by
  cases f with
  | half h => rfl
  | single s =>
    simp only [preferredFloat]
    cases hn : narrow32To16? s <;> simp [isPreferredFloat, hn]
  | double d =>
    simp only [preferredFloat]
    cases hn64 : narrow64To32? d with
    | none => simp [isPreferredFloat, hn64]
    | some s =>
      simp only
      cases hn32 : narrow32To16? s <;> simp [isPreferredFloat, hn32]

theorem isPreferredFloat_iff_eq_preferredFloat (f : CborFloat) :
    isPreferredFloat f = true ↔ preferredFloat f = f := by
  cases f with
  | half h => simp [isPreferredFloat, preferredFloat]
  | single s =>
    simp only [isPreferredFloat, preferredFloat]
    cases hn : narrow32To16? s <;> simp
  | double d =>
    simp only [isPreferredFloat, preferredFloat]
    cases hn64 : narrow64To32? d with
    | none => simp
    | some s =>
      simp only [Option.isNone]
      cases hn32 : narrow32To16? s <;> simp

theorem preferredFloat_idem (f : CborFloat) :
    preferredFloat (preferredFloat f) = preferredFloat f :=
  (isPreferredFloat_iff_eq_preferredFloat _).mp (isPreferredFloat_preferredFloat f)

/-- `preferredFloat` depends only on `toIEEEValue`: any two floats representing
the same IEEE 754 value have the exact same preferred shortest representation. -/
theorem preferredFloat_eq_of_toIEEEValue_eq {f g : CborFloat}
    (h : f.toIEEEValue = g.toIEEEValue) : preferredFloat f = preferredFloat g := by
  have hd : f.toFloat64 = g.toFloat64 :=
    Float64.toIEEEValue_injective (by rw [CborFloat.toFloat64_toIEEEValue, CborFloat.toFloat64_toIEEEValue, h])
  have key : ∀ x : CborFloat, preferredFloat x = preferredFloat (.double x.toFloat64) := by
    intro x
    cases x with
    | half xh =>
      simp [CborFloat.toFloat64, widen16To64, preferredFloat, narrow64To32?_widen32To64,
        narrow32To16?_widen16To32]
    | single xs =>
      simp only [CborFloat.toFloat64, preferredFloat, narrow64To32?_widen32To64]
    | double xd => rfl
  rw [key f, key g, hd]

/-- **Shortest-wire optimality (§4.1):** among all `CborFloat`s representing the
same `IEEEValue`, `preferredFloat f` strictly minimizes `(encodeFloat g).length`,
with equality iff `g = preferredFloat f`. -/
theorem encodeFloatPreferred_shortest {f g : CborFloat}
    (hv : g.toIEEEValue = f.toIEEEValue) :
    (encodeFloatPreferred f).length ≤ (encodeFloat g).length ∧
      ((encodeFloatPreferred f).length = (encodeFloat g).length ↔ g = preferredFloat f) := by
  have hpg : preferredFloat g = preferredFloat f := preferredFloat_eq_of_toIEEEValue_eq hv
  rw [encodeFloatPreferred, ← hpg]
  cases g with
  | half gh =>
    simp [preferredFloat]
  | single gs =>
    simp only [preferredFloat]
    cases hn : narrow32To16? gs with
    | none => simp
    | some h =>
      simp [encodeFloat, encodeFloat16_length, encodeFloat32_length]
  | double gd =>
    simp only [preferredFloat]
    cases hn64 : narrow64To32? gd with
    | none => simp
    | some s =>
      simp only
      cases hn32 : narrow32To16? s with
      | none => simp [encodeFloat, encodeFloat32_length, encodeFloat64_length]
      | some h => simp [encodeFloat, encodeFloat16_length, encodeFloat64_length]

theorem decodeFloatPreferred_encodeFloatPreferred (f : CborFloat) :
    decodeFloatPreferred (encodeFloatPreferred f) = some (preferredFloat f) := by
  simp [decodeFloatPreferred, encodeFloatPreferred, decodeFloat_encodeFloat,
    isPreferredFloat_preferredFloat]

theorem decodeFloatPreferred_eq_some_iff {bs : List UInt8} {f : CborFloat} :
    decodeFloatPreferred bs = some f ↔ bs = encodeFloat f ∧ isPreferredFloat f = true := by
  constructor
  · intro h
    unfold decodeFloatPreferred at h
    cases hd : decodeFloat bs with
    | none => simp [hd] at h
    | some g =>
      simp only [hd] at h
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h; subst h
        exact ⟨decodeFloat_eq_some_iff.mp hd, hp⟩
      · simp at h
  · rintro ⟨rfl, hp⟩
    simp [decodeFloatPreferred, decodeFloat_encodeFloat, hp]

/-! ## §4.2.1 / §4.2.2 Core Deterministic Float Serialization (Canonical NaN `0xf97e00`) -/

/-- Core deterministic float canonicalization (§4.2.1 + §4.2.2):
* every NaN (regardless of width, sign, quiet/signaling bit, or payload)
  canonicalizes to quiet half-precision `0xf97e00` (`Float16.canonicalNaN`);
* every non-NaN float narrows via `preferredFloat` (`binary64 → binary32 → binary16`),
  preserving signed zero (`-0.0` = `0xf98000` vs. `0.0` = `0xf90000`) and
  narrowing `±Infinity` to `0xf97c00` / `0xf9fc00`. -/
def canonicalFloatDet (f : CborFloat) : CborFloat :=
  if f.isNaN then .half Float16.canonicalNaN
  else preferredFloat f

/-- Whether `f` is in §4.2.1 / §4.2.2 core deterministic float form. -/
def isDeterministicFloat (f : CborFloat) : Bool :=
  if f.isNaN then f == .half Float16.canonicalNaN
  else isPreferredFloat f

/-- Encode `f` in §4.2.1 / §4.2.2 core deterministic float form. -/
def encodeFloatDeterministic (f : CborFloat) : List UInt8 :=
  encodeFloat (canonicalFloatDet f)

/-- Decode a float requiring §4.2.1 / §4.2.2 core deterministic serialization
(rejects non-preferred float widths AND any NaN other than `0xf97e00`). -/
def decodeFloatDeterministic (bs : List UInt8) : Option CborFloat :=
  match decodeFloat bs with
  | some f => if isDeterministicFloat f then some f else none
  | none => none

theorem isNaN_preferredFloat (f : CborFloat) :
    (preferredFloat f).isNaN = f.isNaN := by
  have hv := preferredFloat_toIEEEValue f
  have hchar : ∀ x : CborFloat, (x.isNaN = true) ↔ ∃ s sig, x.toIEEEValue = .nan s sig := by
    intro x
    cases x with
    | half h =>
      by_cases he0 : h.exp = 0 <;> by_cases he31 : h.exp = 31 <;> by_cases hm : h.mant = 0 <;>
        simp [-Nat.reducePow, CborFloat.isNaN, Float16.isNaN, CborFloat.toIEEEValue,
          Float16.toIEEEValue, he0, he31, hm]
    | single s =>
      by_cases he0 : s.exp = 0 <;> by_cases he255 : s.exp = 255 <;> by_cases hm : s.mant = 0 <;>
        simp [-Nat.reducePow, CborFloat.isNaN, Float32.isNaN, CborFloat.toIEEEValue,
          Float32.toIEEEValue, he0, he255, hm]
    | double d =>
      by_cases he0 : d.exp = 0 <;> by_cases he2047 : d.exp = 2047 <;> by_cases hm : d.mant = 0 <;>
        simp [-Nat.reducePow, CborFloat.isNaN, Float64.isNaN, CborFloat.toIEEEValue,
          Float64.toIEEEValue, he0, he2047, hm]
  apply Bool.eq_iff_iff.mpr
  rw [hchar, hchar, hv]

theorem isDeterministicFloat_canonicalFloatDet (f : CborFloat) :
    isDeterministicFloat (canonicalFloatDet f) = true := by
  cases hnan : f.isNaN with
  | true =>
    simp only [canonicalFloatDet, hnan, ↓reduceIte]
    rfl
  | false =>
    have hpnan : (preferredFloat f).isNaN = false := by rw [isNaN_preferredFloat, hnan]
    simp [canonicalFloatDet, hnan, isDeterministicFloat, hpnan, isPreferredFloat_preferredFloat]

theorem isDeterministicFloat_iff_eq_canonicalFloatDet (f : CborFloat) :
    isDeterministicFloat f = true ↔ canonicalFloatDet f = f := by
  cases hnan : f.isNaN with
  | true =>
    simp only [isDeterministicFloat, canonicalFloatDet, hnan, ↓reduceIte, beq_iff_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  | false =>
    simp only [isDeterministicFloat, canonicalFloatDet, hnan, Bool.false_eq_true, ↓reduceIte]
    exact isPreferredFloat_iff_eq_preferredFloat f

theorem canonicalFloatDet_idem (f : CborFloat) :
    canonicalFloatDet (canonicalFloatDet f) = canonicalFloatDet f :=
  (isDeterministicFloat_iff_eq_canonicalFloatDet _).mp (isDeterministicFloat_canonicalFloatDet f)

theorem isDeterministicFloat_imp_isPreferredFloat {f : CborFloat}
    (h : isDeterministicFloat f = true) : isPreferredFloat f = true := by
  cases hnan : f.isNaN with
  | true =>
    simp only [isDeterministicFloat, hnan, ↓reduceIte, beq_iff_eq] at h
    subst h; rfl
  | false =>
    simpa [isDeterministicFloat, hnan] using h

theorem encodeFloatDeterministic_nan {f : CborFloat} (h : f.isNaN = true) :
    encodeFloatDeterministic f = [0xf9, 0x7e, 0x00] := by
  simp [encodeFloatDeterministic, canonicalFloatDet, h]; rfl

theorem decodeFloatDeterministic_encodeFloatDeterministic (f : CborFloat) :
    decodeFloatDeterministic (encodeFloatDeterministic f) = some (canonicalFloatDet f) := by
  simp [decodeFloatDeterministic, encodeFloatDeterministic, decodeFloat_encodeFloat,
    isDeterministicFloat_canonicalFloatDet]

theorem decodeFloatDeterministic_eq_some_iff {bs : List UInt8} {f : CborFloat} :
    decodeFloatDeterministic bs = some f ↔ bs = encodeFloat f ∧ isDeterministicFloat f = true := by
  constructor
  · intro h
    unfold decodeFloatDeterministic at h
    cases hd : decodeFloat bs with
    | none => simp [hd] at h
    | some g =>
      simp only [hd] at h
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h; subst h
        exact ⟨decodeFloat_eq_some_iff.mp hd, hp⟩
      · simp at h
  · rintro ⟨rfl, hp⟩
    simp [decodeFloatDeterministic, decodeFloat_encodeFloat, hp]

/-! ## IEEE 754 Round-to-Nearest-Ties-to-Even Lossy Narrowing & Boundary Cases (§2.4) -/

/-- Integer division `x / 2^sh` rounded to nearest, ties to even (IEEE 754 RNE). -/
def divPow2RNE (x sh : Nat) : Nat :=
  if sh = 0 then x
  else
    let q := x / 2 ^ sh
    let r := x % 2 ^ sh
    let half := 2 ^ (sh - 1)
    if half < r || (r == half && q % 2 == 1) then q + 1 else q

theorem divPow2RNE_of_mod_zero {x sh : Nat} (hsh : 0 < sh) (hm : x % 2 ^ sh = 0) :
    divPow2RNE x sh = x / 2 ^ sh := by
  have h0 : sh ≠ 0 := by omega
  have hpos : 0 < 2 ^ (sh - 1) := Nat.pow_pos (by omega)
  simp [divPow2RNE, h0, hm]
  omega

/-- IEEE 754 round-to-nearest-even conversion from `binary64` to `binary32`.
Values outside `binary32`'s precision or dynamic range suffer:
* **precision narrowing** (`divPow2RNE` on low 29 significand bits),
* **exponent overflow** to `±Infinity` (`exp64 ≥ 1151`, or carry out of `exp64 = 1150`), or
* **exponent underflow** to `±0.0` (`exp64 ≤ 872`, or subnormal `divPow2RNE` rounding to `0`). -/
def round64To32 (d : Float64) : Float32 :=
  if _he0 : d.exp = 0 then
    ⟨d.sign, 0, 0, by omega, by omega⟩
  else if _he2047 : d.exp = 2047 then
    if d.mant = 0 then ⟨d.sign, 255, 0, by omega, by omega⟩
    else
      ⟨d.sign, 255, 4194304 + (d.mant / 536870912) % 4194304, by omega, by omega⟩
  else if _hle872 : d.exp ≤ 872 then
    ⟨d.sign, 0, 0, by omega, by omega⟩
  else if _hle896 : d.exp ≤ 896 then
    if hm : divPow2RNE (4503599627370496 + d.mant) (926 - d.exp) < 8388608 then
      ⟨d.sign, 0, divPow2RNE (4503599627370496 + d.mant) (926 - d.exp), by omega, hm⟩
    else ⟨d.sign, 1, 0, by omega, by omega⟩
  else if _hle1150 : d.exp ≤ 1150 then
    if hm : divPow2RNE d.mant 29 < 8388608 then
      ⟨d.sign, d.exp - 896, divPow2RNE d.mant 29, by omega, hm⟩
    else if d.exp = 1150 then ⟨d.sign, 255, 0, by omega, by omega⟩
    else ⟨d.sign, d.exp - 895, 0, by omega, by omega⟩
  else
    ⟨d.sign, 255, 0, by omega, by omega⟩

/-- IEEE 754 round-to-nearest-even conversion from `binary32` to `binary16`. -/
def round32To16 (s : Float32) : Float16 :=
  if _he0 : s.exp = 0 then
    ⟨s.sign, 0, 0, by omega, by omega⟩
  else if _he255 : s.exp = 255 then
    if s.mant = 0 then ⟨s.sign, 31, 0, by omega, by omega⟩
    else
      ⟨s.sign, 31, 512 + (s.mant / 8192) % 512, by omega, by omega⟩
  else if _hle101 : s.exp ≤ 101 then
    ⟨s.sign, 0, 0, by omega, by omega⟩
  else if _hle112 : s.exp ≤ 112 then
    if hm : divPow2RNE (8388608 + s.mant) (126 - s.exp) < 1024 then
      ⟨s.sign, 0, divPow2RNE (8388608 + s.mant) (126 - s.exp), by omega, hm⟩
    else ⟨s.sign, 1, 0, by omega, by omega⟩
  else if _hle142 : s.exp ≤ 142 then
    if hm : divPow2RNE s.mant 13 < 1024 then
      ⟨s.sign, s.exp - 112, divPow2RNE s.mant 13, by omega, hm⟩
    else if s.exp = 142 then ⟨s.sign, 31, 0, by omega, by omega⟩
    else ⟨s.sign, s.exp - 111, 0, by omega, by omega⟩
  else
    ⟨s.sign, 31, 0, by omega, by omega⟩

/-- Every finite or infinite `Float64` that admits an exact `Float32` narrowing
is preserved identically by IEEE 754 RNE `round64To32`. -/
theorem round64To32_eq_of_narrow64To32? {d : Float64} {s : Float32}
    (hfin : d.isNaN = false) (hn : narrow64To32? d = some s) :
    round64To32 d = s := by
  have he := d.hexp; have hm := d.hmant
  unfold narrow64To32? at hn
  by_cases he0 : d.exp = 0
  · simp only [he0, ↓reduceIte] at hn
    by_cases hm0 : d.mant = 0
    · simp only [hm0, ↓reduceIte, Option.some.injEq] at hn
      subst hn; simp [round64To32, he0]
    · simp [hm0] at hn
  · by_cases he2047 : d.exp = 2047
    · by_cases hm0 : d.mant = 0
      · simp [he2047, hm0] at hn
        subst hn; simp [round64To32, he2047, hm0]
      · simp [Float64.isNaN, he2047, hm0] at hfin
    · by_cases hsub : 874 ≤ d.exp ∧ d.exp ≤ 896
      · simp only [he0, he2047, hsub, and_self, ↓reduceIte, ↓reduceDIte] at hn
        by_cases hmod : (4503599627370496 + d.mant) % (2 ^ (926 - d.exp)) = 0
        · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
          subst hn
          have hle1 : ¬ (d.exp ≤ 872) := by omega
          have hle2 : d.exp ≤ 896 := hsub.2
          have hrne : divPow2RNE (4503599627370496 + d.mant) (926 - d.exp) =
              (4503599627370496 + d.mant) / 2 ^ (926 - d.exp) :=
            divPow2RNE_of_mod_zero (by omega) hmod
          have hpow30 : 1073741824 ≤ 2 ^ (926 - d.exp) := by
            change 2 ^ 30 ≤ 2 ^ (926 - d.exp)
            exact Nat.pow_le_pow_right (by omega) (by omega)
          have hlt : (4503599627370496 + d.mant) / 2 ^ (926 - d.exp) < 8388608 :=
            Nat.div_lt_of_lt_mul (by omega)
          simp [round64To32, he0, he2047, hle1, hle2, hrne, hlt]
        · simp [hmod] at hn
      · by_cases hnorm : 897 ≤ d.exp ∧ d.exp ≤ 1150
        · simp only [he0, he2047, hsub, hnorm, and_self, ↓reduceIte, ↓reduceDIte] at hn
          by_cases hmod : d.mant % 536870912 = 0
          · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            have hle1 : ¬ (d.exp ≤ 872) := by omega
            have hle2 : ¬ (d.exp ≤ 896) := by omega
            have hle3 : d.exp ≤ 1150 := hnorm.2
            have hrne : divPow2RNE d.mant 29 = d.mant / 536870912 :=
              divPow2RNE_of_mod_zero (by omega) hmod
            have hlt : d.mant / 536870912 < 8388608 := by omega
            simp [round64To32, he0, he2047, hle1, hle2, hle3, hrne, hlt]
          · simp [hmod] at hn
        · simp [he0, he2047, hsub, hnorm] at hn

/-- **Exact characterization of lossy vs. exact `round64To32` round-trip:**
for every non-NaN `d : Float64`, `widen32To64 (round64To32 d) = d` holds
**if and only if** `narrow64To32? d` succeeds (`≠ none`). When `narrow64To32? d = none`,
no `Float32` (including `round64To32 d`) widens back to `d`. -/
theorem widen32To64_round64To32_eq_iff {d : Float64} (hfin : d.isNaN = false) :
    widen32To64 (round64To32 d) = d ↔ narrow64To32? d ≠ none := by
  constructor
  · intro hw hnone
    have hv : (round64To32 d).toIEEEValue = d.toIEEEValue := by
      rw [← widen32To64_toIEEEValue, hw]
    exact (narrow64To32?_eq_none_iff.mp hnone) (round64To32 d) hv
  · intro hsome
    cases hn : narrow64To32? d with
    | none => exact absurd hn hsome
    | some s =>
      rw [round64To32_eq_of_narrow64To32? hfin hn]
      exact Float64.toIEEEValue_injective (by rw [widen32To64_toIEEEValue, narrow64To32?_sound hn])

/-- Every finite or infinite `Float32` that admits an exact `Float16` narrowing
is preserved identically by IEEE 754 RNE `round32To16`. -/
theorem round32To16_eq_of_narrow32To16? {s : Float32} {h : Float16}
    (hfin : s.isNaN = false) (hn : narrow32To16? s = some h) :
    round32To16 s = h := by
  have he := s.hexp; have hm := s.hmant
  unfold narrow32To16? at hn
  by_cases he0 : s.exp = 0
  · simp only [he0, ↓reduceIte] at hn
    by_cases hm0 : s.mant = 0
    · simp only [hm0, ↓reduceIte, Option.some.injEq] at hn
      subst hn; simp [round32To16, he0]
    · simp [hm0] at hn
  · by_cases he255 : s.exp = 255
    · by_cases hm0 : s.mant = 0
      · simp [he255, hm0] at hn
        subst hn; simp [round32To16, he255, hm0]
      · simp [Float32.isNaN, he255, hm0] at hfin
    · by_cases hsub : 103 ≤ s.exp ∧ s.exp ≤ 112
      · simp only [he0, he255, hsub, and_self, ↓reduceIte, ↓reduceDIte] at hn
        by_cases hmod : (8388608 + s.mant) % (2 ^ (126 - s.exp)) = 0
        · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
          subst hn
          have hle1 : ¬ (s.exp ≤ 101) := by omega
          have hle2 : s.exp ≤ 112 := hsub.2
          have hrne : divPow2RNE (8388608 + s.mant) (126 - s.exp) =
              (8388608 + s.mant) / 2 ^ (126 - s.exp) :=
            divPow2RNE_of_mod_zero (by omega) hmod
          have hpow14 : 16384 ≤ 2 ^ (126 - s.exp) := by
            change 2 ^ 14 ≤ 2 ^ (126 - s.exp)
            exact Nat.pow_le_pow_right (by omega) (by omega)
          have hlt : (8388608 + s.mant) / 2 ^ (126 - s.exp) < 1024 :=
            Nat.div_lt_of_lt_mul (by omega)
          simp [round32To16, he0, he255, hle1, hle2, hrne, hlt]
        · simp [hmod] at hn
      · by_cases hnorm : 113 ≤ s.exp ∧ s.exp ≤ 142
        · simp only [he0, he255, hsub, hnorm, and_self, ↓reduceIte, ↓reduceDIte] at hn
          by_cases hmod : s.mant % 8192 = 0
          · simp only [hmod, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            have hle1 : ¬ (s.exp ≤ 101) := by omega
            have hle2 : ¬ (s.exp ≤ 112) := by omega
            have hle3 : s.exp ≤ 142 := hnorm.2
            have hrne : divPow2RNE s.mant 13 = s.mant / 8192 :=
              divPow2RNE_of_mod_zero (by omega) hmod
            have hlt : s.mant / 8192 < 1024 := by omega
            simp [round32To16, he0, he255, hle1, hle2, hle3, hrne, hlt]
          · simp [hmod] at hn
        · simp [he0, he255, hsub, hnorm] at hn

/-- **Exact characterization of lossy vs. exact `round32To16` round-trip:**
for every non-NaN `s : Float32`, `widen16To32 (round32To16 s) = s` holds
**if and only if** `narrow32To16? s` succeeds (`≠ none`). When `narrow32To16? s = none`,
no `Float16` (including `round32To16 s`) widens back to `s`. -/
theorem widen16To32_round32To16_eq_iff {s : Float32} (hfin : s.isNaN = false) :
    widen16To32 (round32To16 s) = s ↔ narrow32To16? s ≠ none := by
  constructor
  · intro hw hnone
    have hv : (round32To16 s).toIEEEValue = s.toIEEEValue := by
      rw [← widen16To32_toIEEEValue, hw]
    exact (narrow32To16?_eq_none_iff.mp hnone) (round32To16 s) hv
  · intro hsome
    cases hn : narrow32To16? s with
    | none => exact absurd hn hsome
    | some h =>
      rw [round32To16_eq_of_narrow32To16? hfin hn]
      exact Float32.toIEEEValue_injective (by rw [widen16To32_toIEEEValue, narrow32To16?_sound hn])

/-! ### Explicit Boundary Witnesses (§2.4): Signed Zero, `±Infinity`, NaN Payloads, Subnormals, and Lossy Narrowing -/

/-- **Boundary 1 — Signed zero (`-0.0` vs. `0.0`):**
`0.0` (`0xf90000`) and `-0.0` (`0xf98000`) have distinct bit patterns, distinct
`IEEEValue`s, and distinct preferred/deterministic encodings, and `-0.0` in
`binary64`/`binary32` narrows to `0xf98000` (not `0xf90000`). -/
theorem signed_zero_boundary :
    encodeFloat16 Float16.posZero = [0xf9, 0x00, 0x00] ∧
    encodeFloat16 Float16.negZero = [0xf9, 0x80, 0x00] ∧
    Float16.posZero ≠ Float16.negZero ∧
    Float16.posZero.toIEEEValue ≠ Float16.negZero.toIEEEValue ∧
    encodeFloatPreferred (.double Float64.posZero) = [0xf9, 0x00, 0x00] ∧
    encodeFloatPreferred (.double Float64.negZero) = [0xf9, 0x80, 0x00] ∧
    encodeFloatDeterministic (.double Float64.posZero) = [0xf9, 0x00, 0x00] ∧
    encodeFloatDeterministic (.double Float64.negZero) = [0xf9, 0x80, 0x00] ∧
    decodeFloatPreferred [0xfa, 0x80, 0x00, 0x00, 0x00] = none ∧
    decodeFloatPreferred [0xfb, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h; cases h
  · intro h; simp [Float16.toIEEEValue, Float16.posZero, Float16.negZero] at h

/-- **Boundary 2 — `±Infinity` narrowing and non-preferred rejection:**
`binary64` and `binary32` `±Infinity` (Appendix A Rows 35, 37, 38, 40) narrow
to `0xf97c00` / `0xf9fc00` (Rows 32, 34) and are rejected by `decodeFloatPreferred`
and `decodeFloatDeterministic`. -/
theorem infinity_boundary :
    encodeFloatPreferred (.double Float64.posInf) = [0xf9, 0x7c, 0x00] ∧
    encodeFloatPreferred (.single Float32.posInf) = [0xf9, 0x7c, 0x00] ∧
    encodeFloatPreferred (.double Float64.negInf) = [0xf9, 0xfc, 0x00] ∧
    encodeFloatPreferred (.single Float32.negInf) = [0xf9, 0xfc, 0x00] ∧
    decodeFloatPreferred [0xfa, 0x7f, 0x80, 0x00, 0x00] = none ∧
    decodeFloatPreferred [0xfa, 0xff, 0x80, 0x00, 0x00] = none ∧
    decodeFloatPreferred [0xfb, 0x7f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    decodeFloatPreferred [0xfb, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `binary64` quiet NaN carrying a low-order payload bit (`0x7ff8000000000001`). -/
def nan64LowPayload : Float64 := ⟨false, 2047, 2251799813685249, by omega, by omega⟩

/-- A `binary16` signaling NaN (`0x7c01`, `exp = 31, mant = 1 < 512`). -/
def signalingNaN16 : Float16 := ⟨false, 31, 1, by omega, by omega⟩

/-- A negative `binary16` quiet NaN (`0xfe00`, `sign = true, exp = 31, mant = 512`). -/
def negQuietNaN16 : Float16 := ⟨true, 31, 512, by omega, by omega⟩

/-- **Boundary 3 — NaN payloads vs. deterministic NaN canonicalization (§4.1 vs. §4.2.1/§4.2.2):**
* `0xfa7fc00000` (Row 36) and `0xfb7ff8000000000000` (Row 39) have zero low
  significand bits and narrow to `0xf97e00` under **both** §4.1 and §4.2.1;
* `nan64LowPayload` (`0xfb7ff8000000000001`) has non-zero bit 0, so §4.1
  `preferredFloat` keeps all 9 bytes (`narrow64To32? = none`), whereas §4.2.1
  `encodeFloatDeterministic` canonicalizes it to `0xf97e00`;
* `signalingNaN16` (`0xf97c01`) and `negQuietNaN16` (`0xf9fe00`) are §4.1-preferred
  in `binary16`, yet rejected by `decodeFloatDeterministic` and canonicalized to
  `0xf97e00` by `encodeFloatDeterministic`. -/
theorem nan_payload_and_canonical_boundary :
    encodeFloatPreferred (.single Float32.quietNaN) = [0xf9, 0x7e, 0x00] ∧
    encodeFloatPreferred (.double Float64.quietNaN) = [0xf9, 0x7e, 0x00] ∧
    narrow64To32? nan64LowPayload = none ∧
    isPreferredFloat (.double nan64LowPayload) = true ∧
    encodeFloatPreferred (.double nan64LowPayload) =
      [0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01] ∧
    encodeFloatDeterministic (.double nan64LowPayload) = [0xf9, 0x7e, 0x00] ∧
    signalingNaN16.isSignalingNaN = true ∧
    signalingNaN16.isQuietNaN = false ∧
    isPreferredFloat (.half signalingNaN16) = true ∧
    decodeFloatDeterministic [0xf9, 0x7c, 0x01] = none ∧
    encodeFloatDeterministic (.half signalingNaN16) = [0xf9, 0x7e, 0x00] ∧
    decodeFloatDeterministic [0xf9, 0xfe, 0x00] = none ∧
    encodeFloatDeterministic (.half negQuietNaN16) = [0xf9, 0x7e, 0x00] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Boundary 4 — Subnormal round-trips and cross-width normal↔subnormal transitions:**
* `Float16.minPosSubnormal` (`2^-24`, `0xf90001`, Row 28) widens to normal
  `Float32` (`0xfa33800000`, `exp = 103, mant = 0`) and normal `Float64`
  (`0xfb3e70000000000000`, `exp = 999, mant = 0`), both of which narrow back to `0xf90001`;
* `Float32.minPosSubnormal` (`2^-149`, `0xfa00000001`) cannot narrow to `Float16`
  (`narrow32To16? = none`), widens to normal `Float64` (`exp = 874, mant = 0`),
  and narrows from `Float64` back to `0xfa00000001`;
* `Float64.minPosSubnormal` (`2^-1074`, `0xfb0000000000000001`) cannot narrow to
  `Float32` or `Float16` (`isPreferredFloat = true`). -/
theorem subnormal_boundary :
    (widen16To32 Float16.minPosSubnormal).isNormal = true ∧
    encodeFloat32 (widen16To32 Float16.minPosSubnormal) = [0xfa, 0x33, 0x80, 0x00, 0x00] ∧
    encodeFloatPreferred (.single (widen16To32 Float16.minPosSubnormal)) = [0xf9, 0x00, 0x01] ∧
    encodeFloatPreferred (.double (widen16To64 Float16.minPosSubnormal)) = [0xf9, 0x00, 0x01] ∧
    narrow32To16? Float32.minPosSubnormal = none ∧
    isPreferredFloat (.single Float32.minPosSubnormal) = true ∧
    (widen32To64 Float32.minPosSubnormal).isNormal = true ∧
    encodeFloatPreferred (.double (widen32To64 Float32.minPosSubnormal)) =
      [0xfa, 0x00, 0x00, 0x00, 0x01] ∧
    narrow64To32? Float64.minPosSubnormal = none ∧
    isPreferredFloat (.double Float64.minPosSubnormal) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `1.1` in IEEE 754 `binary64` (`0x3ff199999999999a`, Appendix A Row 22). -/
def float64OnePointOne : Float64 := Float64.ofBits 0x3ff199999999999a

/-- `1363896240.5` in IEEE 754 `binary64` (`0x41d452d9ec200000`, Appendix A Row 49 payload). -/
def float64EpochRow49 : Float64 := Float64.ofBits 0x41d452d9ec200000

/-- `1.0e+300` in IEEE 754 `binary64` (`0x7e37e43c8800759c`, Appendix A Row 27). -/
def float64OneE300 : Float64 := Float64.ofBits 0x7e37e43c8800759c

/-- `100000.0` in IEEE 754 `binary32` (`0x47c35000`, Appendix A Row 25). -/
def float32HundredThousand : Float32 := Float32.ofBits 0x47c35000

/-- `1.0 + 2^-11` in IEEE 754 `binary32` (`0x3f801000`, 12-bit significand). -/
def float32OnePlus2PowNeg11 : Float32 := Float32.ofBits 0x3f801000

/-- `2^-25` in IEEE 754 `binary32` (`0x33000000`, half of `Float16.minPosSubnormal`). -/
def float32TwoPowNeg25 : Float32 := Float32.ofBits 0x33000000

/-- **Boundary 5 — Values that do NOT round-trip through narrower widths (and why):**
1. **Precision narrowing (mantissa rounding, not a bug):**
   * `1.1` (`0xfb3ff199999999999a`, Row 22) has non-zero low 29 significand bits
     (`0x1999999a`), so `narrow64To32? = none`; RNE `round64To32` rounds to
     `0xfa3f8ccccd`, which widens to `0xfb3ff19999a0000000 ≠ 0xfb3ff199999999999a`.
   * `1363896240.5` (`0xfb41d452d9ec200000`, Row 49) requires a 32-bit odd
     significand (`2727792481`), exceeding `binary32`'s 24-bit precision;
     `narrow64To32? = none`, and `round64To32` rounds to `0xfa4ea296cf`.
   * `1.0 + 2^-11` (`0xfa3f801000`) requires 12 significand bits, exceeding
     `binary16`'s 11-bit precision; `round32To16` rounds (ties-to-even) to `1.0` (`0xf93c00`).
2. **Exponent overflow (`±Infinity`):**
   * `100000.0` (`0xfa47c35000`, Row 25) exceeds `Float16.maxFinite` (`65504.0`);
     `narrow32To16? = none`, and `round32To16` overflows to `+Infinity` (`0xf97c00`).
   * `1.0e+300` (`0xfb7e37e43c8800759c`, Row 27) exceeds `Float32.maxFinite`;
     `narrow64To32? = none`, and `round64To32` overflows to `+Infinity` (`0xfa7f800000`).
3. **Exponent underflow (`±0.0`):**
   * `2^-25` (`0xfa33000000`) is half of `Float16.minPosSubnormal` (`2^-24`);
     `narrow32To16? = none`, and `round32To16` underflows (ties-to-even) to `+0.0` (`0xf90000`).
   * `Float64.minPosSubnormal` (`2^-1074`) underflows under `round64To32` to `+0.0` (`0xfa00000000`). -/
theorem lossy_narrowing_boundary :
    -- Precision narrowing: 1.1 (Row 22)
    narrow64To32? float64OnePointOne = none ∧
    encodeFloat32 (round64To32 float64OnePointOne) = [0xfa, 0x3f, 0x8c, 0xcc, 0xcd] ∧
    encodeFloat64 (widen32To64 (round64To32 float64OnePointOne)) =
      [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0xa0, 0x00, 0x00, 0x00] ∧
    widen32To64 (round64To32 float64OnePointOne) ≠ float64OnePointOne ∧
    -- Precision narrowing: 1363896240.5 (Row 49 inner binary64)
    narrow64To32? float64EpochRow49 = none ∧
    encodeFloat32 (round64To32 float64EpochRow49) = [0xfa, 0x4e, 0xa2, 0x96, 0xcf] ∧
    widen32To64 (round64To32 float64EpochRow49) ≠ float64EpochRow49 ∧
    -- Precision narrowing: 1.0 + 2^-11 in binary32 -> binary16
    narrow32To16? float32OnePlus2PowNeg11 = none ∧
    encodeFloat16 (round32To16 float32OnePlus2PowNeg11) = [0xf9, 0x3c, 0x00] ∧
    widen16To32 (round32To16 float32OnePlus2PowNeg11) ≠ float32OnePlus2PowNeg11 ∧
    -- Exponent overflow: 100000.0 (Row 25) and 1.0e+300 (Row 27)
    narrow32To16? float32HundredThousand = none ∧
    round32To16 float32HundredThousand = Float16.posInf ∧
    narrow64To32? float64OneE300 = none ∧
    round64To32 float64OneE300 = Float32.posInf ∧
    -- Exponent underflow: 2^-25 (exact tie -> +0.0), s.exp = 102 non-tie -> 2^-24, and 2^-1074
    narrow32To16? float32TwoPowNeg25 = none ∧
    round32To16 float32TwoPowNeg25 = Float16.posZero ∧
    round32To16 (Float32.ofBits 0x33000001) = Float16.minPosSubnormal ∧
    round32To16 (Float32.ofBits 0x33400000) = Float16.minPosSubnormal ∧
    round64To32 Float64.minPosSubnormal = Float32.posZero := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    have := congrArg Float64.toBits h
    revert this; intro h'; cases h'
  · intro h
    have := congrArg Float64.toBits h
    revert this; intro h'; cases h'
  · intro h
    have := congrArg Float32.toBits h
    revert this; intro h'; cases h'

end Cbor.Rfc8949
