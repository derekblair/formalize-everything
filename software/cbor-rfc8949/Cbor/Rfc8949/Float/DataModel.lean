/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Float.Narrowing
import Cbor.Rfc8949.Vectors.AppendixF1

/-!
# RFC 8949 §2, §3.3, §4.2.1 & §5.6.1: Float Data-Model Equivalence, Full CBOR Grammar, and Truncated-Head Refusal

Without modifying Milestone 1's float-free modules, this module extends the M1
head/grammar/deterministic/equivalence stack to **full RFC 8949 CBOR**
(major types 0–7 including IEEE 754 `binary16` `0xf9`, `binary32` `0xfa`, and
`binary64` `0xfb`):

1. **Float data-model equivalence (`FloatKeyVal`, `FloatEquiv`, `canonFloatKey`,
   §2 & §5.6.1):**
   * serialization width (`0xf9` / `0xfa` / `0xfb`) is erased;
   * `-0.0` and `+0.0` are equivalent in the generic data model / map-key
     comparison (§5.6.1), even though their IEEE 754 bit patterns and
     preferred/deterministic serializations (`0xf98000` vs. `0xf90000`) differ;
   * finite nonzero floats are equivalent iff their exact `IEEEValue`s agree;
   * NaN values are equivalent iff their significands agree after right-zero
     extension to 52 trailing bits (§5.6.1).
2. **Full head & wire grammar (`FullHead`, `FullRawItem`, `FullItem`,
   `parseFullRaw`, `parseFullWellFormed`):**
   * `parseFullRaw_eq_some_iff : parseFullRaw bs = some r ↔ r.WF ∧ r.encode = bs`;
   * lossless embedding of M1 `RawItem` and `Item` preserving wire bytes;
   * complete 2/4/8-byte float heads accepted while all **94** Appendix F.1
     malformed byte sequences (including Group 1's 3 truncated float heads
     `f900`, `fa0000`, `fb000000`) are refused (`appendixF1_all_refused_full`).
3. **Full core deterministic codec (`encodeFullDeterministic`,
   `decodeFullDeterministic`) and full §5.6.1 `FullItem.Equiv`:**
   * conservative extension over M1 `Item.Equiv` (`FullItem.equiv_ofItem_iff`);
   * cross-type distinctness (`1.0` `0xf93c00` ≢ `1` `0x01`, `0.0` ≢ `0`,
     floats distinct from integers, tag-2/3 bignums, and simple values).
-/

namespace Cbor.Rfc8949

/-! ## §2 & §5.6.1 Float Data-Model Equivalence (`FloatKeyVal` & `FloatEquiv`) -/

/-- Canonical generic data-model value of an IEEE 754 float (RFC 8949 §2, §5.6.1):
* signed zeros collapse to `.zero` ("specifically, -0.0 is equal to 0.0");
* finite nonzero values are represented by their unique widened `binary64`
  triple `(sign, exp64, mant64)`;
* infinities are `.inf sign`;
* NaNs carry their 52-bit right-zero-extended trailing significand (`sig52`),
  ignoring serialization width and NaN sign bit (§5.6.1). -/
inductive FloatKeyVal where
  | zero
  | finiteNz (sign : Bool) (exp64 : Nat) (mant64 : Nat)
  | inf (sign : Bool)
  | nan (sig52 : Nat)
  deriving DecidableEq, Repr

/-- Extract the 52-bit right-zero-extended NaN trailing significand (§5.6.1). -/
def CborFloat.nanSignificand52 (f : CborFloat) : Nat :=
  f.toFloat64.mant

/-- Map any `CborFloat` to its §2 / §5.6.1 generic data-model representative. -/
def CborFloat.toKeyVal (f : CborFloat) : FloatKeyVal :=
  let d := f.toFloat64
  if d.exp = 0 then
    if d.mant = 0 then .zero
    else .finiteNz d.sign 0 d.mant
  else if d.exp = 2047 then
    if d.mant = 0 then .inf d.sign
    else .nan d.mant
  else
    .finiteNz d.sign d.exp d.mant

/-- RFC 8949 §2 / §5.6.1 generic data-model / map-key equivalence on floats. -/
def FloatEquiv (f g : CborFloat) : Prop :=
  f.toKeyVal = g.toKeyVal

instance : DecidableRel FloatEquiv := fun f g =>
  inferInstanceAs (Decidable (f.toKeyVal = g.toKeyVal))

theorem FloatEquiv.refl (f : CborFloat) : FloatEquiv f f := rfl
theorem FloatEquiv.symm {f g : CborFloat} (h : FloatEquiv f g) : FloatEquiv g f := Eq.symm h
theorem FloatEquiv.trans {f g h : CborFloat} (h₁ : FloatEquiv f g) (h₂ : FloatEquiv g h) :
    FloatEquiv f h := Eq.trans h₁ h₂

theorem floatEquiv_of_toIEEEValue_eq {f g : CborFloat}
    (h : f.toIEEEValue = g.toIEEEValue) : FloatEquiv f g := by
  unfold FloatEquiv CborFloat.toKeyVal
  have hd : f.toFloat64 = g.toFloat64 :=
    Float64.toIEEEValue_injective (by
      rw [CborFloat.toFloat64_toIEEEValue, CborFloat.toFloat64_toIEEEValue, h])
  rw [hd]

/-- §2 width erasure: widening `binary16 → binary32 → binary64` preserves `FloatEquiv`. -/
theorem floatEquiv_widen16To32 (h : Float16) :
    FloatEquiv (.half h) (.single (widen16To32 h)) :=
  floatEquiv_of_toIEEEValue_eq (widen16To32_toIEEEValue h).symm

theorem floatEquiv_widen32To64 (s : Float32) :
    FloatEquiv (.single s) (.double (widen32To64 s)) :=
  floatEquiv_of_toIEEEValue_eq (widen32To64_toIEEEValue s).symm

theorem floatEquiv_preferredFloat (f : CborFloat) :
    FloatEquiv f (preferredFloat f) :=
  floatEquiv_of_toIEEEValue_eq (preferredFloat_toIEEEValue f).symm

/-- §5.6.1 signed-zero equivalence: `-0.0` is equivalent to `0.0` in the generic
data model even though their preferred encodings (`0xf98000` vs. `0xf90000`) differ. -/
theorem floatEquiv_posZero_negZero :
    FloatEquiv (.half Float16.posZero) (.half Float16.negZero) ∧
    FloatEquiv (.single Float32.posZero) (.single Float32.negZero) ∧
    FloatEquiv (.double Float64.posZero) (.double Float64.negZero) ∧
    FloatEquiv (.double Float64.negZero) (.half Float16.posZero) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- §5.6.1 NaN equivalence: two NaN values are equivalent iff their 52-bit
right-zero-extended significands agree. -/
theorem floatEquiv_nan_iff {f g : CborFloat}
    (hf : f.isNaN = true) (hg : g.isNaN = true) :
    FloatEquiv f g ↔ f.nanSignificand52 = g.nanSignificand52 := by
  have hchar : ∀ x : CborFloat, x.isNaN = true →
      x.toFloat64.exp = 2047 ∧ x.toFloat64.mant ≠ 0 := by
    intro x hx
    cases x with
    | half h =>
      simp only [CborFloat.isNaN, Float16.isNaN, Bool.and_eq_true, beq_iff_eq,
        bne_iff_ne] at hx
      obtain ⟨he31, hm0⟩ := hx
      have hs32 : (widen16To32 h).exp = 255 ∧ (widen16To32 h).mant = h.mant * 8192 := by
        simp [widen16To32, he31, hm0]
      have hm32 : (widen16To32 h).mant ≠ 0 := by omega
      simp [CborFloat.toFloat64, widen16To64, widen32To64, hs32.1, hm32]
      omega
    | single s =>
      simp only [CborFloat.isNaN, Float32.isNaN, Bool.and_eq_true, beq_iff_eq,
        bne_iff_ne] at hx
      obtain ⟨he255, hm0⟩ := hx
      simp [CborFloat.toFloat64, widen32To64, he255, hm0]
      omega
    | double d =>
      simp only [CborFloat.isNaN, Float64.isNaN, Bool.and_eq_true, beq_iff_eq,
        bne_iff_ne] at hx
      exact hx
  obtain ⟨hfe, hfm⟩ := hchar f hf
  obtain ⟨hge, hgm⟩ := hchar g hg
  unfold FloatEquiv CborFloat.toKeyVal CborFloat.nanSignificand52
  simp [hfe, hge, hfm, hgm]

/-- Canonical `CborFloat` representative for §5.6.1 `FullItem.canon`:
maps `±0.0` to `+0.0` (`0xf90000`), clears the sign bit on NaNs before
shortest-width narrowing, and narrows all other floats via `preferredFloat`. -/
def canonFloatKey (f : CborFloat) : CborFloat :=
  let d := f.toFloat64
  if d.exp == 0 && d.mant == 0 then
    .half Float16.posZero
  else if d.exp == 2047 && d.mant != 0 then
    preferredFloat (.double ⟨false, 2047, d.mant, by omega, d.hmant⟩)
  else
    preferredFloat (.double d)

theorem isPreferredFloat_canonFloatKey (f : CborFloat) :
    isPreferredFloat (canonFloatKey f) = true := by
  unfold canonFloatKey
  simp only
  split
  · rfl
  · split <;> exact isPreferredFloat_preferredFloat _

private def canonFloatKey64 (d : Float64) : CborFloat :=
  if d.exp == 0 && d.mant == 0 then
    .half Float16.posZero
  else if d.exp == 2047 && d.mant != 0 then
    preferredFloat (.double ⟨false, 2047, d.mant, by omega, d.hmant⟩)
  else
    preferredFloat (.double d)

private def keyVal64 (d : Float64) : FloatKeyVal :=
  if d.exp = 0 then
    if d.mant = 0 then .zero
    else .finiteNz d.sign 0 d.mant
  else if d.exp = 2047 then
    if d.mant = 0 then .inf d.sign
    else .nan d.mant
  else
    .finiteNz d.sign d.exp d.mant

private theorem canonFloatKey64_toIEEEValue_not_zero {d : Float64}
    (hnz : ¬ (d.exp = 0 ∧ d.mant = 0)) :
    (if d.exp == 2047 && d.mant != 0 then
        preferredFloat (.double ⟨false, 2047, d.mant, by omega, d.hmant⟩)
      else preferredFloat (.double d)).toIEEEValue ≠
      Float16.posZero.toIEEEValue := by
  by_cases hnan : (d.exp == 2047 && d.mant != 0) = true
  · simp only [hnan, ↓reduceIte, preferredFloat_toIEEEValue]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hnan
    simp [CborFloat.toIEEEValue, Float64.toIEEEValue, Float16.toIEEEValue, Float16.posZero,
      hnan.2]
  · have hfnan : (d.exp == 2047 && d.mant != 0) = false := Bool.eq_false_iff.mpr hnan
    simp only [hfnan, Bool.false_eq_true, ↓reduceIte, preferredFloat_toIEEEValue]
    by_cases he0 : d.exp = 0
    · have hm0 : d.mant ≠ 0 := fun hm => hnz ⟨he0, hm⟩
      simp [CborFloat.toIEEEValue, Float64.toIEEEValue, Float16.toIEEEValue, Float16.posZero,
        he0, hm0]
    · by_cases he2047 : d.exp = 2047
      · by_cases hm0 : d.mant = 0 <;>
          simp [CborFloat.toIEEEValue, Float64.toIEEEValue, Float16.toIEEEValue, Float16.posZero,
            he2047, hm0]
      · simp [-Nat.reducePow, CborFloat.toIEEEValue, Float64.toIEEEValue,
          Float16.toIEEEValue, Float16.posZero, he0, he2047]

theorem canonFloatKey_eq_iff (f g : CborFloat) :
    canonFloatKey f = canonFloatKey g ↔ FloatEquiv f g := by
  change canonFloatKey64 f.toFloat64 = canonFloatKey64 g.toFloat64 ↔
    keyVal64 f.toFloat64 = keyVal64 g.toFloat64
  generalize f.toFloat64 = df, g.toFloat64 = dg
  constructor
  · intro hc
    unfold canonFloatKey64 at hc
    by_cases hfz : df.exp = 0 ∧ df.mant = 0
    · have hfz_b : (df.exp == 0 && df.mant == 0) = true := by simp [hfz.1, hfz.2]
      simp only [hfz_b, ↓reduceIte] at hc
      by_cases hgz : dg.exp = 0 ∧ dg.mant = 0
      · simp [keyVal64, hfz.1, hfz.2, hgz.1, hgz.2]
      · have hgz_b : (dg.exp == 0 && dg.mant == 0) = false := by
          apply Bool.eq_false_iff.mpr
          simp [Bool.and_eq_true, beq_iff_eq]; exact fun a b => hgz ⟨a, b⟩
        simp only [hgz_b, Bool.false_eq_true, ↓reduceIte] at hc
        have hv := congrArg CborFloat.toIEEEValue hc.symm
        exact False.elim (canonFloatKey64_toIEEEValue_not_zero hgz hv)
    · have hfz_b : (df.exp == 0 && df.mant == 0) = false := by
        apply Bool.eq_false_iff.mpr
        simp [Bool.and_eq_true, beq_iff_eq]; exact fun a b => hfz ⟨a, b⟩
      simp only [hfz_b, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hgz : dg.exp = 0 ∧ dg.mant = 0
      · have hgz_b : (dg.exp == 0 && dg.mant == 0) = true := by simp [hgz.1, hgz.2]
        simp only [hgz_b, ↓reduceIte] at hc
        have hv := congrArg CborFloat.toIEEEValue hc
        exact False.elim (canonFloatKey64_toIEEEValue_not_zero hfz hv)
      · have hgz_b : (dg.exp == 0 && dg.mant == 0) = false := by
          apply Bool.eq_false_iff.mpr
          simp [Bool.and_eq_true, beq_iff_eq]; exact fun a b => hgz ⟨a, b⟩
        simp only [hgz_b, Bool.false_eq_true, ↓reduceIte] at hc
        have hv := congrArg CborFloat.toIEEEValue hc
        cases hfn : (df.exp == 2047 && df.mant != 0) <;>
          cases hgn : (dg.exp == 2047 && dg.mant != 0)
        · simp only [hfn, hgn, Bool.false_eq_true, ↓reduceIte, preferredFloat_toIEEEValue] at hv
          have hdfg : df = dg := Float64.toIEEEValue_injective hv
          rw [hdfg]
        · simp only [hfn, hgn, Bool.false_eq_true, ↓reduceIte, preferredFloat_toIEEEValue] at hv
          have hgn' : dg.exp = 2047 ∧ dg.mant ≠ 0 := by
            simpa [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hgn
          by_cases hfe0 : df.exp = 0
          · have hfm0 : df.mant ≠ 0 := fun hm => hfz ⟨hfe0, hm⟩
            simp [CborFloat.toIEEEValue, Float64.toIEEEValue, hgn'.2, hfe0, hfm0] at hv
          · by_cases hfe2047 : df.exp = 2047
            · have hfm0 : df.mant = 0 := by
                by_cases hm : df.mant = 0
                · exact hm
                · have : (df.exp == 2047 && df.mant != 0) = true := by simp [hfe2047, hm]
                  rw [hfn] at this; cases this
              simp [CborFloat.toIEEEValue, Float64.toIEEEValue, hgn'.2, hfe2047, hfm0] at hv
            · simp [-Nat.reducePow, CborFloat.toIEEEValue, Float64.toIEEEValue,
                hgn'.2, hfe0, hfe2047] at hv
        · simp only [hfn, hgn, Bool.false_eq_true, ↓reduceIte, preferredFloat_toIEEEValue] at hv
          have hfn' : df.exp = 2047 ∧ df.mant ≠ 0 := by
            simpa [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hfn
          by_cases hge0 : dg.exp = 0
          · have hgm0 : dg.mant ≠ 0 := fun hm => hgz ⟨hge0, hm⟩
            simp [CborFloat.toIEEEValue, Float64.toIEEEValue, hfn'.2, hge0, hgm0] at hv
          · by_cases hge2047 : dg.exp = 2047
            · have hgm0 : dg.mant = 0 := by
                by_cases hm : dg.mant = 0
                · exact hm
                · have : (dg.exp == 2047 && dg.mant != 0) = true := by simp [hge2047, hm]
                  rw [hgn] at this; cases this
              simp [CborFloat.toIEEEValue, Float64.toIEEEValue, hfn'.2, hge2047, hgm0] at hv
            · simp [-Nat.reducePow, CborFloat.toIEEEValue, Float64.toIEEEValue,
                hfn'.2, hge0, hge2047] at hv
        · simp only [hfn, hgn, ↓reduceIte, preferredFloat_toIEEEValue] at hv
          have hfn' : df.exp = 2047 ∧ df.mant ≠ 0 := by
            simpa [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hfn
          have hgn' : dg.exp = 2047 ∧ dg.mant ≠ 0 := by
            simpa [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hgn
          simp [CborFloat.toIEEEValue, Float64.toIEEEValue, hfn'.2, hgn'.2] at hv
          simp [keyVal64, hfn'.1, hgn'.1, hgn'.2, hv]
  · intro heq
    unfold keyVal64 at heq
    unfold canonFloatKey64
    by_cases hfe0 : df.exp = 0 <;> by_cases hge0 : dg.exp = 0
    · by_cases hfm0 : df.mant = 0 <;> by_cases hgm0 : dg.mant = 0
      · simp [hfe0, hge0, hfm0, hgm0]
      · simp [hfe0, hge0, hfm0, hgm0] at heq
      · simp [hfe0, hge0, hfm0, hgm0] at heq
      · simp [hfe0, hge0, hfm0, hgm0] at heq
        have hdfg : df = dg := Float64.ext heq.1 (by omega) heq.2
        rw [hdfg]
    · by_cases hfm0 : df.mant = 0
      · by_cases hge2047 : dg.exp = 2047
        · by_cases hgm0 : dg.mant = 0 <;> simp [hfe0, hfm0, hge2047, hgm0] at heq
        · simp [hfe0, hge0, hfm0, hge2047] at heq
      · by_cases hge2047 : dg.exp = 2047
        · by_cases hgm0 : dg.mant = 0 <;> simp [hfe0, hfm0, hge2047, hgm0] at heq
        · simp [hfe0, hge0, hfm0, hge2047] at heq
          exact False.elim (hge0 heq.2.1.symm)
    · by_cases hgm0 : dg.mant = 0
      · by_cases hfe2047 : df.exp = 2047
        · by_cases hfm0 : df.mant = 0 <;> simp [hge0, hgm0, hfe2047, hfm0] at heq
        · simp [hfe0, hge0, hgm0, hfe2047] at heq
      · by_cases hfe2047 : df.exp = 2047
        · by_cases hfm0 : df.mant = 0 <;> simp [hge0, hgm0, hfe2047, hfm0] at heq
        · simp [hfe0, hge0, hgm0, hfe2047] at heq
    · by_cases hfe2047 : df.exp = 2047 <;> by_cases hge2047 : dg.exp = 2047
      · by_cases hfm0 : df.mant = 0 <;> by_cases hgm0 : dg.mant = 0
        · simp [hfe2047, hge2047, hfm0, hgm0] at heq
          have hdfg : df = dg := Float64.ext heq (by omega) (by omega)
          rw [hdfg]
        · simp [hfe2047, hge2047, hfm0, hgm0] at heq
        · simp [hfe2047, hge2047, hfm0, hgm0] at heq
        · simp [hfe2047, hge2047, hfm0, hgm0] at heq ⊢
          congr 2
          exact Float64.ext rfl rfl heq
      · by_cases hfm0 : df.mant = 0 <;> simp [hge0, hfe2047, hge2047, hfm0] at heq
      · by_cases hgm0 : dg.mant = 0 <;> simp [hfe0, hfe2047, hge2047, hgm0] at heq
      · simp [hfe0, hge0, hfe2047, hge2047] at heq
        have hdfg : df = dg := Float64.ext heq.1 heq.2.1 heq.2.2
        rw [hdfg]

/-! ## Full CBOR Head (`FullHead`) and Truncated-Head Refusal -/

/-- A decoded CBOR head across all major types 0–7, extending Milestone 1's
float-free `Head` with IEEE 754 `CborFloat` heads (`0xf9`, `0xfa`, `0xfb`). -/
inductive FullHead where
  | base (h : Head)
  | float (f : CborFloat)
  deriving DecidableEq, Repr

/-- Wire bytes of a `FullHead`. -/
def FullHead.bytes : FullHead → List UInt8
  | .base h => h.bytes
  | .float f => encodeFloat f

/-- Validity of a `FullHead` (every `CborFloat` is valid by bit-field bounds). -/
def FullHead.Valid : FullHead → Prop
  | .base h => h.Valid
  | .float _ => True

/-- Decode one full CBOR head (major types 0–7, including `0xf9`/`0xfa`/`0xfb`). -/
def decodeFullHead (bs : List UInt8) : Option (FullHead × List UInt8) :=
  match decodeFloatPrefix bs with
  | some (f, rest) => some (.float f, rest)
  | none =>
    match decodeHead bs with
    | some (h, rest) => some (.base h, rest)
    | none => none

private theorem head_bytes_not_float {h : Head} (hv : h.Valid) (rest : List UInt8) :
    decodeFloatPrefix (h.bytes ++ rest) = none := by
  have notFloatByte : ∀ (m ai : Nat) (tl : List UInt8),
      m * 32 + ai < 256 → m * 32 + ai ≠ 249 → m * 32 + ai ≠ 250 → m * 32 + ai ≠ 251 →
      decodeFloatPrefix (UInt8.ofNat (m * 32 + ai) :: tl) = none := by
    intro m ai tl hlt h249 h250 h251
    have h9 : UInt8.ofNat (m * 32 + ai) ≠ 0xf9 := fun e => by
      have := congrArg UInt8.toNat e
      rw [toNat_ofNat_byte, Nat.mod_eq_of_lt hlt] at this; exact h249 this
    have ha : UInt8.ofNat (m * 32 + ai) ≠ 0xfa := fun e => by
      have := congrArg UInt8.toNat e
      rw [toNat_ofNat_byte, Nat.mod_eq_of_lt hlt] at this; exact h250 this
    have hb : UInt8.ofNat (m * 32 + ai) ≠ 0xfb := fun e => by
      have := congrArg UInt8.toNat e
      rw [toNat_ofNat_byte, Nat.mod_eq_of_lt hlt] at this; exact h251 this
    simp only [decodeFloatPrefix, h9, ha, hb, ↓reduceIte]
  cases h with
  | arg m w n =>
    obtain ⟨hm, hf⟩ := hv
    have hai := Width.ai_lt hf
    simp only [Head.bytes, encodeHead, List.cons_append]
    exact notFloatByte m (w.ai n) _ (by omega) (by omega) (by omega) (by omega)
  | indef m =>
    obtain ⟨h2, h5⟩ := hv
    simp only [Head.bytes, List.cons_append, List.nil_append]
    exact notFloatByte m 31 _ (by omega) (by omega) (by omega) (by omega)
  | brk => rfl
  | simple v =>
    simp only [Head.bytes, encodeHead, List.cons_append]
    rcases hv with hv | ⟨hv1, hv2⟩
    · have hw : simpleWidth v = .inline := by simp [simpleWidth, hv]
      rw [hw]; simp only [Width.ai]
      exact notFloatByte 7 v _ (by omega) (by omega) (by omega) (by omega)
    · have hw : simpleWidth v = .w1 := by simp [simpleWidth]; omega
      rw [hw]; simp only [Width.ai]
      exact notFloatByte 7 24 _ (by omega) (by omega) (by omega) (by omega)

theorem decodeFullHead_bytes {h : FullHead} (hv : h.Valid) (rest : List UInt8) :
    decodeFullHead (h.bytes ++ rest) = some (h, rest) := by
  cases h with
  | base hb =>
    simp [decodeFullHead, FullHead.bytes, head_bytes_not_float hv rest, decodeHead_bytes hv rest]
  | float f =>
    simp [decodeFullHead, FullHead.bytes, decodeFloatPrefix_encodeFloat]

theorem decodeFullHead_sound {bs rest : List UInt8} {h : FullHead}
    (hd : decodeFullHead bs = some (h, rest)) : h.Valid ∧ bs = h.bytes ++ rest := by
  unfold decodeFullHead at hd
  cases hf : decodeFloatPrefix bs with
  | some pr =>
    simp only [hf, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    exact ⟨trivial, decodeFloatPrefix_sound hf⟩
  | none =>
    simp only [hf] at hd
    cases hb : decodeHead bs with
    | none => simp [hb] at hd
    | some pr =>
      simp only [hb, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact decodeHead_sound hb

theorem decodeFullHead_of_decodeHead {bs rest : List UInt8} {h : Head}
    (hd : decodeHead bs = some (h, rest)) :
    decodeFullHead bs = some (.base h, rest) := by
  obtain ⟨hv, rfl⟩ := decodeHead_sound hd
  exact decodeFullHead_bytes (h := .base h) hv rest

private theorem ofBits_zero_eq_posZero16 : Float16.ofBits 0 = Float16.posZero :=
  Float16.ext rfl rfl rfl

private theorem ofBits_zero_eq_posZero32 : Float32.ofBits 0 = Float32.posZero :=
  Float32.ext rfl rfl rfl

private theorem ofBits_zero_eq_posZero64 : Float64.ofBits 0 = Float64.posZero :=
  Float64.ext rfl rfl rfl

/-- **Complete float heads accepted vs. Appendix F.1 Group 1 truncated float heads refused (§2.5):**
`decodeFullHead` accepts complete 2/4/8-byte float heads (`0xf90000`, `0xfa00000000`,
`0xfb0000000000000000`) while refusing Appendix F.1's 3 truncated float heads
(`f900`, `fa0000`, `fb000000`). -/
theorem fullHead_complete_vs_truncated :
    decodeFullHead [0xf9, 0x00, 0x00] = some (.float (.half Float16.posZero), []) ∧
    decodeFullHead [0xfa, 0x00, 0x00, 0x00, 0x00] = some (.float (.single Float32.posZero), []) ∧
    decodeFullHead [0xfb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
      some (.float (.double Float64.posZero), []) ∧
    decodeFullHead Vectors.appendixF1Seq16 = none ∧
    decodeFullHead Vectors.appendixF1Seq17 = none ∧
    decodeFullHead Vectors.appendixF1Seq18 = none := by
  rw [← ofBits_zero_eq_posZero16, ← ofBits_zero_eq_posZero32, ← ofBits_zero_eq_posZero64]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Full CBOR Syntax Trees (`FullItem` & `FullRawItem`) and Step-Fueled Wire Parser -/

/-- Full RFC 8949 CBOR data items (major types 0–7 including IEEE 754 floats). -/
inductive FullItem where
  | uint (n : Nat)
  | nint (n : Nat)
  | bytes (payload : List UInt8)
  | text (payload : List UInt8)
  | bytesIndef (chunks : List (List UInt8))
  | textIndef (chunks : List (List UInt8))
  | array (items : List FullItem)
  | arrayIndef (items : List FullItem)
  | map (entries : List (FullItem × FullItem))
  | mapIndef (entries : List (FullItem × FullItem))
  | tag (number : Nat) (content : FullItem)
  | simple (value : Nat)
  | float (value : CborFloat)
  deriving Repr, Inhabited

/-- Full wire-level syntax tree recording head argument `Width`s and float widths. -/
inductive FullRawItem where
  | uint (w : Width) (n : Nat)
  | nint (w : Width) (n : Nat)
  | bytes (w : Width) (payload : List UInt8)
  | text (w : Width) (payload : List UInt8)
  | bytesIndef (chunks : List (Width × List UInt8))
  | textIndef (chunks : List (Width × List UInt8))
  | array (w : Width) (items : List FullRawItem)
  | arrayIndef (items : List FullRawItem)
  | map (w : Width) (entries : List (FullRawItem × FullRawItem))
  | mapIndef (entries : List (FullRawItem × FullRawItem))
  | tag (w : Width) (number : Nat) (content : FullRawItem)
  | simple (value : Nat)
  | float (value : CborFloat)
  deriving Repr, Inhabited

@[elab_as_elim]
theorem FullItem.rec' {motive : FullItem → Prop}
    (uint : ∀ n, motive (.uint n)) (nint : ∀ n, motive (.nint n))
    (bytes : ∀ p, motive (.bytes p)) (text : ∀ p, motive (.text p))
    (bytesIndef : ∀ cs, motive (.bytesIndef cs)) (textIndef : ∀ cs, motive (.textIndef cs))
    (array : ∀ xs, (∀ x ∈ xs, motive x) → motive (.array xs))
    (arrayIndef : ∀ xs, (∀ x ∈ xs, motive x) → motive (.arrayIndef xs))
    (map : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.map kvs))
    (mapIndef : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.mapIndef kvs))
    (tag : ∀ t x, motive x → motive (.tag t x))
    (simple : ∀ v, motive (.simple v))
    (float : ∀ f, motive (.float f)) (x : FullItem) : motive x :=
  @FullItem.rec motive (fun xs => ∀ x ∈ xs, motive x)
    (fun kvs => ∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2)
    (fun kv => motive kv.1 ∧ motive kv.2)
    uint nint bytes text bytesIndef textIndef array arrayIndef map mapIndef tag simple float
    (by simp)
    (fun x xs hx hxs => by
      simp only [List.mem_cons]; rintro y (rfl | hy); exact hx; exact hxs y hy)
    (by simp)
    (fun kv kvs hkv hkvs => by
      simp only [List.mem_cons]; rintro y (rfl | hy); exact hkv; exact hkvs y hy)
    (fun k v hk hv => ⟨hk, hv⟩) x

@[elab_as_elim]
theorem FullRawItem.rec' {motive : FullRawItem → Prop}
    (uint : ∀ w n, motive (.uint w n)) (nint : ∀ w n, motive (.nint w n))
    (bytes : ∀ w p, motive (.bytes w p)) (text : ∀ w p, motive (.text w p))
    (bytesIndef : ∀ cs, motive (.bytesIndef cs)) (textIndef : ∀ cs, motive (.textIndef cs))
    (array : ∀ w xs, (∀ x ∈ xs, motive x) → motive (.array w xs))
    (arrayIndef : ∀ xs, (∀ x ∈ xs, motive x) → motive (.arrayIndef xs))
    (map : ∀ w kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.map w kvs))
    (mapIndef : ∀ kvs, (∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2) → motive (.mapIndef kvs))
    (tag : ∀ w t x, motive x → motive (.tag w t x))
    (simple : ∀ v, motive (.simple v))
    (float : ∀ f, motive (.float f)) (x : FullRawItem) : motive x :=
  @FullRawItem.rec motive (fun xs => ∀ x ∈ xs, motive x)
    (fun kvs => ∀ kv ∈ kvs, motive kv.1 ∧ motive kv.2)
    (fun kv => motive kv.1 ∧ motive kv.2)
    uint nint bytes text bytesIndef textIndef array arrayIndef map mapIndef tag simple float
    (by simp)
    (fun x xs hx hxs => by
      simp only [List.mem_cons]; rintro y (rfl | hy); exact hx; exact hxs y hy)
    (by simp)
    (fun kv kvs hkv hkvs => by
      simp only [List.mem_cons]; rintro y (rfl | hy); exact hkv; exact hkvs y hy)
    (fun k v hk hv => ⟨hk, hv⟩) x

namespace FullRawItem

mutual
/-- Serialize a full wire-level tree (§3, §3.1, §3.2, §3.3, §3.4). -/
def encode : FullRawItem → List UInt8
  | .uint w n => encodeHead 0 w n
  | .nint w n => encodeHead 1 w n
  | .bytes w p => encodeHead 2 w p.length ++ p
  | .text w p => encodeHead 3 w p.length ++ p
  | .bytesIndef cs => 0x5f :: (RawItem.encodeChunks 2 cs ++ [0xff])
  | .textIndef cs => 0x7f :: (RawItem.encodeChunks 3 cs ++ [0xff])
  | .array w xs => encodeHead 4 w xs.length ++ encodeList xs
  | .arrayIndef xs => 0x9f :: (encodeList xs ++ [0xff])
  | .map w kvs => encodeHead 5 w kvs.length ++ encodePairs kvs
  | .mapIndef kvs => 0xbf :: (encodePairs kvs ++ [0xff])
  | .tag w t x => encodeHead 6 w t ++ encode x
  | .simple v => encodeHead 7 (simpleWidth v) v
  | .float f => encodeFloat f
def encodeList : List FullRawItem → List UInt8
  | [] => []
  | x :: xs => encode x ++ encodeList xs
def encodePairs : List (FullRawItem × FullRawItem) → List UInt8
  | [] => []
  | (k, v) :: kvs => encode k ++ encode v ++ encodePairs kvs
end

mutual
/-- Well-formedness of a full wire-level tree. -/
def WF : FullRawItem → Prop
  | .uint w n => w.fits n = true
  | .nint w n => w.fits n = true
  | .bytes w p => w.fits p.length = true
  | .text w p => w.fits p.length = true
  | .bytesIndef cs => ∀ c ∈ cs, c.1.fits c.2.length = true
  | .textIndef cs => ∀ c ∈ cs, c.1.fits c.2.length = true
  | .array w xs => w.fits xs.length = true ∧ WFList xs
  | .arrayIndef xs => WFList xs
  | .map w kvs => w.fits kvs.length = true ∧ WFPairs kvs
  | .mapIndef kvs => WFPairs kvs
  | .tag w t x => w.fits t = true ∧ WF x
  | .simple v => v < 24 ∨ (32 ≤ v ∧ v < 256)
  | .float _ => True
def WFList : List FullRawItem → Prop
  | [] => True
  | x :: xs => WF x ∧ WFList xs
def WFPairs : List (FullRawItem × FullRawItem) → Prop
  | [] => True
  | (k, v) :: kvs => WF k ∧ WF v ∧ WFPairs kvs
end

mutual
/-- Erase non-float argument `Width`s (keeping each `CborFloat` value). -/
def toItem : FullRawItem → FullItem
  | .uint _ n => .uint n
  | .nint _ n => .nint n
  | .bytes _ p => .bytes p
  | .text _ p => .text p
  | .bytesIndef cs => .bytesIndef (cs.map Prod.snd)
  | .textIndef cs => .textIndef (cs.map Prod.snd)
  | .array _ xs => .array (toItemList xs)
  | .arrayIndef xs => .arrayIndef (toItemList xs)
  | .map _ kvs => .map (toItemPairs kvs)
  | .mapIndef kvs => .mapIndef (toItemPairs kvs)
  | .tag _ t x => .tag t (toItem x)
  | .simple v => .simple v
  | .float f => .float f
def toItemList : List FullRawItem → List FullItem
  | [] => []
  | x :: xs => toItem x :: toItemList xs
def toItemPairs : List (FullRawItem × FullRawItem) → List (FullItem × FullItem)
  | [] => []
  | (k, v) :: kvs => (toItem k, toItem v) :: toItemPairs kvs
end

mutual
/-- Embed a Milestone-1 float-free `RawItem` losslessly into `FullRawItem`. -/
def ofRawItem : RawItem → FullRawItem
  | .uint w n => .uint w n
  | .nint w n => .nint w n
  | .bytes w p => .bytes w p
  | .text w p => .text w p
  | .bytesIndef cs => .bytesIndef cs
  | .textIndef cs => .textIndef cs
  | .array w xs => .array w (ofRawItemList xs)
  | .arrayIndef xs => .arrayIndef (ofRawItemList xs)
  | .map w kvs => .map w (ofRawItemPairs kvs)
  | .mapIndef kvs => .mapIndef (ofRawItemPairs kvs)
  | .tag w t x => .tag w t (ofRawItem x)
  | .simple v => .simple v
def ofRawItemList : List RawItem → List FullRawItem
  | [] => []
  | x :: xs => ofRawItem x :: ofRawItemList xs
def ofRawItemPairs : List (RawItem × RawItem) → List (FullRawItem × FullRawItem)
  | [] => []
  | (k, v) :: kvs => (ofRawItem k, ofRawItem v) :: ofRawItemPairs kvs
end

mutual
def beq : FullRawItem → FullRawItem → Bool
  | .uint w₁ a, .uint w₂ b => w₁ == w₂ && a == b
  | .nint w₁ a, .nint w₂ b => w₁ == w₂ && a == b
  | .bytes w₁ p, .bytes w₂ q => w₁ == w₂ && p == q
  | .text w₁ p, .text w₂ q => w₁ == w₂ && p == q
  | .bytesIndef cs, .bytesIndef ds => cs == ds
  | .textIndef cs, .textIndef ds => cs == ds
  | .array w₁ xs, .array w₂ ys => w₁ == w₂ && beqList xs ys
  | .arrayIndef xs, .arrayIndef ys => beqList xs ys
  | .map w₁ kvs, .map w₂ lws => w₁ == w₂ && beqPairs kvs lws
  | .mapIndef kvs, .mapIndef lws => beqPairs kvs lws
  | .tag w₁ t x, .tag w₂ u y => w₁ == w₂ && t == u && beq x y
  | .simple v, .simple w => v == w
  | .float f, .float g => f == g
  | _, _ => false
def beqList : List FullRawItem → List FullRawItem → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false
def beqPairs : List (FullRawItem × FullRawItem) → List (FullRawItem × FullRawItem) → Bool
  | [], [] => true
  | (k, v) :: kvs, (l, w) :: lws => beq k l && beq v w && beqPairs kvs lws
  | _, _ => false
end

theorem beqList_iff {xs : List FullRawItem} (ih : ∀ x ∈ xs, ∀ y, beq x y = true ↔ x = y) :
    ∀ ys, beqList xs ys = true ↔ xs = ys := by
  induction xs with
  | nil => intro ys; cases ys <;> simp [beqList]
  | cons x xs ihxs =>
    intro ys; cases ys with
    | nil => simp [beqList]
    | cons y ys =>
      simp only [beqList, Bool.and_eq_true, List.cons.injEq]
      rw [ih x (by simp) y, ihxs (fun z hz => ih z (by simp [hz])) ys]

theorem beqPairs_iff {kvs : List (FullRawItem × FullRawItem)}
    (ih : ∀ kv ∈ kvs, (∀ y, beq kv.1 y = true ↔ kv.1 = y) ∧ (∀ y, beq kv.2 y = true ↔ kv.2 = y)) :
    ∀ lws, beqPairs kvs lws = true ↔ kvs = lws := by
  induction kvs with
  | nil => intro lws; cases lws <;> simp [beqPairs]
  | cons kv kvs ihkvs =>
    intro lws; obtain ⟨k, v⟩ := kv; cases lws with
    | nil => simp [beqPairs]
    | cons lw lws =>
      obtain ⟨l, w⟩ := lw
      simp only [beqPairs, Bool.and_eq_true, List.cons.injEq, Prod.mk.injEq]
      rw [(ih (k, v) (by simp)).1 l, (ih (k, v) (by simp)).2 w,
        ihkvs (fun z hz => ih z (by simp [hz])) lws, and_assoc]

theorem beq_iff (x : FullRawItem) : ∀ y, beq x y = true ↔ x = y := by
  induction x using FullRawItem.rec' with
  | uint w a => intro y; cases y <;> simp [beq]
  | nint w a => intro y; cases y <;> simp [beq]
  | bytes w p => intro y; cases y <;> simp [beq]
  | text w p => intro y; cases y <;> simp [beq]
  | bytesIndef cs => intro y; cases y <;> simp [beq]
  | textIndef cs => intro y; cases y <;> simp [beq]
  | array w xs ih => intro y; cases y <;> simp [beq, beqList_iff ih]
  | arrayIndef xs ih => intro y; cases y <;> simp [beq, beqList_iff ih]
  | map w kvs ih => intro y; cases y <;> simp [beq, beqPairs_iff ih]
  | mapIndef kvs ih => intro y; cases y <;> simp [beq, beqPairs_iff ih]
  | tag w t x ih => intro y; cases y <;> simp [beq, ih, and_assoc]
  | simple v => intro y; cases y <;> simp [beq]
  | float f => intro y; cases y <;> simp [beq]

instance : DecidableEq FullRawItem := fun x y => decidable_of_iff _ (beq_iff x y)

theorem encodeList_eq (xs : List FullRawItem) : encodeList xs = (xs.map encode).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeList, ih]

theorem encodePairs_eq (kvs : List (FullRawItem × FullRawItem)) :
    encodePairs kvs = (kvs.map fun kv => encode kv.1 ++ encode kv.2).flatten := by
  induction kvs with
  | nil => rfl
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [encodePairs, ih]

theorem WFList_iff (xs : List FullRawItem) : WFList xs ↔ ∀ x ∈ xs, WF x := by
  induction xs with
  | nil => simp [WFList]
  | cons x xs ih => simp [WFList, ih]

theorem WFPairs_iff (kvs : List (FullRawItem × FullRawItem)) :
    WFPairs kvs ↔ ∀ kv ∈ kvs, WF kv.1 ∧ WF kv.2 := by
  induction kvs with
  | nil => simp [WFPairs]
  | cons kv kvs ih => obtain ⟨k, v⟩ := kv; simp [WFPairs, ih, and_assoc]

theorem ofRawItemList_length (xs : List RawItem) :
    (ofRawItemList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ofRawItemList, ih]

theorem ofRawItemPairs_length (kvs : List (RawItem × RawItem)) :
    (ofRawItemPairs kvs).length = kvs.length := by
  induction kvs with
  | nil => rfl
  | cons kv _ ih => obtain ⟨_, _⟩ := kv; simp [ofRawItemPairs, ih]

theorem encode_ofRawItem (r : RawItem) : (ofRawItem r).encode = r.encode := by
  induction r using RawItem.rec' with
  | uint w n => rfl
  | nint w n => rfl
  | bytes w p => rfl
  | text w p => rfl
  | bytesIndef cs => rfl
  | textIndef cs => rfl
  | array w xs ih =>
    have hlist : ∀ l : List RawItem,
        (∀ x ∈ l, (ofRawItem x).encode = x.encode) →
        encodeList (ofRawItemList l) = RawItem.encodeList l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons y ys ihys =>
        simp [ofRawItemList, encodeList, RawItem.encodeList, hl y (by simp),
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofRawItem, encode, RawItem.encode, ofRawItemList_length, hlist xs ih]
  | arrayIndef xs ih =>
    have hlist : ∀ l : List RawItem,
        (∀ x ∈ l, (ofRawItem x).encode = x.encode) →
        encodeList (ofRawItemList l) = RawItem.encodeList l := by
      intro l hl; induction l with
      | nil => rfl
      | cons y ys ihys =>
        simp [ofRawItemList, encodeList, RawItem.encodeList, hl y (by simp),
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofRawItem, encode, RawItem.encode, hlist xs ih]
  | map w kvs ih =>
    have hpairs : ∀ l : List (RawItem × RawItem),
        (∀ kv ∈ l, (ofRawItem kv.1).encode = kv.1.encode ∧ (ofRawItem kv.2).encode = kv.2.encode) →
        encodePairs (ofRawItemPairs l) = RawItem.encodePairs l := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        simp [ofRawItemPairs, encodePairs, RawItem.encodePairs,
          (hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofRawItem, encode, RawItem.encode, ofRawItemPairs_length, hpairs kvs ih]
  | mapIndef kvs ih =>
    have hpairs : ∀ l : List (RawItem × RawItem),
        (∀ kv ∈ l, (ofRawItem kv.1).encode = kv.1.encode ∧ (ofRawItem kv.2).encode = kv.2.encode) →
        encodePairs (ofRawItemPairs l) = RawItem.encodePairs l := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        simp [ofRawItemPairs, encodePairs, RawItem.encodePairs,
          (hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofRawItem, encode, RawItem.encode, hpairs kvs ih]
  | tag w t x ih => simp [ofRawItem, encode, RawItem.encode, ih]
  | simple v => rfl

theorem wf_ofRawItem {r : RawItem} (hr : r.WF) : (ofRawItem r).WF := by
  induction r using RawItem.rec' with
  | uint w n => exact hr
  | nint w n => exact hr
  | bytes w p => exact hr
  | text w p => exact hr
  | bytesIndef cs => exact hr
  | textIndef cs => exact hr
  | array w xs ih =>
    obtain ⟨hfit, hxs⟩ := hr
    rw [RawItem.WFList_iff] at hxs
    refine ⟨by simpa [ofRawItemList_length] using hfit, ?_⟩
    have hlist : ∀ l : List RawItem, (∀ x ∈ l, (ofRawItem x).WF) → WFList (ofRawItemList l) := by
      intro l hl; induction l with
      | nil => trivial
      | cons y ys ihys => exact ⟨hl y (by simp), ihys (fun z hz => hl z (by simp [hz]))⟩
    exact hlist xs (fun x hx => ih x hx (hxs x hx))
  | arrayIndef xs ih =>
    rw [RawItem.WF, RawItem.WFList_iff] at hr
    have hlist : ∀ l : List RawItem, (∀ x ∈ l, (ofRawItem x).WF) → WFList (ofRawItemList l) := by
      intro l hl; induction l with
      | nil => trivial
      | cons y ys ihys => exact ⟨hl y (by simp), ihys (fun z hz => hl z (by simp [hz]))⟩
    exact hlist xs (fun x hx => ih x hx (hr x hx))
  | map w kvs ih =>
    obtain ⟨hfit, hkvs⟩ := hr
    rw [RawItem.WFPairs_iff] at hkvs
    refine ⟨by simpa [ofRawItemPairs_length] using hfit, ?_⟩
    have hpairs : ∀ l : List (RawItem × RawItem),
        (∀ kv ∈ l, (ofRawItem kv.1).WF ∧ (ofRawItem kv.2).WF) → WFPairs (ofRawItemPairs l) := by
      intro l hl; induction l with
      | nil => trivial
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        exact ⟨(hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2, ihys (fun z hz => hl z (by simp [hz]))⟩
    exact hpairs kvs (fun kv hkv => ⟨(ih kv hkv).1 (hkvs kv hkv).1, (ih kv hkv).2 (hkvs kv hkv).2⟩)
  | mapIndef kvs ih =>
    rw [RawItem.WF, RawItem.WFPairs_iff] at hr
    have hpairs : ∀ l : List (RawItem × RawItem),
        (∀ kv ∈ l, (ofRawItem kv.1).WF ∧ (ofRawItem kv.2).WF) → WFPairs (ofRawItemPairs l) := by
      intro l hl; induction l with
      | nil => trivial
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        exact ⟨(hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2, ihys (fun z hz => hl z (by simp [hz]))⟩
    exact hpairs kvs (fun kv hkv => ⟨(ih kv hkv).1 (hr kv hkv).1, (ih kv hkv).2 (hr kv hkv).2⟩)
  | tag w t x ih => exact ⟨hr.1, ih hr.2⟩
  | simple v => exact hr

end FullRawItem

/-! ## Step-fueled full CBOR wire parser & exact grammar characterization -/

/-- Decode payload/body of a `FullHead`. -/
def decodeFullBody (item : List UInt8 → Option (FullRawItem × List UInt8)) (fuel : Nat) :
    FullHead → List UInt8 → Option (FullRawItem × List UInt8)
  | .base (.arg 0 w n), rest => some (.uint w n, rest)
  | .base (.arg 1 w n), rest => some (.nint w n, rest)
  | .base (.arg 2 w n), rest =>
    if n ≤ rest.length then some (.bytes w (rest.take n), rest.drop n) else none
  | .base (.arg 3 w n), rest =>
    if n ≤ rest.length then some (.text w (rest.take n), rest.drop n) else none
  | .base (.arg 4 w n), rest =>
    match decodeCount item n rest with
    | none => none
    | some (xs, rest') => some (.array w xs, rest')
  | .base (.arg 5 w n), rest =>
    match decodeCount (decodePair item) n rest with
    | none => none
    | some (kvs, rest') => some (.map w kvs, rest')
  | .base (.arg 6 w t), rest =>
    match item rest with
    | none => none
    | some (x, rest') => some (.tag w t x, rest')
  | .base (.arg _ _ _), _ => none
  | .base (.indef 2), rest =>
    match decodeUntilBreak (decodeChunk 2) fuel rest with
    | none => none
    | some (cs, rest') => some (.bytesIndef cs, rest')
  | .base (.indef 3), rest =>
    match decodeUntilBreak (decodeChunk 3) fuel rest with
    | none => none
    | some (cs, rest') => some (.textIndef cs, rest')
  | .base (.indef 4), rest =>
    match decodeUntilBreak item fuel rest with
    | none => none
    | some (xs, rest') => some (.arrayIndef xs, rest')
  | .base (.indef 5), rest =>
    match decodeUntilBreak (decodePair item) fuel rest with
    | none => none
    | some (kvs, rest') => some (.mapIndef kvs, rest')
  | .base (.indef _), _ => none
  | .base .brk, _ => none
  | .base (.simple v), rest => some (.simple v, rest)
  | .float f, rest => some (.float f, rest)

/-- Step-fueled full CBOR prefix decoder. -/
def decodeFullRaw : Nat → List UInt8 → Option (FullRawItem × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match decodeFullHead bs with
    | none => none
    | some (h, rest) => decodeFullBody (decodeFullRaw fuel) fuel h rest

/-- Full CBOR wire-level parser (`bs.length + 1` initial step fuel). -/
def parseFullRaw (bs : List UInt8) : Option FullRawItem :=
  match decodeFullRaw (bs.length + 1) bs with
  | some (r, []) => some r
  | _ => none

/-- Full CBOR variation-tolerant well-formedness parser (§3, §4.1). -/
def parseFullWellFormed (bs : List UInt8) : Option FullItem :=
  (parseFullRaw bs).map FullRawItem.toItem

theorem decodeFullBody_sound {item : List UInt8 → Option (FullRawItem × List UInt8)}
    (hitem : ∀ bs r rest, item bs = some (r, rest) → r.WF ∧ bs = r.encode ++ rest)
    {fuel : Nat} {h : FullHead} (hv : h.Valid) {bs : List UInt8} {r : FullRawItem}
    {rest : List UInt8} (hb : decodeFullBody item fuel h bs = some (r, rest)) :
    r.WF ∧ h.bytes ++ bs = r.encode ++ rest := by
  cases h with
  | float f =>
    simp only [decodeFullBody, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact ⟨trivial, rfl⟩
  | base hd =>
    cases hd with
    | arg m w n =>
      obtain ⟨hm, hfit⟩ := hv
      match m, hm with
      | 0, _ =>
        simp only [decodeFullBody, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb; exact ⟨hfit, rfl⟩
      | 1, _ =>
        simp only [decodeFullBody, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb; exact ⟨hfit, rfl⟩
      | 2, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · rename_i hn
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hlen : (bs.take n).length = n := by simp; omega
          refine ⟨by simp only [FullRawItem.WF, hlen]; exact hfit, ?_⟩
          simp [FullRawItem.encode, FullHead.bytes, Head.bytes, hlen]
        · simp at hb
      | 3, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · rename_i hn
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          have hlen : (bs.take n).length = n := by simp; omega
          refine ⟨by simp only [FullRawItem.WF, hlen]; exact hfit, ?_⟩
          simp [FullRawItem.encode, FullHead.bytes, Head.bytes, hlen]
        · simp at hb
      | 4, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i xs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hlen, hwf, rfl⟩ := decodeCount_sound hitem _ _ _ _ hc
          refine ⟨⟨by rw [hlen]; exact hfit, (FullRawItem.WFList_iff xs).2 hwf⟩, ?_⟩
          simp [FullRawItem.encode, FullHead.bytes, Head.bytes, hlen, FullRawItem.encodeList_eq]
      | 5, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i kvs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hlen, hwf, rfl⟩ := decodeCount_sound
            (fun bs kv rest h => decodePair_sound hitem h) _ _ _ _ hc
          refine ⟨⟨by rw [hlen]; exact hfit, (FullRawItem.WFPairs_iff kvs).2 hwf⟩, ?_⟩
          simp [FullRawItem.encode, FullHead.bytes, Head.bytes, hlen, FullRawItem.encodePairs_eq]
      | 6, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i x rest' hx
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hwf, rfl⟩ := hitem _ _ _ hx
          exact ⟨⟨hfit, hwf⟩, by simp [FullRawItem.encode, FullHead.bytes, Head.bytes]⟩
      | _ + 7, hm => omega
    | indef m =>
      obtain ⟨h2, h5⟩ := hv
      match m, h2, h5 with
      | 2, _, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i cs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
            (fun bs c rest h => decodeChunk_sound h) _ _ _ _ hc
          exact ⟨hwf, by simp [FullRawItem.encode, FullHead.bytes, Head.bytes, encodeChunks_eq]⟩
      | 3, _, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i cs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
            (fun bs c rest h => decodeChunk_sound h) _ _ _ _ hc
          exact ⟨hwf, by simp [FullRawItem.encode, FullHead.bytes, Head.bytes, encodeChunks_eq]⟩
      | 4, _, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i xs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound hitem _ _ _ _ hc
          exact ⟨(FullRawItem.WFList_iff xs).2 hwf,
            by simp [FullRawItem.encode, FullHead.bytes, Head.bytes, FullRawItem.encodeList_eq]⟩
      | 5, _, _ =>
        simp only [decodeFullBody] at hb
        split at hb
        · simp at hb
        · rename_i kvs rest' hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          obtain ⟨hwf, rfl⟩ := decodeUntilBreak_sound
            (fun bs kv rest h => decodePair_sound hitem h) _ _ _ _ hc
          exact ⟨(FullRawItem.WFPairs_iff kvs).2 hwf,
            by simp [FullRawItem.encode, FullHead.bytes, Head.bytes, FullRawItem.encodePairs_eq]⟩
    | brk => simp [decodeFullBody] at hb
    | simple v =>
      simp only [decodeFullBody, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb; exact ⟨hv, rfl⟩

theorem decodeFullRaw_sound : ∀ fuel bs r rest, decodeFullRaw fuel bs = some (r, rest) →
    r.WF ∧ bs = r.encode ++ rest := by
  intro fuel
  induction fuel with
  | zero => intro bs r rest h; simp [decodeFullRaw] at h
  | succ fuel ih =>
    intro bs r rest h
    simp only [decodeFullRaw] at h
    split at h
    · simp at h
    · rename_i hd0 rest0 hd
      obtain ⟨hv, rfl⟩ := decodeFullHead_sound hd
      exact decodeFullBody_sound ih hv h

theorem FullRawItem.encode_first {r : FullRawItem} (hr : r.WF) :
    ∃ b t, r.encode = b :: t ∧ b ≠ 0xff := by
  cases r with
  | uint w n => exact encodeHead_first (by have := Width.ai_lt hr; omega)
  | nint w n => exact encodeHead_first (by have := Width.ai_lt hr; omega)
  | bytes w p =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 2) (w := w) (n := p.length)
      (by have := Width.ai_lt hr; omega)
    exact ⟨b, t ++ p, by simp [FullRawItem.encode, h], hb⟩
  | text w p =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 3) (w := w) (n := p.length)
      (by have := Width.ai_lt hr; omega)
    exact ⟨b, t ++ p, by simp [FullRawItem.encode, h], hb⟩
  | bytesIndef _ => exact ⟨0x5f, _, rfl, fun h => by cases h⟩
  | textIndef _ => exact ⟨0x7f, _, rfl, fun h => by cases h⟩
  | array w xs =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 4) (w := w) (n := xs.length)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t ++ FullRawItem.encodeList xs, by simp [FullRawItem.encode, h], hb⟩
  | arrayIndef _ => exact ⟨0x9f, _, rfl, fun h => by cases h⟩
  | map w kvs =>
    obtain ⟨b, t, h, hb⟩ := encodeHead_first (m := 5) (w := w) (n := kvs.length)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t ++ FullRawItem.encodePairs kvs, by simp [FullRawItem.encode, h], hb⟩
  | mapIndef _ => exact ⟨0xbf, _, rfl, fun h => by cases h⟩
  | tag w t x =>
    obtain ⟨b, t', h, hb⟩ := encodeHead_first (m := 6) (w := w) (n := t)
      (by have := Width.ai_lt hr.1; omega)
    exact ⟨b, t' ++ x.encode, by simp [FullRawItem.encode, h], hb⟩
  | simple v =>
    apply encodeHead_first
    simp only [FullRawItem.WF] at hr
    simp only [simpleWidth]
    split <;> simp [Width.ai] <;> omega
  | float f =>
    cases f with
    | half v => exact ⟨0xf9, beBytes 2 v.toBits, rfl, fun h => by cases h⟩
    | single v => exact ⟨0xfa, beBytes 4 v.toBits, rfl, fun h => by cases h⟩
    | double v => exact ⟨0xfb, beBytes 8 v.toBits, rfl, fun h => by cases h⟩

theorem FullRawItem.encode_ne_nil {r : FullRawItem} (hr : r.WF) : r.encode ≠ [] := by
  obtain ⟨b, t, h, _⟩ := FullRawItem.encode_first hr
  simp [h]

theorem decodeFullRaw_of_head {fuel : Nat} {bs rest : List UInt8} {h : FullHead}
    (hd : decodeFullHead bs = some (h, rest)) :
    decodeFullRaw (fuel + 1) bs = decodeFullBody (decodeFullRaw fuel) fuel h rest := by
  simp [decodeFullRaw, hd]

theorem decodeFullRaw_arg {fuel m : Nat} {w : Width} {n : Nat}
    (hm : m ≤ 6) (hf : w.fits n = true) (rest : List UInt8) :
    decodeFullRaw (fuel + 1) (encodeHead m w n ++ rest) =
      decodeFullBody (decodeFullRaw fuel) fuel (.base (.arg m w n)) rest :=
  decodeFullRaw_of_head (decodeFullHead_bytes (h := .base (.arg m w n)) ⟨hm, hf⟩ rest)

theorem decodeFullRaw_complete : ∀ fuel (r : FullRawItem) (rest : List UInt8), r.WF →
    r.encode.length < fuel → decodeFullRaw fuel (r.encode ++ rest) = some (r, rest) := by
  intro fuel
  induction fuel with
  | zero => intro r rest _ h; omega
  | succ fuel ih =>
    intro r rest hwf hlen
    cases r with
    | uint w n =>
      rw [FullRawItem.encode, decodeFullRaw_arg (by omega) hwf rest]
      rfl
    | nint w n =>
      rw [FullRawItem.encode, decodeFullRaw_arg (by omega) hwf rest]
      rfl
    | bytes w p =>
      rw [FullRawItem.encode, List.append_assoc, decodeFullRaw_arg (by omega) hwf (p ++ rest)]
      simp [decodeFullBody]
    | text w p =>
      rw [FullRawItem.encode, List.append_assoc, decodeFullRaw_arg (by omega) hwf (p ++ rest)]
      simp [decodeFullBody]
    | bytesIndef cs =>
      have hd := decodeFullHead_bytes (h := .base (.indef 2)) ⟨by omega, by omega⟩
        (RawItem.encodeChunks 2 cs ++ 0xff :: rest)
      have hb : (FullHead.base (.indef 2)).bytes = [0x5f] := rfl
      rw [hb] at hd
      simp only [FullRawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeFullRaw_of_head (by simpa using hd)]
      simp only [FullRawItem.WF] at hwf
      have hlen' : cs.length < fuel := by
        have := length_le_flatten cs (f := chunkEnc 2) (fun c hc => by
          obtain ⟨b, t, h, _⟩ := chunkEnc_first (m := 2) (by omega) (hwf c hc); simp [h])
        rw [encodeChunks_eq] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      rw [encodeChunks_eq, decodeFullBody, decodeUntilBreak_complete cs
        (fun c hc rest' => decodeChunk_complete (by omega) (hwf c hc) rest')
        (fun c hc => chunkEnc_first (by omega) (hwf c hc)) fuel hlen' rest]
    | textIndef cs =>
      have hd := decodeFullHead_bytes (h := .base (.indef 3)) ⟨by omega, by omega⟩
        (RawItem.encodeChunks 3 cs ++ 0xff :: rest)
      have hb : (FullHead.base (.indef 3)).bytes = [0x7f] := rfl
      rw [hb] at hd
      simp only [FullRawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeFullRaw_of_head (by simpa using hd)]
      simp only [FullRawItem.WF] at hwf
      have hlen' : cs.length < fuel := by
        have := length_le_flatten cs (f := chunkEnc 3) (fun c hc => by
          obtain ⟨b, t, h, _⟩ := chunkEnc_first (m := 3) (by omega) (hwf c hc); simp [h])
        rw [encodeChunks_eq] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      rw [encodeChunks_eq, decodeFullBody, decodeUntilBreak_complete cs
        (fun c hc rest' => decodeChunk_complete (by omega) (hwf c hc) rest')
        (fun c hc => chunkEnc_first (by omega) (hwf c hc)) fuel hlen' rest]
    | array w xs =>
      obtain ⟨hfit, hxs⟩ := hwf
      rw [FullRawItem.WFList_iff] at hxs
      rw [FullRawItem.encode, List.append_assoc, decodeFullRaw_arg (by omega) hfit]
      simp only [FullRawItem.encode, List.length_append, encodeHead_length,
        FullRawItem.encodeList_eq] at hlen
      rw [FullRawItem.encodeList_eq, decodeFullBody, decodeCount_complete xs
        (fun x hx rest' => ih x rest' (hxs x hx) (by
          have := length_le_flatten_of_mem (f := FullRawItem.encode) hx; omega)) rest]
    | arrayIndef xs =>
      rw [FullRawItem.WF, FullRawItem.WFList_iff] at hwf
      have hd := decodeFullHead_bytes (h := .base (.indef 4)) ⟨by omega, by omega⟩
        (FullRawItem.encodeList xs ++ 0xff :: rest)
      have hb : (FullHead.base (.indef 4)).bytes = [0x9f] := rfl
      rw [hb] at hd
      simp only [FullRawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeFullRaw_of_head (by simpa using hd)]
      simp only [FullRawItem.encodeList_eq, List.length_cons, List.length_append] at hlen
      have hlen' : xs.length < fuel := by
        have := length_le_flatten xs (f := FullRawItem.encode)
          (fun x hx => FullRawItem.encode_ne_nil (hwf x hx))
        omega
      rw [FullRawItem.encodeList_eq, decodeFullBody, decodeUntilBreak_complete xs
        (fun x hx rest' => ih x rest' (hwf x hx) (by
          have := length_le_flatten_of_mem (f := FullRawItem.encode) hx; omega))
        (fun x hx => FullRawItem.encode_first (hwf x hx)) fuel hlen' rest]
    | map w kvs =>
      obtain ⟨hfit, hkvs⟩ := hwf
      rw [FullRawItem.WFPairs_iff] at hkvs
      rw [FullRawItem.encode, List.append_assoc, decodeFullRaw_arg (by omega) hfit]
      simp only [FullRawItem.encode, List.length_append, encodeHead_length,
        FullRawItem.encodePairs_eq] at hlen
      rw [FullRawItem.encodePairs_eq, decodeFullBody, decodeCount_complete
        (dec := decodePair (decodeFullRaw fuel))
        (enc := fun kv : FullRawItem × FullRawItem => kv.1.encode ++ kv.2.encode) kvs
        (fun kv hkv rest' => by
          have hmem := length_le_flatten_of_mem
            (f := fun kv : FullRawItem × FullRawItem => kv.1.encode ++ kv.2.encode) hkv
          simp only [List.length_append] at hmem
          exact decodePair_complete
            (fun r' => ih kv.1 r' (hkvs kv hkv).1 (by omega))
            (fun r' => ih kv.2 r' (hkvs kv hkv).2 (by omega)) rest') rest]
    | mapIndef kvs =>
      rw [FullRawItem.WF, FullRawItem.WFPairs_iff] at hwf
      have hd := decodeFullHead_bytes (h := .base (.indef 5)) ⟨by omega, by omega⟩
        (FullRawItem.encodePairs kvs ++ 0xff :: rest)
      have hb : (FullHead.base (.indef 5)).bytes = [0xbf] := rfl
      rw [hb] at hd
      simp only [FullRawItem.encode, List.cons_append, List.append_assoc, List.nil_append] at hlen ⊢
      rw [decodeFullRaw_of_head (by simpa using hd)]
      simp only [FullRawItem.encodePairs_eq, List.length_cons, List.length_append] at hlen
      have hlen' : kvs.length < fuel := by
        have := length_le_flatten kvs
          (f := fun kv : FullRawItem × FullRawItem => kv.1.encode ++ kv.2.encode)
          (fun kv hkv => by simp [FullRawItem.encode_ne_nil (hwf kv hkv).1])
        omega
      rw [FullRawItem.encodePairs_eq, decodeFullBody, decodeUntilBreak_complete
        (dec := decodePair (decodeFullRaw fuel))
        (enc := fun kv : FullRawItem × FullRawItem => kv.1.encode ++ kv.2.encode) kvs
        (fun kv hkv rest' => by
          have hmem := length_le_flatten_of_mem
            (f := fun kv : FullRawItem × FullRawItem => kv.1.encode ++ kv.2.encode) hkv
          simp only [List.length_append] at hmem
          exact decodePair_complete
            (fun r' => ih kv.1 r' (hwf kv hkv).1 (by omega))
            (fun r' => ih kv.2 r' (hwf kv hkv).2 (by omega)) rest')
        (fun kv hkv => by
          obtain ⟨b, t, he, hb'⟩ := FullRawItem.encode_first (hwf kv hkv).1
          exact ⟨b, t ++ kv.2.encode, by simp [he], hb'⟩)
        fuel hlen' rest]
    | tag w t x =>
      obtain ⟨hfit, hx⟩ := hwf
      rw [FullRawItem.encode, List.append_assoc, decodeFullRaw_arg (by omega) hfit (x.encode ++ rest)]
      simp only [FullRawItem.encode, List.length_append, encodeHead_length] at hlen
      rw [decodeFullBody, ih x rest hx (by omega)]
    | simple v =>
      exact decodeFullRaw_of_head (decodeFullHead_bytes (h := .base (.simple v)) hwf rest)
    | float f =>
      exact decodeFullRaw_of_head (decodeFullHead_bytes (h := .float f) trivial rest)

/-- **Exact full RFC 8949 wire-grammar characterization:** `parseFullRaw bs = some r`
iff `r` is well-formed and `r.encode = bs`. -/
theorem parseFullRaw_eq_some_iff {bs : List UInt8} {r : FullRawItem} :
    parseFullRaw bs = some r ↔ r.WF ∧ r.encode = bs := by
  constructor
  · intro h
    unfold parseFullRaw at h
    cases hd : decodeFullRaw (bs.length + 1) bs with
    | none => simp [hd] at h
    | some pr =>
      obtain ⟨r', rest⟩ := pr
      cases rest with
      | nil =>
        simp only [hd, Option.some.injEq] at h
        subst h
        obtain ⟨hwf, henc⟩ := decodeFullRaw_sound _ _ _ _ hd
        exact ⟨hwf, by simpa using henc.symm⟩
      | cons _ _ => simp [hd] at h
  · rintro ⟨hwf, rfl⟩
    have hc := decodeFullRaw_complete (r.encode.length + 1) r [] hwf (by omega)
    simp only [List.append_nil] at hc
    simp [parseFullRaw, hc]

theorem FullRawItem.encode_prefix_unique {r₁ r₂ : FullRawItem} {t₁ t₂ : List UInt8}
    (h₁ : r₁.WF) (h₂ : r₂.WF) (he : r₁.encode ++ t₁ = r₂.encode ++ t₂) :
    r₁ = r₂ ∧ t₁ = t₂ := by
  let fuel := r₁.encode.length + r₂.encode.length + 1
  have c₁ := decodeFullRaw_complete fuel r₁ t₁ h₁ (by omega)
  have c₂ := decodeFullRaw_complete fuel r₂ t₂ h₂ (by omega)
  rw [he, c₂] at c₁
  simp only [Option.some.injEq, Prod.mk.injEq] at c₁
  exact ⟨c₁.1.symm, c₁.2.symm⟩

theorem FullRawItem.encode_injective {r₁ r₂ : FullRawItem} (h₁ : r₁.WF) (h₂ : r₂.WF)
    (he : r₁.encode = r₂.encode) : r₁ = r₂ :=
  (FullRawItem.encode_prefix_unique h₁ h₂ (t₁ := []) (t₂ := []) (by simpa using he)).1

/-- **Conservative extension over M1 `parseRaw`:** every float-free CBOR wire
parsed by `parseRaw` parses to `FullRawItem.ofRawItem r` under `parseFullRaw`. -/
theorem parseFullRaw_of_parseRaw {bs : List UInt8} {r : RawItem}
    (h : parseRaw bs = some r) : parseFullRaw bs = some (FullRawItem.ofRawItem r) := by
  obtain ⟨hwf, henc⟩ := parseRaw_eq_some_iff.mp h
  exact parseFullRaw_eq_some_iff.mpr ⟨FullRawItem.wf_ofRawItem hwf,
    (FullRawItem.encode_ofRawItem r).trans henc⟩

/-! ## `FullItem` Preferred / Deterministic Encodings and Full §5.6.1 `Equiv` -/

namespace FullItem

mutual
def beq : FullItem → FullItem → Bool
  | .uint a, .uint b => a == b
  | .nint a, .nint b => a == b
  | .bytes p, .bytes q => p == q
  | .text p, .text q => p == q
  | .bytesIndef cs, .bytesIndef ds => cs == ds
  | .textIndef cs, .textIndef ds => cs == ds
  | .array xs, .array ys => beqList xs ys
  | .arrayIndef xs, .arrayIndef ys => beqList xs ys
  | .map kvs, .map lws => beqPairs kvs lws
  | .mapIndef kvs, .mapIndef lws => beqPairs kvs lws
  | .tag t x, .tag u y => t == u && beq x y
  | .simple v, .simple w => v == w
  | .float f, .float g => f == g
  | _, _ => false
def beqList : List FullItem → List FullItem → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false
def beqPairs : List (FullItem × FullItem) → List (FullItem × FullItem) → Bool
  | [], [] => true
  | (k, v) :: kvs, (l, w) :: lws => beq k l && beq v w && beqPairs kvs lws
  | _, _ => false
end

theorem beqList_iff {xs : List FullItem} (ih : ∀ x ∈ xs, ∀ y, beq x y = true ↔ x = y) :
    ∀ ys, beqList xs ys = true ↔ xs = ys := by
  induction xs with
  | nil => intro ys; cases ys <;> simp [beqList]
  | cons x xs ihxs =>
    intro ys; cases ys with
    | nil => simp [beqList]
    | cons y ys =>
      simp only [beqList, Bool.and_eq_true, List.cons.injEq]
      rw [ih x (by simp) y, ihxs (fun z hz => ih z (by simp [hz])) ys]

theorem beqPairs_iff {kvs : List (FullItem × FullItem)}
    (ih : ∀ kv ∈ kvs, (∀ y, beq kv.1 y = true ↔ kv.1 = y) ∧ (∀ y, beq kv.2 y = true ↔ kv.2 = y)) :
    ∀ lws, beqPairs kvs lws = true ↔ kvs = lws := by
  induction kvs with
  | nil => intro lws; cases lws <;> simp [beqPairs]
  | cons kv kvs ihkvs =>
    intro lws; obtain ⟨k, v⟩ := kv; cases lws with
    | nil => simp [beqPairs]
    | cons lw lws =>
      obtain ⟨l, w⟩ := lw
      simp only [beqPairs, Bool.and_eq_true, List.cons.injEq, Prod.mk.injEq]
      rw [(ih (k, v) (by simp)).1 l, (ih (k, v) (by simp)).2 w,
        ihkvs (fun z hz => ih z (by simp [hz])) lws, and_assoc]

theorem beq_iff (x : FullItem) : ∀ y, beq x y = true ↔ x = y := by
  induction x using FullItem.rec' with
  | uint a => intro y; cases y <;> simp [beq]
  | nint a => intro y; cases y <;> simp [beq]
  | bytes p => intro y; cases y <;> simp [beq]
  | text p => intro y; cases y <;> simp [beq]
  | bytesIndef cs => intro y; cases y <;> simp [beq]
  | textIndef cs => intro y; cases y <;> simp [beq]
  | array xs ih => intro y; cases y <;> simp [beq, beqList_iff ih]
  | arrayIndef xs ih => intro y; cases y <;> simp [beq, beqList_iff ih]
  | map kvs ih => intro y; cases y <;> simp [beq, beqPairs_iff ih]
  | mapIndef kvs ih => intro y; cases y <;> simp [beq, beqPairs_iff ih]
  | tag t x ih => intro y; cases y <;> simp [beq, ih]
  | simple v => intro y; cases y <;> simp [beq]
  | float f => intro y; cases y <;> simp [beq]

instance : DecidableEq FullItem := fun x y => decidable_of_iff _ (beq_iff x y)

mutual
def WF : FullItem → Prop
  | .uint n => n < 2 ^ 64
  | .nint n => n < 2 ^ 64
  | .bytes p => p.length < 2 ^ 64
  | .text p => p.length < 2 ^ 64
  | .bytesIndef cs => ∀ c ∈ cs, c.length < 2 ^ 64
  | .textIndef cs => ∀ c ∈ cs, c.length < 2 ^ 64
  | .array xs => xs.length < 2 ^ 64 ∧ WFList xs
  | .arrayIndef xs => WFList xs
  | .map kvs => kvs.length < 2 ^ 64 ∧ WFPairs kvs
  | .mapIndef kvs => WFPairs kvs
  | .tag t x => t < 2 ^ 64 ∧ WF x
  | .simple v => v < 24 ∨ (32 ≤ v ∧ v < 256)
  | .float _ => True
def WFList : List FullItem → Prop
  | [] => True
  | x :: xs => WF x ∧ WFList xs
def WFPairs : List (FullItem × FullItem) → Prop
  | [] => True
  | (k, v) :: kvs => WF k ∧ WF v ∧ WFPairs kvs
end

mutual
/-- Choose §4.1 preferred shortest widths for all arguments and floats. -/
def toRaw : FullItem → FullRawItem
  | .uint n => .uint (Width.preferred n) n
  | .nint n => .nint (Width.preferred n) n
  | .bytes p => .bytes (Width.preferred p.length) p
  | .text p => .text (Width.preferred p.length) p
  | .bytesIndef cs => .bytesIndef (cs.map fun c => (Width.preferred c.length, c))
  | .textIndef cs => .textIndef (cs.map fun c => (Width.preferred c.length, c))
  | .array xs => .array (Width.preferred xs.length) (toRawList xs)
  | .arrayIndef xs => .arrayIndef (toRawList xs)
  | .map kvs => .map (Width.preferred kvs.length) (toRawPairs kvs)
  | .mapIndef kvs => .mapIndef (toRawPairs kvs)
  | .tag t x => .tag (Width.preferred t) t (toRaw x)
  | .simple v => .simple v
  | .float f => .float (preferredFloat f)
def toRawList : List FullItem → List FullRawItem
  | [] => []
  | x :: xs => toRaw x :: toRawList xs
def toRawPairs : List (FullItem × FullItem) → List (FullRawItem × FullRawItem)
  | [] => []
  | (k, v) :: kvs => (toRaw k, toRaw v) :: toRawPairs kvs
end

mutual
/-- Embed a Milestone-1 float-free `Item` into `FullItem`. -/
def ofItem : Item → FullItem
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .bytesIndef cs => .bytesIndef cs
  | .textIndef cs => .textIndef cs
  | .array xs => .array (ofItemList xs)
  | .arrayIndef xs => .arrayIndef (ofItemList xs)
  | .map kvs => .map (ofItemPairs kvs)
  | .mapIndef kvs => .mapIndef (ofItemPairs kvs)
  | .tag t x => .tag t (ofItem x)
  | .simple v => .simple v
def ofItemList : List Item → List FullItem
  | [] => []
  | x :: xs => ofItem x :: ofItemList xs
def ofItemPairs : List (Item × Item) → List (FullItem × FullItem)
  | [] => []
  | (k, v) :: kvs => (ofItem k, ofItem v) :: ofItemPairs kvs
end

mutual
def textValid : FullItem → Bool
  | .text p => utf8Valid p
  | .textIndef cs => cs.all utf8Valid
  | .array xs => textValidList xs
  | .arrayIndef xs => textValidList xs
  | .map kvs => textValidPairs kvs
  | .mapIndef kvs => textValidPairs kvs
  | .tag _ x => textValid x
  | _ => true
def textValidList : List FullItem → Bool
  | [] => true
  | x :: xs => textValid x && textValidList xs
def textValidPairs : List (FullItem × FullItem) → Bool
  | [] => true
  | (k, v) :: kvs => textValid k && textValid v && textValidPairs kvs
end

end FullItem

/-- §4.1 preferred serialization of a `FullItem`. -/
def encodeFullPreferred (x : FullItem) : List UInt8 :=
  x.toRaw.encode

/-- §4.2.1 bytewise lexicographic map-key comparator on `FullItem` pairs. -/
def fullKeyLt (p q : FullItem × FullItem) : Bool :=
  lexLt (encodeFullPreferred p.1) (encodeFullPreferred q.1)

def fullKeysStrict : List (FullItem × FullItem) → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest => fullKeyLt p q && fullKeysStrict (q :: rest)

namespace FullItem

mutual
/-- §4.2.1 + §4.2.2 core deterministic normalization on `FullItem`:
definite lengths throughout, `canonicalFloatDet` on every float (shortest width
and quiet `0xf97e00` for every NaN), and stably key-sorted maps. -/
def normalise : FullItem → FullItem
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .bytesIndef cs => .bytes cs.flatten
  | .textIndef cs => .text cs.flatten
  | .array xs => .array (normaliseList xs)
  | .arrayIndef xs => .array (normaliseList xs)
  | .map kvs => .map (sortBy fullKeyLt (normalisePairs kvs))
  | .mapIndef kvs => .map (sortBy fullKeyLt (normalisePairs kvs))
  | .tag t x => .tag t (normalise x)
  | .simple v => .simple v
  | .float f => .float (canonicalFloatDet f)
def normaliseList : List FullItem → List FullItem
  | [] => []
  | x :: xs => normalise x :: normaliseList xs
def normalisePairs : List (FullItem × FullItem) → List (FullItem × FullItem)
  | [] => []
  | (k, v) :: kvs => (normalise k, normalise v) :: normalisePairs kvs
end

mutual
/-- Whether a `FullItem` is in §4.2.1 / §4.2.2 deterministic shape
(no indefinite lengths, strictly sorted map keys, and `isDeterministicFloat`
on every float). -/
def isDeterministic : FullItem → Bool
  | .bytesIndef _ | .textIndef _ | .arrayIndef _ | .mapIndef _ => false
  | .array xs => isDeterministicList xs
  | .map kvs => fullKeysStrict kvs && isDeterministicPairs kvs
  | .tag _ x => isDeterministic x
  | .float f => isDeterministicFloat f
  | _ => true
def isDeterministicList : List FullItem → Bool
  | [] => true
  | x :: xs => isDeterministic x && isDeterministicList xs
def isDeterministicPairs : List (FullItem × FullItem) → Bool
  | [] => true
  | (k, v) :: kvs => isDeterministic k && isDeterministic v && isDeterministicPairs kvs
end

end FullItem

/-- §4.2.1 + §4.2.2 core deterministic encoding of a `FullItem`. -/
def encodeFullDeterministic (x : FullItem) : List UInt8 :=
  encodeFullPreferred x.normalise

/-- Strict §4.2.1 + §4.2.2 + §5.3.1 core deterministic decoder on full CBOR:
accepts `bs` iff `bs` parses to `x`, `x` is in deterministic shape (including
shortest-float width and canonical quiet NaN `0xf97e00`), all text is valid
UTF-8, and `encodeFullDeterministic x = bs`. -/
def decodeFullDeterministic (bs : List UInt8) : Option FullItem :=
  match parseFullWellFormed bs with
  | none => none
  | some x =>
    if x.isDeterministic && x.textValid && encodeFullDeterministic x == bs then some x else none

theorem encodeFullDeterministic_of_decodeFullDeterministic {bs : List UInt8} {x : FullItem}
    (h : decodeFullDeterministic bs = some x) :
    x.isDeterministic = true ∧ x.textValid = true ∧ encodeFullDeterministic x = bs := by
  unfold decodeFullDeterministic at h
  cases hp : parseFullWellFormed bs with
  | none => simp [hp] at h
  | some y =>
    simp only [hp] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.1.1, hc.1.2, hc.2⟩
    · simp at h

/-! ### Full §2 / §5.6.1 Data-Model Equivalence (`FullItem.Equiv`) -/

def fullEntryLt (p q : FullItem × FullItem) : Bool :=
  lexLt (encodeFullPreferred p.1) (encodeFullPreferred q.1) ||
    (encodeFullPreferred p.1 == encodeFullPreferred q.1 &&
      lexLt (encodeFullPreferred p.2) (encodeFullPreferred q.2))

def fullInsertUniq (x : FullItem × FullItem) : List (FullItem × FullItem) → List (FullItem × FullItem)
  | [] => [x]
  | y :: ys =>
    if y = x then y :: ys
    else if fullEntryLt y x then y :: fullInsertUniq x ys
    else x :: y :: ys

def fullSortUniq : List (FullItem × FullItem) → List (FullItem × FullItem)
  | [] => []
  | x :: xs => fullInsertUniq x (fullSortUniq xs)

namespace FullItem

mutual
/-- Canonical §5.6.1 generic data-model representative of a `FullItem`. -/
def canon : FullItem → FullItem
  | .uint n => .uint n
  | .nint n => .nint n
  | .bytes p => .bytes p
  | .text p => .text p
  | .bytesIndef cs => .bytes cs.flatten
  | .textIndef cs => .text cs.flatten
  | .array xs => .array (canonList xs)
  | .arrayIndef xs => .array (canonList xs)
  | .map kvs => .map (fullSortUniq (canonPairs kvs))
  | .mapIndef kvs => .map (fullSortUniq (canonPairs kvs))
  | .tag t x => .tag t (canon x)
  | .simple v => .simple v
  | .float f => .float (canonFloatKey f)
def canonList : List FullItem → List FullItem
  | [] => []
  | x :: xs => canon x :: canonList xs
def canonPairs : List (FullItem × FullItem) → List (FullItem × FullItem)
  | [] => []
  | (k, v) :: kvs => (canon k, canon v) :: canonPairs kvs
end

/-- RFC 8949 §2 / §5.6.1 basic generic data-model equivalence on `FullItem`. -/
def Equiv (x y : FullItem) : Prop := x.canon = y.canon

instance : DecidableRel Equiv := fun x y => inferInstanceAs (Decidable (x.canon = y.canon))

theorem Equiv.refl (x : FullItem) : Equiv x x := rfl
theorem Equiv.symm {x y : FullItem} (h : Equiv x y) : Equiv y x := Eq.symm h
theorem Equiv.trans {x y z : FullItem} (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  Eq.trans h₁ h₂

/-- **Float clause of §5.6.1:** two float items are equivalent iff `FloatEquiv` holds. -/
theorem equiv_float_iff (f g : CborFloat) :
    Equiv (.float f) (.float g) ↔ FloatEquiv f g := by
  simp only [Equiv, canon, float.injEq]
  exact canonFloatKey_eq_iff f g

/-- **§2 / §5.6.1 cross-type distinctness:** floating-point values are distinct
from unsigned integers, negative integers, tagged values (including tag-2/3
bignums), and simple values, even when numerically equal (`1.0 ≠ 1`, `0.0 ≠ 0`). -/
theorem not_equiv_float_uint (f : CborFloat) (n : Nat) : ¬ Equiv (.float f) (.uint n) := by
  simp [Equiv, canon]

theorem not_equiv_float_nint (f : CborFloat) (n : Nat) : ¬ Equiv (.float f) (.nint n) := by
  simp [Equiv, canon]

theorem not_equiv_float_tag (f : CborFloat) (t : Nat) (x : FullItem) :
    ¬ Equiv (.float f) (.tag t x) := by
  simp [Equiv, canon]

theorem not_equiv_float_simple (f : CborFloat) (v : Nat) : ¬ Equiv (.float f) (.simple v) := by
  simp [Equiv, canon]

theorem ofItem_injective : Function.Injective ofItem := by
  intro x
  induction x using Item.rec' with
  | uint a => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | nint a => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | bytes p => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | text p => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | bytesIndef cs => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | textIndef cs => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h
  | array xs ih =>
    have hlist : ∀ (l₁ : List Item), (∀ x ∈ l₁, ∀ y, ofItem x = ofItem y → x = y) →
        ∀ l₂, ofItemList l₁ = ofItemList l₂ → l₁ = l₂ := by
      intro l₁ hl; induction l₁ with
      | nil => intro l₂ h; cases l₂ <;> simp [ofItemList] at h; rfl
      | cons a as ihas =>
        intro l₂ h; cases l₂ with
        | nil => simp [ofItemList] at h
        | cons b bs =>
          simp only [ofItemList, List.cons.injEq] at h
          exact List.cons_eq_cons.mpr ⟨hl a (by simp) b h.1,
            ihas (fun z hz => hl z (by simp [hz])) bs h.2⟩
    intro y h; cases y <;> simp [ofItem] at h ⊢
    exact hlist xs ih _ h
  | arrayIndef xs ih =>
    have hlist : ∀ (l₁ : List Item), (∀ x ∈ l₁, ∀ y, ofItem x = ofItem y → x = y) →
        ∀ l₂, ofItemList l₁ = ofItemList l₂ → l₁ = l₂ := by
      intro l₁ hl; induction l₁ with
      | nil => intro l₂ h; cases l₂ <;> simp [ofItemList] at h; rfl
      | cons a as ihas =>
        intro l₂ h; cases l₂ with
        | nil => simp [ofItemList] at h
        | cons b bs =>
          simp only [ofItemList, List.cons.injEq] at h
          exact List.cons_eq_cons.mpr ⟨hl a (by simp) b h.1,
            ihas (fun z hz => hl z (by simp [hz])) bs h.2⟩
    intro y h; cases y <;> simp [ofItem] at h ⊢
    exact hlist xs ih _ h
  | map kvs ih =>
    have hpairs : ∀ (l₁ : List (Item × Item)),
        (∀ kv ∈ l₁, (∀ y, ofItem kv.1 = ofItem y → kv.1 = y) ∧
          (∀ y, ofItem kv.2 = ofItem y → kv.2 = y)) →
        ∀ l₂, ofItemPairs l₁ = ofItemPairs l₂ → l₁ = l₂ := by
      intro l₁ hl; induction l₁ with
      | nil => intro l₂ h; cases l₂ <;> simp [ofItemPairs] at h; rfl
      | cons kv as ihas =>
        obtain ⟨k, v⟩ := kv
        intro l₂ h; cases l₂ with
        | nil => simp [ofItemPairs] at h
        | cons lw bs =>
          obtain ⟨l, w⟩ := lw
          simp only [ofItemPairs, List.cons.injEq, Prod.mk.injEq] at h
          exact List.cons_eq_cons.mpr ⟨Prod.ext ((hl (k, v) (by simp)).1 l h.1.1)
            ((hl (k, v) (by simp)).2 w h.1.2),
            ihas (fun z hz => hl z (by simp [hz])) bs h.2⟩
    intro y h; cases y <;> simp [ofItem] at h ⊢
    exact hpairs kvs ih _ h
  | mapIndef kvs ih =>
    have hpairs : ∀ (l₁ : List (Item × Item)),
        (∀ kv ∈ l₁, (∀ y, ofItem kv.1 = ofItem y → kv.1 = y) ∧
          (∀ y, ofItem kv.2 = ofItem y → kv.2 = y)) →
        ∀ l₂, ofItemPairs l₁ = ofItemPairs l₂ → l₁ = l₂ := by
      intro l₁ hl; induction l₁ with
      | nil => intro l₂ h; cases l₂ <;> simp [ofItemPairs] at h; rfl
      | cons kv as ihas =>
        obtain ⟨k, v⟩ := kv
        intro l₂ h; cases l₂ with
        | nil => simp [ofItemPairs] at h
        | cons lw bs =>
          obtain ⟨l, w⟩ := lw
          simp only [ofItemPairs, List.cons.injEq, Prod.mk.injEq] at h
          exact List.cons_eq_cons.mpr ⟨Prod.ext ((hl (k, v) (by simp)).1 l h.1.1)
            ((hl (k, v) (by simp)).2 w h.1.2),
            ihas (fun z hz => hl z (by simp [hz])) bs h.2⟩
    intro y h; cases y <;> simp [ofItem] at h ⊢
    exact hpairs kvs ih _ h
  | tag t x ih =>
    intro y h; cases y <;> simp [ofItem] at h ⊢
    exact ⟨h.1, ih h.2⟩
  | simple v => intro y h; cases y <;> simp [ofItem] at h ⊢; exact h

theorem ofItemList_length (xs : List Item) :
    (ofItemList xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [ofItemList, ih]

theorem ofItemPairs_length (kvs : List (Item × Item)) :
    (ofItemPairs kvs).length = kvs.length := by
  induction kvs with
  | nil => rfl
  | cons kv _ ih => obtain ⟨_, _⟩ := kv; simp [ofItemPairs, ih]

theorem toRaw_ofItem (x : Item) : (ofItem x).toRaw = FullRawItem.ofRawItem x.toRaw := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => rfl
  | textIndef cs => rfl
  | array xs ih =>
    have hlist : ∀ l : List Item,
        (∀ y ∈ l, (ofItem y).toRaw = FullRawItem.ofRawItem y.toRaw) →
        toRawList (ofItemList l) = FullRawItem.ofRawItemList (Item.toRawList l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons y ys ihys =>
        simp [ofItemList, toRawList, Item.toRawList, FullRawItem.ofRawItemList,
          hl y (by simp), ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, toRaw, Item.toRaw, FullRawItem.ofRawItem, ofItemList_length, hlist xs ih]
  | arrayIndef xs ih =>
    have hlist : ∀ l : List Item,
        (∀ y ∈ l, (ofItem y).toRaw = FullRawItem.ofRawItem y.toRaw) →
        toRawList (ofItemList l) = FullRawItem.ofRawItemList (Item.toRawList l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons y ys ihys =>
        simp [ofItemList, toRawList, Item.toRawList, FullRawItem.ofRawItemList,
          hl y (by simp), ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, toRaw, Item.toRaw, FullRawItem.ofRawItem, hlist xs ih]
  | map kvs ih =>
    have hpairs : ∀ l : List (Item × Item),
        (∀ kv ∈ l, (ofItem kv.1).toRaw = FullRawItem.ofRawItem kv.1.toRaw ∧
          (ofItem kv.2).toRaw = FullRawItem.ofRawItem kv.2.toRaw) →
        toRawPairs (ofItemPairs l) = FullRawItem.ofRawItemPairs (Item.toRawPairs l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        simp [ofItemPairs, toRawPairs, Item.toRawPairs, FullRawItem.ofRawItemPairs,
          (hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2, ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, toRaw, Item.toRaw, FullRawItem.ofRawItem, ofItemPairs_length, hpairs kvs ih]
  | mapIndef kvs ih =>
    have hpairs : ∀ l : List (Item × Item),
        (∀ kv ∈ l, (ofItem kv.1).toRaw = FullRawItem.ofRawItem kv.1.toRaw ∧
          (ofItem kv.2).toRaw = FullRawItem.ofRawItem kv.2.toRaw) →
        toRawPairs (ofItemPairs l) = FullRawItem.ofRawItemPairs (Item.toRawPairs l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        simp [ofItemPairs, toRawPairs, Item.toRawPairs, FullRawItem.ofRawItemPairs,
          (hl (k, v) (by simp)).1, (hl (k, v) (by simp)).2, ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, toRaw, Item.toRaw, FullRawItem.ofRawItem, hpairs kvs ih]
  | tag t x ih => simp [ofItem, toRaw, Item.toRaw, FullRawItem.ofRawItem, ih]
  | simple v => rfl

end FullItem

theorem encodeFullPreferred_ofItem (x : Item) :
    encodeFullPreferred (FullItem.ofItem x) = encodePreferred x := by
  rw [encodeFullPreferred, FullItem.toRaw_ofItem, FullRawItem.encode_ofRawItem, encodePreferred]

private theorem fullEntryLt_ofItem (p q : Item × Item) :
    fullEntryLt (FullItem.ofItem p.1, FullItem.ofItem p.2)
      (FullItem.ofItem q.1, FullItem.ofItem q.2) = entryLt p q := by
  simp [fullEntryLt, entryLt, encodeFullPreferred_ofItem]

private theorem fullInsertUniq_ofItem (x : Item × Item) (l : List (Item × Item)) :
    fullInsertUniq (FullItem.ofItem x.1, FullItem.ofItem x.2) (FullItem.ofItemPairs l) =
      FullItem.ofItemPairs (insertUniq x l) := by
  induction l with
  | nil => obtain ⟨_, _⟩ := x; rfl
  | cons y ys ih =>
    obtain ⟨xk, xv⟩ := x; obtain ⟨yk, yv⟩ := y
    by_cases h1 : yk = xk ∧ yv = xv
    · obtain ⟨rfl, rfl⟩ := h1
      simp [FullItem.ofItemPairs, fullInsertUniq, insertUniq]
    · have h1' : ¬ (FullItem.ofItem yk = FullItem.ofItem xk ∧
          FullItem.ofItem yv = FullItem.ofItem xv) :=
        fun ⟨a, b⟩ => h1 ⟨FullItem.ofItem_injective a, FullItem.ofItem_injective b⟩
      simp only [FullItem.ofItemPairs, fullInsertUniq, insertUniq, Prod.mk.injEq,
        h1, h1', ↓reduceIte, fullEntryLt_ofItem (yk, yv) (xk, xv)]
      cases entryLt (yk, yv) (xk, xv) <;> simp [FullItem.ofItemPairs, ih]

private theorem fullSortUniq_ofItem (l : List (Item × Item)) :
    fullSortUniq (FullItem.ofItemPairs l) = FullItem.ofItemPairs (sortUniq l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    simp only [FullItem.ofItemPairs, fullSortUniq, sortUniq]
    rw [ih, fullInsertUniq_ofItem (k, v) (sortUniq xs)]

theorem FullItem.canon_ofItem (x : Item) :
    (FullItem.ofItem x).canon = FullItem.ofItem x.canon := by
  induction x using Item.rec' with
  | uint n => rfl
  | nint n => rfl
  | bytes p => rfl
  | text p => rfl
  | bytesIndef cs => rfl
  | textIndef cs => rfl
  | array xs ih =>
    have hlist : ∀ l : List Item,
        (∀ y ∈ l, (ofItem y).canon = ofItem y.canon) →
        canonList (ofItemList l) = ofItemList (Item.canonWithList false l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons y ys ihys =>
        have hy : (ofItem y).canon = ofItem (Item.canonWith false y) := hl y (by simp)
        simp [ofItemList, canonList, Item.canonWithList, hy,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, canon, Item.canon, Item.canonWith, hlist xs ih]
  | arrayIndef xs ih =>
    have hlist : ∀ l : List Item,
        (∀ y ∈ l, (ofItem y).canon = ofItem y.canon) →
        canonList (ofItemList l) = ofItemList (Item.canonWithList false l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons y ys ihys =>
        have hy : (ofItem y).canon = ofItem (Item.canonWith false y) := hl y (by simp)
        simp [ofItemList, canonList, Item.canonWithList, hy,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, canon, Item.canon, Item.canonWith, hlist xs ih]
  | map kvs ih =>
    have hpairs : ∀ l : List (Item × Item),
        (∀ kv ∈ l, (ofItem kv.1).canon = ofItem kv.1.canon ∧
          (ofItem kv.2).canon = ofItem kv.2.canon) →
        canonPairs (ofItemPairs l) = ofItemPairs (Item.canonWithPairs false l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        have hk : (ofItem k).canon = ofItem (Item.canonWith false k) := (hl (k, v) (by simp)).1
        have hv : (ofItem v).canon = ofItem (Item.canonWith false v) := (hl (k, v) (by simp)).2
        simp [ofItemPairs, canonPairs, Item.canonWithPairs, hk, hv,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, canon, Item.canon, Item.canonWith, hpairs kvs ih, fullSortUniq_ofItem]
  | mapIndef kvs ih =>
    have hpairs : ∀ l : List (Item × Item),
        (∀ kv ∈ l, (ofItem kv.1).canon = ofItem kv.1.canon ∧
          (ofItem kv.2).canon = ofItem kv.2.canon) →
        canonPairs (ofItemPairs l) = ofItemPairs (Item.canonWithPairs false l) := by
      intro l hl; induction l with
      | nil => rfl
      | cons kv ys ihys =>
        obtain ⟨k, v⟩ := kv
        have hk : (ofItem k).canon = ofItem (Item.canonWith false k) := (hl (k, v) (by simp)).1
        have hv : (ofItem v).canon = ofItem (Item.canonWith false v) := (hl (k, v) (by simp)).2
        simp [ofItemPairs, canonPairs, Item.canonWithPairs, hk, hv,
          ihys (fun z hz => hl z (by simp [hz]))]
    simp [ofItem, canon, Item.canon, Item.canonWith, hpairs kvs ih, fullSortUniq_ofItem]
  | tag t x ih => simp [ofItem, canon, Item.canon, Item.canonWith, ih]
  | simple v => rfl

/-- **Conservative extension of §5.6.1 `Item.Equiv`:** two float-free M1 items
are equivalent in `FullItem.Equiv` iff they are equivalent in M1 `Item.Equiv`. -/
theorem FullItem.equiv_ofItem_iff (x y : Item) :
    FullItem.Equiv (.ofItem x) (.ofItem y) ↔ Item.Equiv x y := by
  simp only [FullItem.Equiv, Item.Equiv, FullItem.canon_ofItem]
  exact ⟨fun h => FullItem.ofItem_injective h, congrArg FullItem.ofItem⟩

/-- Concrete §2 / §5.6.1 map-key equivalence witnesses:
* `1.0` (`0xf93c00`) and `1` (`0x01`) are **not** equivalent map keys;
* `0.0` (`0xf90000`) and `-0.0` (`0xf98000`) **are** equivalent map keys;
* `{0.0: 1, -0.0: 1}` and `{0.0: 1}` are `FullItem.Equiv` maps;
* `Infinity` across `f16`/`f32`/`f64` (`0xf97c00`, `0xfa7f800000`, `0xfb7ff0000000000000`)
  and `NaN` across `f16`/`f32`/`f64` (`0xf97e00`, `0xfa7fc00000`, `0xfb7ff8000000000000`)
  are `FullItem.Equiv`, whereas `nan64LowPayload` (`0xfb7ff8000000000001`) is **not**
  `FullItem.Equiv` to `0xf97e00`. -/
theorem float_dataModel_equiv_witnesses :
    ¬ FullItem.Equiv (.float (.half (Float16.ofBits 0x3c00))) (.uint 1) ∧
    FullItem.Equiv (.float (.half Float16.posZero)) (.float (.half Float16.negZero)) ∧
    FullItem.Equiv
      (.map [(.float (.half Float16.posZero), .uint 1),
             (.float (.half Float16.negZero), .uint 1)])
      (.map [(.float (.half Float16.posZero), .uint 1)]) ∧
    FullItem.Equiv (.float (.half Float16.posInf)) (.float (.single Float32.posInf)) ∧
    FullItem.Equiv (.float (.half Float16.posInf)) (.float (.double Float64.posInf)) ∧
    FullItem.Equiv (.float (.half Float16.canonicalNaN)) (.float (.single Float32.quietNaN)) ∧
    FullItem.Equiv (.float (.half Float16.canonicalNaN)) (.float (.double Float64.quietNaN)) ∧
    ¬ FullItem.Equiv (.float (.half Float16.canonicalNaN)) (.float (.double nan64LowPayload)) := by
  refine ⟨FullItem.not_equiv_float_uint _ _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  rw [FullItem.equiv_float_iff] at h
  unfold FloatEquiv CborFloat.toKeyVal at h
  revert h; intro h'; cases h'

/-! ## All 94 Appendix F.1 Malformed Sequences Refused by the Full Float-Enabled Parser -/

private def allParseFullRawNone (seqs : List (List UInt8)) : Bool :=
  seqs.all fun bs => (parseFullRaw bs).isNone

private theorem appendixF1Group01_full : allParseFullRawNone Vectors.appendixF1Group01.sequences = true := rfl
private theorem appendixF1Group02_full : allParseFullRawNone Vectors.appendixF1Group02.sequences = true := rfl
private theorem appendixF1Group03_full : allParseFullRawNone Vectors.appendixF1Group03.sequences = true := rfl
private theorem appendixF1Group04_full : allParseFullRawNone Vectors.appendixF1Group04.sequences = true := rfl
private theorem appendixF1Group05_full : allParseFullRawNone Vectors.appendixF1Group05.sequences = true := rfl
private theorem appendixF1Group06_full : allParseFullRawNone Vectors.appendixF1Group06.sequences = true := rfl
private theorem appendixF1Group07_full : allParseFullRawNone Vectors.appendixF1Group07.sequences = true := rfl
private theorem appendixF1Group08_full : allParseFullRawNone Vectors.appendixF1Group08.sequences = true := rfl
private theorem appendixF1Group09_full : allParseFullRawNone Vectors.appendixF1Group09.sequences = true := rfl
private theorem appendixF1Group10_full : allParseFullRawNone Vectors.appendixF1Group10.sequences = true := rfl
private theorem appendixF1Group11_full : allParseFullRawNone Vectors.appendixF1Group11.sequences = true := rfl
private theorem appendixF1Group12_full : allParseFullRawNone Vectors.appendixF1Group12.sequences = true := rfl
private theorem appendixF1Group13_full : allParseFullRawNone Vectors.appendixF1Group13.sequences = true := rfl
private theorem appendixF1Group14_full : allParseFullRawNone Vectors.appendixF1Group14.sequences = true := rfl

private theorem appendixF1_all_parseFullRaw_isNone :
    ∀ bs ∈ Vectors.appendixF1Vectors, (parseFullRaw bs).isNone = true := by
  intro bs hbs
  simp only [Vectors.appendixF1Vectors, Vectors.appendixF1Groups, List.map, List.mem_flatten] at hbs
  obtain ⟨seqs, hmem, hbs'⟩ := hbs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp appendixF1Group01_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group02_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group03_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group04_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group05_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group06_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group07_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group08_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group09_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group10_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group11_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group12_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group13_full bs hbs'
  · exact List.all_eq_true.mp appendixF1Group14_full bs hbs'

/-- **Universal Appendix F.1 refusal theorem on the full float-enabled CBOR parser:**
every one of the **94** malformed byte sequences in RFC 8949 Appendix F.1
(including Group 1's 3 truncated float heads `f900`, `fa0000`, `fb000000`)
returns `none` under `parseFullRaw`, `parseFullWellFormed`, and
`decodeFullDeterministic`, while complete 2/4/8-byte float wires succeed. -/
theorem appendixF1_all_refused_full :
    (∀ bs ∈ Vectors.appendixF1Vectors,
      parseFullRaw bs = none ∧
      parseFullWellFormed bs = none ∧
      decodeFullDeterministic bs = none) ∧
    parseFullWellFormed [0xf9, 0x00, 0x00] = some (.float (.half Float16.posZero)) ∧
    parseFullWellFormed [0xfa, 0x00, 0x00, 0x00, 0x00] = some (.float (.single Float32.posZero)) ∧
    parseFullWellFormed [0xfb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] =
      some (.float (.double Float64.posZero)) := by
  rw [← ofBits_zero_eq_posZero16, ← ofBits_zero_eq_posZero32, ← ofBits_zero_eq_posZero64]
  refine ⟨fun bs hbs => ?_, rfl, rfl, rfl⟩
  have hnone : (parseFullRaw bs).isNone = true := appendixF1_all_parseFullRaw_isNone bs hbs
  have hp : parseFullRaw bs = none := Option.isNone_iff_eq_none.mp hnone
  exact ⟨hp, by simp [parseFullWellFormed, hp], by simp [decodeFullDeterministic, parseFullWellFormed, hp]⟩

end Cbor.Rfc8949
