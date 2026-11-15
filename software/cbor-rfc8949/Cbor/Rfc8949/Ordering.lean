/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Indefinite

/-!
# Map-key ordering profiles: Core (§4.2.1), Length-first (§4.2.3), and CTAP2

RFC 8949 defines two deterministic map-key orders and contrasts them with FIDO
CTAP2's canonical CBOR order:

1. **Core deterministic order (§4.2.1):** bytewise lexicographic order `lexLt`
   on the keys' deterministic encodings.
2. **Length-first order (§4.2.3, formerly RFC 7049 §3.9):** shorter encoded
   byte sequences first, ties broken bytewise (`lengthFirstLt`).
3. **CTAP2 canonical CBOR order (FIDO CTAP2 §6; discussed in §4.2.3):** major
   type first, then encoded byte length, then bytewise (`ctap2Lt`).

This module proves the exact relationship between the profiles (ticket #34
deliverable 5):

* **Atomic agreement (`order_core_eq_ctap2_atomic`):** on well-formed atomic
  keys (major types `{0, 1, 2, 3, 7}`), core bytewise order and CTAP2 order
  agree identically on `encodeDeterministic`. Variants are also given for
  `IndefBounded` indefinite strings (`order_core_eq_ctap2_atomic_indefBounded`),
  deterministic wires (`order_core_eq_ctap2_atomic_wire`), and stable map
  sorting (`sortBy_core_eq_ctap2_atomic`).
* **Compound divergence (`order_core_ne_ctap2_compound`):** on compound keys
  (major types `{4, 5, 6}`), core bytewise order and CTAP2 order diverge. RFC
  8949 §4.2.1's own example pair `[100]` (`81 18 64`, 3 bytes) vs `[-1]`
  (`81 20`, 2 bytes) sorts `[100]` before `[-1]` under §4.2.1 (`0x18 < 0x20`),
  whereas both CTAP2 and §4.2.3 sort `[-1]` before `[100]` (`2 < 3`).
* **Cross-major length-first divergence (`order_core_ne_lengthFirst_atomic`):**
  `100` (`18 64`, 2 bytes, major 0) precedes `-1` (`20`, 1 byte, major 1)
  under both §4.2.1 and CTAP2, while `-1` precedes `100` under §4.2.3.
-/

namespace Cbor.Rfc8949

/-! ## Item major type, atomic predicate, and profile key comparators -/

namespace Item

/-- CBOR major type (`0..7`, RFC 8949 §3.1). Indefinite-length strings, arrays,
and maps share the major type of their definite counterparts (`2..5`). -/
def majorType : Item → Nat
  | .uint _ => 0
  | .nint _ => 1
  | .bytes _ | .bytesIndef _ => 2
  | .text _ | .textIndef _ => 3
  | .array _ | .arrayIndef _ => 4
  | .map _ | .mapIndef _ => 5
  | .tag _ _ => 6
  | .simple _ => 7

/-- Definite atomic CBOR items: major types `{0, 1, 2, 3, 7}` (unsigned and
negative integers, definite byte and text strings, and simple values). -/
def isAtomic : Item → Bool
  | .uint _ | .nint _ | .bytes _ | .text _ | .simple _ => true
  | _ => false

theorem isAtomic_iff (x : Item) :
    x.isAtomic = true ↔ x.Definite ∧ x.majorType ∈ ([0, 1, 2, 3, 7] : List Nat) := by
  cases x <;> simp [isAtomic, Definite, majorType]

theorem majorType_lt_eight (x : Item) : x.majorType < 8 := by
  cases x <;> simp [majorType]

end Item

/-- Core deterministic key comparator (§4.2.1). -/
def coreKeyOrder (x y : Item) : Bool :=
  lexLt (encodeDeterministic x) (encodeDeterministic y)

/-- Length-first deterministic key comparator (§4.2.3 / RFC 7049 §3.9). -/
def lengthFirstKeyOrder (x y : Item) : Bool :=
  lengthFirstLt (encodeDeterministic x) (encodeDeterministic y)

/-- CTAP2 canonical CBOR key comparator (FIDO CTAP2 §6; §4.2.3). -/
def ctap2KeyOrder (x y : Item) : Bool :=
  ctap2Lt (encodeDeterministic x) (encodeDeterministic y)

/-! ## Big-endian and preferred-head byte order lemmas -/

theorem beBytes_mod (k n : Nat) : beBytes k (n % 256 ^ k) = beBytes k n :=
  beValue_inj (by simp [beBytes_length]) (by simp [beValue_beBytes])

/-- Big-endian `k`-byte encodings preserve strict order on `< 256 ^ k`,
regardless of any trailing suffixes. -/
theorem lexLt_beBytes : ∀ (k : Nat) {a b : Nat}, a < b → b < 256 ^ k →
    ∀ (r₁ r₂ : List UInt8), lexLt (beBytes k a ++ r₁) (beBytes k b ++ r₂) = true
  | 0, _, _, hab, hb, _, _ => by simp at hb; omega
  | k + 1, a, b, hab, hb, r₁, r₂ => by
    have hp : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
    have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hqb : b / 256 ^ k < 256 := by
      apply Nat.lt_of_not_le
      intro hc
      have hle := Nat.mul_le_mul_left (256 ^ k) hc
      have hdm := Nat.div_add_mod b (256 ^ k)
      omega
    have hqa : a / 256 ^ k ≤ b / 256 ^ k := Nat.div_le_div_right (by omega)
    have ha_byte : (UInt8.ofNat (a / 256 ^ k % 256)).toNat = a / 256 ^ k := by
      rw [toNat_ofNat_byte, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have hb_byte : (UInt8.ofNat (b / 256 ^ k % 256)).toNat = b / 256 ^ k := by
      rw [toNat_ofNat_byte, Nat.mod_mod, Nat.mod_eq_of_lt hqb]
    simp only [beBytes, List.cons_append]
    rw [lexLt_cons_cons]
    by_cases hqlt : a / 256 ^ k < b / 256 ^ k
    · left; omega
    · right
      have hqeq : a / 256 ^ k = b / 256 ^ k := by omega
      refine ⟨UInt8.toNat_inj.mp (by omega), ?_⟩
      have hda := Nat.div_add_mod a (256 ^ k)
      have hdb := Nat.div_add_mod b (256 ^ k)
      rw [hqeq] at hda
      have hrlt : a % 256 ^ k < b % 256 ^ k := by omega
      have hrbound : b % 256 ^ k < 256 ^ k := Nat.mod_lt b hpos
      rw [← beBytes_mod k a, ← beBytes_mod k b]
      exact lexLt_beBytes k hrlt hrbound r₁ r₂

theorem Width.eq_of_extra_eq {w₁ w₂ : Width} (h : w₁.extra = w₂.extra) : w₁ = w₂ := by
  cases w₁ <;> cases w₂ <;> simp [Width.extra] at h ⊢

theorem Width.preferred_extra_mono {a b : Nat} (hab : a ≤ b) :
    (Width.preferred a).extra ≤ (Width.preferred b).extra := by
  by_cases ha1 : a < 24 <;> by_cases ha2 : a < 2 ^ 8 <;>
    by_cases ha3 : a < 2 ^ 16 <;> by_cases ha4 : a < 2 ^ 32 <;>
  by_cases hb1 : b < 24 <;> by_cases hb2 : b < 2 ^ 8 <;>
    by_cases hb3 : b < 2 ^ 16 <;> by_cases hb4 : b < 2 ^ 32 <;>
    simp [Width.preferred, Width.extra, ha1, ha2, ha3, ha4, hb1, hb2, hb3, hb4] <;>
    omega

theorem Width.preferred_ai_lt_of_extra_lt {a b : Nat}
    (h : (Width.preferred a).extra < (Width.preferred b).extra) :
    (Width.preferred a).ai a < (Width.preferred b).ai b := by
  by_cases ha1 : a < 24 <;> by_cases ha2 : a < 2 ^ 8 <;>
    by_cases ha3 : a < 2 ^ 16 <;> by_cases ha4 : a < 2 ^ 32 <;>
  by_cases hb1 : b < 24 <;> by_cases hb2 : b < 2 ^ 8 <;>
    by_cases hb3 : b < 2 ^ 16 <;> by_cases hb4 : b < 2 ^ 32 <;>
    simp [Width.preferred, Width.extra, Width.ai, ha1, ha2, ha3, ha4, hb1, hb2, hb3, hb4] at h ⊢ <;>
    omega

theorem Width.preferred_fits_of_lt {n : Nat} (hn : n < 2 ^ 64) :
    (Width.preferred n).fits n = true := by
  unfold Width.preferred
  split <;> (try split) <;> (try split) <;> (try split) <;> simp [Width.fits] <;> omega

/-- Preferred heads of one major type sort in strictly increasing order of
their argument `n < 2 ^ 64`, regardless of trailing payload bytes. -/
theorem lexLt_encodeHead_preferred_append {m a b : Nat} (hm : m < 8)
    (hab : a < b) (hb : b < 2 ^ 64) (r₁ r₂ : List UInt8) :
    lexLt (encodeHead m (Width.preferred a) a ++ r₁)
      (encodeHead m (Width.preferred b) b ++ r₂) = true := by
  have ha : a < 2 ^ 64 := by omega
  have hf₁ := Width.preferred_fits_of_lt ha
  have hf₂ := Width.preferred_fits_of_lt hb
  have hai₁ := Width.ai_lt hf₁
  have hai₂ := Width.ai_lt hf₂
  have hb₁ : (UInt8.ofNat (m * 32 + (Width.preferred a).ai a)).toNat =
      m * 32 + (Width.preferred a).ai a := by
    rw [toNat_ofNat_byte]; omega
  have hb₂ : (UInt8.ofNat (m * 32 + (Width.preferred b).ai b)).toNat =
      m * 32 + (Width.preferred b).ai b := by
    rw [toNat_ofNat_byte]; omega
  simp only [encodeHead, List.cons_append]
  rw [lexLt_cons_cons]
  have hextra := Width.preferred_extra_mono (Nat.le_of_lt hab)
  by_cases hexlt : (Width.preferred a).extra < (Width.preferred b).extra
  · left
    have hailt := Width.preferred_ai_lt_of_extra_lt hexlt
    omega
  · have hexeq : (Width.preferred a).extra = (Width.preferred b).extra := by omega
    have hweq : Width.preferred a = Width.preferred b := Width.eq_of_extra_eq hexeq
    rw [hweq] at hb₁ hf₁ ⊢
    generalize Width.preferred b = w at hb₁ hb₂ hf₂ ⊢
    cases w with
    | inline =>
      simp only [Width.ai] at hb₁ hb₂ ⊢
      left; omega
    | w1 | w2 | w4 | w8 =>
      right
      exact ⟨rfl, lexLt_beBytes _ hab (Width.fits_lt hf₂ (by decide)) r₁ r₂⟩

theorem wireMajor_ofNat {m ai : Nat} (hm : m < 8) (hai : ai < 32) (rest : List UInt8) :
    wireMajor (UInt8.ofNat (m * 32 + ai) :: rest) = m := by
  simp only [wireMajor, toNat_ofNat_byte]
  omega

theorem wireMajor_encodeHead {m n : Nat} {w : Width} (hm : m < 8) (hai : w.ai n < 32) :
    wireMajor (encodeHead m w n) = m :=
  wireMajor_ofNat hm hai _

theorem wireMajor_encodeHead_append {m n : Nat} {w : Width} (hm : m < 8) (hai : w.ai n < 32)
    (rest : List UInt8) : wireMajor (encodeHead m w n ++ rest) = m := by
  simp only [encodeHead, List.cons_append]
  exact wireMajor_ofNat hm hai _

/-- Initial byte carries major type in its upper 3 bits, so any wire with a
smaller valid major type sorts strictly earlier bytewise. -/
theorem lexLt_of_wireMajor_lt : ∀ {a b : List UInt8},
    a ≠ [] → b ≠ [] → wireMajor a < wireMajor b → lexLt a b = true
  | [], _, ha, _, _ => absurd rfl ha
  | _, [], _, hb, _ => absurd rfl hb
  | x :: xs, y :: ys, _, _, hlt => by
    simp only [wireMajor] at hlt
    rw [lexLt_cons_cons]
    left
    omega

theorem encodeDeterministic_atomic_nonempty {x : Item} (hax : x.isAtomic = true) :
    encodeDeterministic x ≠ [] := by
  cases x <;> simp [Item.isAtomic] at hax <;>
    simp [encodeDeterministic, encodePreferred, Item.normalise, Item.toRaw, RawItem.encode,
      encodeHead]

theorem wireMajor_encodeDeterministic_atomic {x : Item} (hx : x.WF) (hax : x.isAtomic = true) :
    wireMajor (encodeDeterministic x) = x.majorType := by
  cases x with
  | uint n =>
    have hf := Width.preferred_fits_of_lt hx
    exact wireMajor_encodeHead (by decide) (by have := Width.ai_lt hf; omega)
  | nint n =>
    have hf := Width.preferred_fits_of_lt hx
    exact wireMajor_encodeHead (by decide) (by have := Width.ai_lt hf; omega)
  | bytes p =>
    have hf := Width.preferred_fits_of_lt hx
    exact wireMajor_encodeHead_append (by decide) (by have := Width.ai_lt hf; omega) p
  | text p =>
    have hf := Width.preferred_fits_of_lt hx
    exact wireMajor_encodeHead_append (by decide) (by have := Width.ai_lt hf; omega) p
  | simple v =>
    simp only [Item.WF] at hx
    rcases hx with hv | ⟨hv1, hv2⟩
    · have hw : simpleWidth v = .inline := by simp [simpleWidth, hv]
      simp only [encodeDeterministic, encodePreferred, Item.normalise, Item.toRaw,
        RawItem.encode, hw, Item.majorType]
      exact wireMajor_encodeHead (by decide) (by simp [Width.ai]; omega)
    · have hw : simpleWidth v = .w1 := by simp [simpleWidth]; omega
      simp only [encodeDeterministic, encodePreferred, Item.normalise, Item.toRaw,
        RawItem.encode, hw, Item.majorType]
      exact wireMajor_encodeHead (by decide) (by simp [Width.ai])
  | bytesIndef _ | textIndef _ | array _ | arrayIndef _ | map _ | mapIndef _ | tag _ _ =>
    simp [Item.isAtomic] at hax

/-! ## Within-major-type agreement between `lexLt` and `lengthFirstLt` -/

private theorem lengthFirstLt_eq_of_length_eq {a b : List UInt8} (h : a.length = b.length) :
    lengthFirstLt a b = lexLt a b := by
  simp [lengthFirstLt, h]

private theorem lexLt_eq_lengthFirstLt_int (m : Nat) (hm : m < 8) {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    lexLt (encodeHead m (Width.preferred a) a) (encodeHead m (Width.preferred b) b) =
      lengthFirstLt (encodeHead m (Width.preferred a) a) (encodeHead m (Width.preferred b) b) := by
  by_cases hab : a < b
  · have hlex : lexLt (encodeHead m (Width.preferred a) a)
        (encodeHead m (Width.preferred b) b) = true := by
      simpa using lexLt_encodeHead_preferred_append hm hab hb [] []
    have hlen : (encodeHead m (Width.preferred a) a).length ≤
        (encodeHead m (Width.preferred b) b).length := by
      simp only [encodeHead_length]
      have := Width.preferred_extra_mono (Nat.le_of_lt hab)
      omega
    by_cases hlt : (encodeHead m (Width.preferred a) a).length <
        (encodeHead m (Width.preferred b) b).length
    · rw [hlex, eq_comm, lengthFirstLt_iff]; exact Or.inl hlt
    · rw [lengthFirstLt_eq_of_length_eq (by omega)]
  · by_cases hba : b < a
    · have hlex : lexLt (encodeHead m (Width.preferred b) b)
          (encodeHead m (Width.preferred a) a) = true := by
        simpa using lexLt_encodeHead_preferred_append hm hba ha [] []
      have hlen : (encodeHead m (Width.preferred b) b).length ≤
          (encodeHead m (Width.preferred a) a).length := by
        simp only [encodeHead_length]
        have := Width.preferred_extra_mono (Nat.le_of_lt hba)
        omega
      by_cases hlt : (encodeHead m (Width.preferred b) b).length <
          (encodeHead m (Width.preferred a) a).length
      · have hlf : lengthFirstLt (encodeHead m (Width.preferred b) b)
            (encodeHead m (Width.preferred a) a) = true :=
          (lengthFirstLt_iff _ _).2 (Or.inl hlt)
        rw [lexLt_asymm hlex, lengthFirstLt_asymm hlf]
      · rw [lengthFirstLt_eq_of_length_eq (by omega)]
    · have heq : a = b := by omega
      subst heq
      simp [lexLt_irrefl, lengthFirstLt_irrefl]

private theorem lexLt_eq_lengthFirstLt_string (m : Nat) (hm : m < 8) {p₁ p₂ : List UInt8}
    (hp₁ : p₁.length < 2 ^ 64) (hp₂ : p₂.length < 2 ^ 64) :
    lexLt (encodeHead m (Width.preferred p₁.length) p₁.length ++ p₁)
      (encodeHead m (Width.preferred p₂.length) p₂.length ++ p₂) =
    lengthFirstLt (encodeHead m (Width.preferred p₁.length) p₁.length ++ p₁)
      (encodeHead m (Width.preferred p₂.length) p₂.length ++ p₂) := by
  by_cases hab : p₁.length < p₂.length
  · have hlex := lexLt_encodeHead_preferred_append hm hab hp₂ p₁ p₂
    have hlt : (encodeHead m (Width.preferred p₁.length) p₁.length ++ p₁).length <
        (encodeHead m (Width.preferred p₂.length) p₂.length ++ p₂).length := by
      simp only [List.length_append, encodeHead_length]
      have := Width.preferred_extra_mono (Nat.le_of_lt hab)
      omega
    rw [hlex, eq_comm, lengthFirstLt_iff]
    exact Or.inl hlt
  · by_cases hba : p₂.length < p₁.length
    · have hlex := lexLt_encodeHead_preferred_append hm hba hp₁ p₂ p₁
      have hlt : (encodeHead m (Width.preferred p₂.length) p₂.length ++ p₂).length <
          (encodeHead m (Width.preferred p₁.length) p₁.length ++ p₁).length := by
        simp only [List.length_append, encodeHead_length]
        have := Width.preferred_extra_mono (Nat.le_of_lt hba)
        omega
      have hlf : lengthFirstLt (encodeHead m (Width.preferred p₂.length) p₂.length ++ p₂)
          (encodeHead m (Width.preferred p₁.length) p₁.length ++ p₁) = true :=
        (lengthFirstLt_iff _ _).2 (Or.inl hlt)
      rw [lexLt_asymm hlex, lengthFirstLt_asymm hlf]
    · have heq : p₁.length = p₂.length := by omega
      apply (lengthFirstLt_eq_of_length_eq _).symm
      simp [encodeHead_length, heq]

private theorem lexLt_eq_lengthFirstLt_simple {v₁ v₂ : Nat}
    (hv₁ : v₁ < 24 ∨ (32 ≤ v₁ ∧ v₁ < 256)) (hv₂ : v₂ < 24 ∨ (32 ≤ v₂ ∧ v₂ < 256)) :
    lexLt (encodeHead 7 (simpleWidth v₁) v₁) (encodeHead 7 (simpleWidth v₂) v₂) =
      lengthFirstLt (encodeHead 7 (simpleWidth v₁) v₁) (encodeHead 7 (simpleWidth v₂) v₂) := by
  rcases hv₁ with h1 | ⟨h1lo, h1hi⟩ <;> rcases hv₂ with h2 | ⟨h2lo, h2hi⟩
  · have hw₁ : simpleWidth v₁ = .inline := by simp [simpleWidth, h1]
    have hw₂ : simpleWidth v₂ = .inline := by simp [simpleWidth, h2]
    apply (lengthFirstLt_eq_of_length_eq _).symm
    simp [encodeHead_length, hw₁, hw₂]
  · have hw₁ : simpleWidth v₁ = .inline := by simp [simpleWidth, h1]
    have hw₂ : simpleWidth v₂ = .w1 := by simp [simpleWidth]; omega
    have hlen : (encodeHead 7 (simpleWidth v₁) v₁).length <
        (encodeHead 7 (simpleWidth v₂) v₂).length := by
      simp [encodeHead_length, hw₁, hw₂, Width.extra]
    have hlex : lexLt (encodeHead 7 (simpleWidth v₁) v₁)
        (encodeHead 7 (simpleWidth v₂) v₂) = true := by
      simp only [hw₁, hw₂, encodeHead, Width.ai, Width.extra, beBytes]
      rw [lexLt_cons_cons]
      left
      simp only [toNat_ofNat_byte]
      omega
    rw [hlex, eq_comm, lengthFirstLt_iff]
    exact Or.inl hlen
  · have hw₁ : simpleWidth v₁ = .w1 := by simp [simpleWidth]; omega
    have hw₂ : simpleWidth v₂ = .inline := by simp [simpleWidth, h2]
    have hlen : (encodeHead 7 (simpleWidth v₂) v₂).length <
        (encodeHead 7 (simpleWidth v₁) v₁).length := by
      simp [encodeHead_length, hw₁, hw₂, Width.extra]
    have hlex : lexLt (encodeHead 7 (simpleWidth v₂) v₂)
        (encodeHead 7 (simpleWidth v₁) v₁) = true := by
      simp only [hw₁, hw₂, encodeHead, Width.ai, Width.extra, beBytes]
      rw [lexLt_cons_cons]
      left
      simp only [toNat_ofNat_byte]
      omega
    have hlf : lengthFirstLt (encodeHead 7 (simpleWidth v₂) v₂)
        (encodeHead 7 (simpleWidth v₁) v₁) = true :=
      (lengthFirstLt_iff _ _).2 (Or.inl hlen)
    rw [lexLt_asymm hlex, lengthFirstLt_asymm hlf]
  · have hw₁ : simpleWidth v₁ = .w1 := by simp [simpleWidth]; omega
    have hw₂ : simpleWidth v₂ = .w1 := by simp [simpleWidth]; omega
    apply (lengthFirstLt_eq_of_length_eq _).symm
    simp [encodeHead_length, hw₁, hw₂]

/-- Within any single atomic major type (`{0, 1, 2, 3, 7}`), bytewise order
(`§4.2.1`) and length-first order (`§4.2.3`) agree identically on deterministic
encodings. -/
theorem order_core_eq_lengthFirst_same_major_atomic {x y : Item}
    (hx : x.WF) (hy : y.WF) (hax : x.isAtomic = true) (hay : y.isAtomic = true)
    (hm : x.majorType = y.majorType) :
    lexLt (encodeDeterministic x) (encodeDeterministic y) =
      lengthFirstLt (encodeDeterministic x) (encodeDeterministic y) := by
  cases x <;> cases y <;> simp [Item.isAtomic, Item.majorType] at hax hay hm
  · exact lexLt_eq_lengthFirstLt_int 0 (by decide) hx hy
  · exact lexLt_eq_lengthFirstLt_int 1 (by decide) hx hy
  · exact lexLt_eq_lengthFirstLt_string 2 (by decide) hx hy
  · exact lexLt_eq_lengthFirstLt_string 3 (by decide) hx hy
  · exact lexLt_eq_lengthFirstLt_simple hx hy

/-! ## Deliverable 5 main theorems: atomic agreement and compound divergence -/

/-- **Atomic profile agreement (RFC 8949 §4.2.3 / ticket #34 deliverable 5):**
On well-formed atomic CBOR keys (major types `{0, 1, 2, 3, 7}`), core
deterministic bytewise order (`lexLt`, §4.2.1) and CTAP2 canonical CBOR order
(`ctap2Lt`, FIDO CTAP2 §6) agree identically on `encodeDeterministic`. -/
theorem order_core_eq_ctap2_atomic {x y : Item}
    (hx : x.WF) (hy : y.WF) (hax : x.isAtomic = true) (hay : y.isAtomic = true) :
    lexLt (encodeDeterministic x) (encodeDeterministic y) =
      ctap2Lt (encodeDeterministic x) (encodeDeterministic y) := by
  have hmx := wireMajor_encodeDeterministic_atomic hx hax
  have hmy := wireMajor_encodeDeterministic_atomic hy hay
  have hnx := encodeDeterministic_atomic_nonempty hax
  have hny := encodeDeterministic_atomic_nonempty hay
  unfold ctap2Lt
  rw [hmx, hmy]
  by_cases hlt : x.majorType < y.majorType
  · simp only [hlt, ↓reduceIte]
    exact lexLt_of_wireMajor_lt hnx hny (by rw [hmx, hmy]; exact hlt)
  · simp only [hlt, ↓reduceIte]
    by_cases heq : x.majorType = y.majorType
    · simp only [heq, ↓reduceIte]
      exact order_core_eq_lengthFirst_same_major_atomic hx hy hax hay heq
    · simp only [heq, ↓reduceIte]
      have hgt : y.majorType < x.majorType := by omega
      exact lexLt_asymm (lexLt_of_wireMajor_lt hny hnx (by rw [hmx, hmy]; exact hgt))

/-- Atomic agreement extended to `IndefBounded` indefinite strings (major types
`{0, 1, 2, 3, 7}` arbitrary `Item`s, definite or chunked). -/
theorem order_core_eq_ctap2_atomic_indefBounded {x y : Item}
    (hx : x.WF) (hy : y.WF) (hbx : x.IndefBounded) (hby : y.IndefBounded)
    (hmx : x.majorType ∈ ([0, 1, 2, 3, 7] : List Nat))
    (hmy : y.majorType ∈ ([0, 1, 2, 3, 7] : List Nat)) :
    lexLt (encodeDeterministic x) (encodeDeterministic y) =
      ctap2Lt (encodeDeterministic x) (encodeDeterministic y) := by
  have hx_norm_wf : x.normalise.WF := by
    cases x <;> simp [Item.majorType] at hmx <;> (first | exact hx | exact hbx)
  have hy_norm_wf : y.normalise.WF := by
    cases y <;> simp [Item.majorType] at hmy <;> (first | exact hy | exact hby)
  have hx_norm_at : x.normalise.isAtomic = true := by
    cases x <;> simp [Item.majorType] at hmx <;> rfl
  have hy_norm_at : y.normalise.isAtomic = true := by
    cases y <;> simp [Item.majorType] at hmy <;> rfl
  rw [← encodeDeterministic_normalise x, ← encodeDeterministic_normalise y]
  exact order_core_eq_ctap2_atomic hx_norm_wf hy_norm_wf hx_norm_at hy_norm_at

/-- Wire-level atomic agreement: on any two valid deterministic encodings
whose decoded items have atomic major types `{0, 1, 2, 3, 7}`, `lexLt` and
`ctap2Lt` agree identically. -/
theorem order_core_eq_ctap2_atomic_wire {bs₁ bs₂ : List UInt8} {x y : Item}
    (hx : decodeDeterministic bs₁ = some x) (hy : decodeDeterministic bs₂ = some y)
    (hmx : x.majorType ∈ ([0, 1, 2, 3, 7] : List Nat))
    (hmy : y.majorType ∈ ([0, 1, 2, 3, 7] : List Nat)) :
    lexLt bs₁ bs₂ = ctap2Lt bs₁ bs₂ := by
  obtain ⟨henc₁, hdet₁, _, hwf₁⟩ := encodeDeterministic_of_decodeDeterministic hx
  obtain ⟨henc₂, hdet₂, _, hwf₂⟩ := encodeDeterministic_of_decodeDeterministic hy
  have hax : x.isAtomic = true := by
    cases x <;> simp [Item.majorType, Item.isDeterministic] at hmx hdet₁ <;> rfl
  have hay : y.isAtomic = true := by
    cases y <;> simp [Item.majorType, Item.isDeterministic] at hmy hdet₂ <;> rfl
  rw [← henc₁, ← henc₂]
  exact order_core_eq_ctap2_atomic hwf₁ hwf₂ hax hay

/-- Stable sorting of well-formed atomic map entries produces the exact same
list under core order (§4.2.1) and CTAP2 order. -/
theorem sortBy_core_eq_ctap2_atomic (kvs : List (Item × Item))
    (hwf : ∀ kv ∈ kvs, kv.1.WF ∧ kv.1.isAtomic = true) :
    sortBy (fun p q : Item × Item => coreKeyOrder p.1 q.1) kvs =
      sortBy (fun p q : Item × Item => ctap2KeyOrder p.1 q.1) kvs :=
  sortBy_congr kvs fun p hp q hq =>
    order_core_eq_ctap2_atomic (hwf p hp).1 (hwf q hq).1 (hwf p hp).2 (hwf q hq).2

/-- `[100]` from RFC 8949 §4.2.1's map-key ordering example (`81 18 64`). -/
def compoundKeyArray100 : Item := .array [.uint 100]

/-- `[-1]` from RFC 8949 §4.2.1's map-key ordering example (`81 20`). -/
def compoundKeyArrayNeg1 : Item := .array [.nint 0]

/-- **Compound profile divergence (RFC 8949 §4.2.1 / §4.2.3; ticket #34
deliverable 5):**
Core bytewise order (`lexLt`) and CTAP2 order (`ctap2Lt`) disagree on the
deterministic compound keys `[100]` (`[0x81, 0x18, 0x64]`, 3 bytes) and `[-1]`
(`[0x81, 0x20]`, 2 bytes) from RFC 8949 §4.2.1:
* both keys are accepted by `decodeDeterministic`;
* `lexLt` places `[100]` strictly before `[-1]` (`0x18 < 0x20` at byte 1);
* `ctap2Lt` (and `lengthFirstLt`) places `[-1]` strictly before `[100]`
  (same major type 4, `2 < 3` bytes);
* hence `lexLt` and `ctap2Lt` evaluate to opposite Booleans on this pair. -/
theorem order_core_ne_ctap2_compound :
    let w100 := encodeDeterministic compoundKeyArray100
    let wNeg1 := encodeDeterministic compoundKeyArrayNeg1
    w100 = [0x81, 0x18, 0x64] ∧
    wNeg1 = [0x81, 0x20] ∧
    decodeDeterministic w100 = some compoundKeyArray100 ∧
    decodeDeterministic wNeg1 = some compoundKeyArrayNeg1 ∧
    lexLt w100 wNeg1 = true ∧
    ctap2Lt w100 wNeg1 = false ∧
    ctap2Lt wNeg1 w100 = true ∧
    lengthFirstLt w100 wNeg1 = false ∧
    lexLt w100 wNeg1 ≠ ctap2Lt w100 wNeg1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Universal core-vs-CTAP2 agreement on all deterministic keys is false:
`compoundKeyArray100` and `compoundKeyArrayNeg1` refute it. -/
theorem not_order_core_eq_ctap2_all :
    ¬ (∀ x y : Item, x.WF → y.WF → x.isDeterministic = true → y.isDeterministic = true →
        lexLt (encodeDeterministic x) (encodeDeterministic y) =
          ctap2Lt (encodeDeterministic x) (encodeDeterministic y)) := by
  intro hall
  have hw1 : compoundKeyArray100.WF := by
    simp [compoundKeyArray100, Item.WF, Item.WFList]
  have hw2 : compoundKeyArrayNeg1.WF := by
    simp [compoundKeyArrayNeg1, Item.WF, Item.WFList]
  have h := hall compoundKeyArray100 compoundKeyArrayNeg1 hw1 hw2 rfl rfl
  exact order_core_ne_ctap2_compound.2.2.2.2.2.2.2.2 h

/-- Cross-major atomic divergence between §4.2.1/CTAP2 and §4.2.3
(`lengthFirstLt`): `100` (`[0x18, 0x64]`, 2 bytes, major 0) precedes `-1`
(`[0x20]`, 1 byte, major 1) under both `lexLt` and `ctap2Lt`, whereas `-1`
precedes `100` under `lengthFirstLt`. -/
theorem order_core_ne_lengthFirst_atomic :
    let w100 := encodeDeterministic (.uint 100)
    let wNeg1 := encodeDeterministic (.nint 0)
    w100 = [0x18, 0x64] ∧
    wNeg1 = [0x20] ∧
    lexLt w100 wNeg1 = true ∧
    ctap2Lt w100 wNeg1 = true ∧
    lengthFirstLt w100 wNeg1 = false ∧
    lexLt w100 wNeg1 ≠ lengthFirstLt w100 wNeg1 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩

end Cbor.Rfc8949
