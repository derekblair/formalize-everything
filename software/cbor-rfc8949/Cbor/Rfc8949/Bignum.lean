/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Cbor.Rfc8949.Deterministic

/-!
# Tag 2/3 bignums (§3.4.3, §4.2.2)

A bignum is tag 2 or tag 3 around a byte string read in network byte order
as `n`; its value is `n` (tag 2) or `-1 - n` (tag 3). Leading zero bytes
are allowed and do not change the value ("Decoders that understand these
tags MUST be able to decode bignums that do have leading zeroes"); the
generic `parseWellFormed` keeps such strings unchanged. Contents of other
types are invalid (`bignumValue?` is `none`). An indefinite-length byte
string is a byte string data item, so its concatenated chunks count.

Preferred serialization (§3.4.3, recommended by §4.2.2) uses major types 0
and 1 whenever they can hold the integer, so a bignum appears exactly
outside `-2^64 .. 2^64 - 1`. `encodeInt` is that serialization, and the
boundary theorems are stated in the form of ticket #34's binding amendment
I3: tag 2 iff `z ≥ 2^64` (`m = z.toNat ≥ 2^64`), tag 3 iff `z < -2^64`
(`m = (-1 - z).toNat ≥ 2^64`), content the minimal big-endian bytes of `m`
with no leading `0x00` and at least 9 bytes. In particular `-2^64` (RFC 8949
Appendix A, row 13) is major type 1, which the withdrawn `|z| ≥ 2^64` form
would misclassify (`dossier_form_misclassifies_row13`).
-/

namespace Cbor.Rfc8949

/-- Number of bytes in the minimal big-endian representation of `n`
(`0` for `n = 0`). The first argument is fuel; `byteLen` supplies `n`, which
is always enough. -/
def byteLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else byteLenAux k (n / 256) + 1

/-- Length of the minimal big-endian representation of `n`. -/
def byteLen (n : Nat) : Nat := byteLenAux n n

/-- The minimal big-endian bytes of `n`: no leading zero byte, empty for 0
(§3.4.3 preferred serialization of the bignum's byte string). -/
def minimalBE (n : Nat) : List UInt8 := beBytes (byteLen n) n

namespace Item

/-- Content of a byte-string item: the bytes of a definite string, or the
concatenation of the chunks of an indefinite one (§3.2.3). -/
def byteContent? : Item → Option (List UInt8)
  | .bytes p => some p
  | .bytesIndef cs => some cs.flatten
  | _ => none

/-- §3.4.3: value of a bignum. `none` for anything that is not tag 2 or 3
around a byte string. -/
def bignumValue? : Item → Option Int
  | .tag 2 x => x.byteContent?.map fun p => (beValue p : Int)
  | .tag 3 x => x.byteContent?.map fun p => -1 - (beValue p : Int)
  | _ => none

/-- Integer value in the extended generic data model: major types 0 and 1
(§3.1) and bignums (§3.4.3). -/
def intValue? : Item → Option Int
  | .uint n => some n
  | .nint n => some (-1 - n)
  | x => x.bignumValue?

end Item

/-- Preferred serialization of an integer in the extended generic data model
(§3.4.3, §4.2.2): major type 0 for `0 ≤ z < 2^64`, major type 1 for
`-2^64 ≤ z < 0`, otherwise tag 2 / tag 3 around the minimal big-endian bytes
of `m`. -/
def encodeInt (z : Int) : Item :=
  if 0 ≤ z then
    if z < 2 ^ 64 then .uint z.toNat else .tag 2 (.bytes (minimalBE z.toNat))
  else
    if -2 ^ 64 ≤ z then .nint (-1 - z).toNat else .tag 3 (.bytes (minimalBE (-1 - z).toNat))

/-! ## Minimal big-endian bytes -/

theorem byteLenAux_spec : ∀ (k n : Nat), n ≤ k →
    n < 256 ^ byteLenAux k n ∧ (n ≠ 0 → 256 ^ (byteLenAux k n - 1) ≤ n)
  | 0, n, h => by simp [byteLenAux]; omega
  | k + 1, n, h => by
    simp only [byteLenAux]
    split
    · simp [*]
    · rename_i hn
      have ih := byteLenAux_spec k (n / 256) (by omega)
      refine ⟨?_, fun _ => ?_⟩
      · rw [Nat.pow_succ]; omega
      · simp only [Nat.add_sub_cancel]
        by_cases h0 : n / 256 = 0
        · have : byteLenAux k (n / 256) = 0 := by
            cases k <;> simp [byteLenAux, h0]
          rw [this]; simp; omega
        · have := ih.2 h0
          have h1 : 1 ≤ byteLenAux k (n / 256) := by
            rcases Nat.eq_zero_or_pos (byteLenAux k (n / 256)) with h2 | h2
            · rw [h2] at ih; simp at ih; omega
            · exact h2
          calc 256 ^ byteLenAux k (n / 256)
              = 256 ^ (byteLenAux k (n / 256) - 1) * 256 := by
                rw [← Nat.pow_succ]; congr 1; omega
            _ ≤ n / 256 * 256 := Nat.mul_le_mul_right _ this
            _ ≤ n := Nat.div_mul_le_self n 256

theorem lt_byteLen (n : Nat) : n < 256 ^ byteLen n := (byteLenAux_spec n n (Nat.le_refl _)).1

theorem byteLen_ge {n : Nat} (hn : n ≠ 0) : 256 ^ (byteLen n - 1) ≤ n :=
  (byteLenAux_spec n n (Nat.le_refl _)).2 hn

theorem byteLen_pos {n : Nat} (hn : n ≠ 0) : 0 < byteLen n := by
  rcases Nat.eq_zero_or_pos (byteLen n) with h | h
  · have := lt_byteLen n; rw [h] at this; simp at this; omega
  · exact h

theorem beValue_minimalBE (n : Nat) : beValue (minimalBE n) = n :=
  beValue_beBytes_of_lt (lt_byteLen n)

theorem minimalBE_length (n : Nat) : (minimalBE n).length = byteLen n := beBytes_length _ _

/-- The first byte of `beBytes (k+1) n`. -/
theorem beBytes_succ_head (k n : Nat) :
    (beBytes (k + 1) n).head? = some (UInt8.ofNat (n / 256 ^ k % 256)) := rfl

/-- Minimal bytes never start with `0x00`. -/
theorem minimalBE_head_ne_zero (n : Nat) : (minimalBE n).head? ≠ some 0 := by
  unfold minimalBE
  by_cases hn : n = 0
  · subst hn; simp [byteLen, byteLenAux, beBytes]
  · have hpos := byteLen_pos hn
    obtain ⟨k, hk⟩ : ∃ k, byteLen n = k + 1 := ⟨byteLen n - 1, by omega⟩
    rw [hk, beBytes_succ_head]
    have hlo := byteLen_ge hn
    have hhi := lt_byteLen n
    rw [hk] at hlo hhi
    simp only [Nat.add_sub_cancel] at hlo
    have hpk : 0 < 256 ^ k := Nat.pow_pos (by decide)
    have hq : n / 256 ^ k < 256 := by
      rw [Nat.pow_succ] at hhi
      exact Nat.div_lt_of_lt_mul hhi
    have hq1 : 1 ≤ n / 256 ^ k := (Nat.le_div_iff_mul_le hpk).2 (by omega)
    intro h
    simp only [Option.some.injEq] at h
    have h2 := congrArg UInt8.toNat h
    rw [toNat_ofNat_byte, Nat.mod_eq_of_lt hq] at h2
    simp at h2
    omega

/-- Bytes without a leading zero are the minimal representation of their
value. -/
theorem minimalBE_beValue {p : List UInt8} (hp : p.head? ≠ some 0) :
    minimalBE (beValue p) = p := by
  have hlen : byteLen (beValue p) = p.length := by
    match p, hp with
    | [], _ => simp [beValue, byteLen, byteLenAux]
    | b :: bs, hb =>
      have hb0 : b.toNat ≠ 0 := by
        intro h0; apply hb; simp only [List.head?_cons, Option.some.injEq]
        exact UInt8.toNat_inj.mp (by simp [h0])
      have hv := beValue_lt bs
      have hb256 : b.toNat < 256 := b.toNat_lt
      have hval : beValue (b :: bs) = b.toNat * 256 ^ bs.length + beValue bs := rfl
      have hne : beValue (b :: bs) ≠ 0 := by
        rw [hval]; have : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
        have : 0 < b.toNat * 256 ^ bs.length := Nat.mul_pos (by omega) this
        omega
      have h1 := lt_byteLen (beValue (b :: bs))
      have h2 := byteLen_ge hne
      -- 256^len ≤ value < 256^(len+1) pins byteLen
      have hup : beValue (b :: bs) < 256 ^ (bs.length + 1) := by
        have := beValue_lt (b :: bs); simpa using this
      have hlo : 256 ^ bs.length ≤ beValue (b :: bs) := by
        rw [hval]
        have : 256 ^ bs.length ≤ b.toNat * 256 ^ bs.length :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      simp only [List.length_cons]
      apply Nat.le_antisymm
      · rcases Nat.lt_or_ge (bs.length + 1) (byteLen (beValue (b :: bs))) with hlt | hge
        · exfalso
          have : 256 ^ (bs.length + 1) ≤ 256 ^ (byteLen (beValue (b :: bs)) - 1) :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        · exact hge
      · rcases Nat.lt_or_ge (byteLen (beValue (b :: bs))) (bs.length + 1) with hlt | hge
        · exfalso
          have : 256 ^ byteLen (beValue (b :: bs)) ≤ 256 ^ bs.length :=
            Nat.pow_le_pow_right (by decide) (by omega)
          omega
        · exact hge
  unfold minimalBE
  rw [hlen, beBytes_beValue]

/-- `m ≥ 2^64` needs at least 9 minimal bytes. -/
theorem nine_le_minimalBE_length {m : Nat} (hm : 2 ^ 64 ≤ m) : 9 ≤ (minimalBE m).length := by
  rw [minimalBE_length]
  rcases Nat.lt_or_ge (byteLen m) 9 with h | h
  · exfalso
    have h1 := lt_byteLen m
    have : 256 ^ byteLen m ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  · exact h

/-! ## Exact integer semantics -/

theorem intValue?_uint (n : Nat) : (Item.uint n).intValue? = some n := rfl
theorem intValue?_nint (n : Nat) : (Item.nint n).intValue? = some (-1 - (n : Int)) := rfl
theorem bignumValue?_tag2 (p : List UInt8) :
    (Item.tag 2 (.bytes p)).bignumValue? = some (beValue p : Int) := rfl
theorem bignumValue?_tag3 (p : List UInt8) :
    (Item.tag 3 (.bytes p)).bignumValue? = some (-1 - (beValue p : Int)) := rfl
theorem bignumValue?_tag2_indef (cs : List (List UInt8)) :
    (Item.tag 2 (.bytesIndef cs)).bignumValue? = some (beValue cs.flatten : Int) := rfl

/-- Leading zero bytes do not change a big-endian value. -/
theorem beValue_zeros_append (k : Nat) (p : List UInt8) :
    beValue (List.replicate k 0 ++ p) = beValue p := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, beValue, ih]

/-- Leading-zero tolerance (§3.4.3): leading zero bytes do not change a
tag-2 bignum's value. -/
theorem bignumValue?_tag2_leading_zeros (k : Nat) (p : List UInt8) :
    (Item.tag 2 (.bytes (List.replicate k 0 ++ p))).bignumValue? =
      (Item.tag 2 (.bytes p)).bignumValue? := by
  simp [Item.bignumValue?, Item.byteContent?, beValue_zeros_append]

/-- Leading-zero tolerance (§3.4.3) for tag 3. -/
theorem bignumValue?_tag3_leading_zeros (k : Nat) (p : List UInt8) :
    (Item.tag 3 (.bytes (List.replicate k 0 ++ p))).bignumValue? =
      (Item.tag 3 (.bytes p)).bignumValue? := by
  simp [Item.bignumValue?, Item.byteContent?, beValue_zeros_append]

/-- Exact semantics of the preferred integer serialization. -/
theorem intValue?_encodeInt (z : Int) : (encodeInt z).intValue? = some z := by
  unfold encodeInt
  split
  · split
    · simp only [Item.intValue?, Option.some.injEq]; omega
    · simp only [Item.intValue?, Item.bignumValue?, Item.byteContent?, Option.map_some,
        beValue_minimalBE, Option.some.injEq]
      omega
  · split
    · simp only [Item.intValue?, Option.some.injEq]; omega
    · simp only [Item.intValue?, Item.bignumValue?, Item.byteContent?, Option.map_some,
        beValue_minimalBE, Option.some.injEq]
      omega

/-! ## The canonical minimal boundary (ticket #34, amendment I3) -/

theorem encodeInt_uint_iff (z : Int) :
    (∃ n, encodeInt z = .uint n) ↔ 0 ≤ z ∧ z < 2 ^ 64 := by
  unfold encodeInt
  constructor
  · rintro ⟨n, hn⟩
    split at hn
    · split at hn
      · omega
      · simp at hn
    · split at hn <;> simp at hn
  · rintro ⟨h0, h1⟩
    exact ⟨z.toNat, by rw [ite_eq_left h0, ite_eq_left h1]⟩

theorem encodeInt_nint_iff (z : Int) :
    (∃ n, encodeInt z = .nint n) ↔ -2 ^ 64 ≤ z ∧ z < 0 := by
  unfold encodeInt
  constructor
  · rintro ⟨n, hn⟩
    split at hn
    · split at hn <;> simp at hn
    · split at hn
      · omega
      · simp at hn
  · rintro ⟨h0, h1⟩
    exact ⟨(-1 - z).toNat, by rw [ite_eq_right (show ¬ 0 ≤ z by omega), ite_eq_left h0]⟩

/-- I3: the preferred serialization uses tag 2 exactly when `z ≥ 2^64`. -/
theorem encodeInt_tag2_iff (z : Int) :
    (∃ p, encodeInt z = .tag 2 (.bytes p)) ↔ 2 ^ 64 ≤ z := by
  unfold encodeInt
  constructor
  · rintro ⟨p, hp⟩
    split at hp
    · split at hp
      · simp at hp
      · omega
    · split at hp <;> simp at hp
  · intro h
    exact ⟨minimalBE z.toNat, by rw [ite_eq_left (show 0 ≤ z by omega), ite_eq_right (show ¬ z < 2 ^ 64 by omega)]⟩

/-- I3: the preferred serialization uses tag 3 exactly when `z < -2^64`. -/
theorem encodeInt_tag3_iff (z : Int) :
    (∃ p, encodeInt z = .tag 3 (.bytes p)) ↔ z < -2 ^ 64 := by
  unfold encodeInt
  constructor
  · rintro ⟨p, hp⟩
    split at hp
    · split at hp <;> simp at hp
    · split at hp
      · simp at hp
      · omega
  · intro h
    exact ⟨minimalBE (-1 - z).toNat,
      by rw [ite_eq_right (show ¬ 0 ≤ z by omega), ite_eq_right (show ¬ -2 ^ 64 ≤ z by omega)]⟩

/-- I3: a tag-2 serialization carries `m = z.toNat ≥ 2^64` as minimal
big-endian bytes, with no leading `0x00` and at least 9 bytes. -/
theorem encodeInt_tag2_content {z : Int} {p : List UInt8} (h : encodeInt z = .tag 2 (.bytes p)) :
    2 ^ 64 ≤ z.toNat ∧ p = minimalBE z.toNat ∧ beValue p = z.toNat ∧
      p.head? ≠ some 0 ∧ 9 ≤ p.length := by
  have hz := (encodeInt_tag2_iff z).1 ⟨p, h⟩
  have hp : p = minimalBE z.toNat := by
    rw [encodeInt, ite_eq_left (show 0 ≤ z by omega), ite_eq_right (show ¬ z < 2 ^ 64 by omega)] at h
    simp only [Item.tag.injEq, Item.bytes.injEq, true_and] at h
    exact h.symm
  have hm : 2 ^ 64 ≤ z.toNat := by omega
  subst hp
  exact ⟨hm, rfl, beValue_minimalBE _, minimalBE_head_ne_zero _, nine_le_minimalBE_length hm⟩

/-- I3: a tag-3 serialization carries `m = (-1 - z).toNat ≥ 2^64` as minimal
big-endian bytes, with no leading `0x00` and at least 9 bytes. -/
theorem encodeInt_tag3_content {z : Int} {p : List UInt8} (h : encodeInt z = .tag 3 (.bytes p)) :
    2 ^ 64 ≤ (-1 - z).toNat ∧ p = minimalBE (-1 - z).toNat ∧ beValue p = (-1 - z).toNat ∧
      p.head? ≠ some 0 ∧ 9 ≤ p.length := by
  have hz := (encodeInt_tag3_iff z).1 ⟨p, h⟩
  have hp : p = minimalBE (-1 - z).toNat := by
    rw [encodeInt, ite_eq_right (show ¬ 0 ≤ z by omega), ite_eq_right (show ¬ -2 ^ 64 ≤ z by omega)] at h
    simp only [Item.tag.injEq, Item.bytes.injEq, true_and] at h
    exact h.symm
  have hm : 2 ^ 64 ≤ (-1 - z).toNat := by omega
  subst hp
  exact ⟨hm, rfl, beValue_minimalBE _, minimalBE_head_ne_zero _, nine_le_minimalBE_length hm⟩

/-- RFC 8949 Appendix A row 13: `-2^64` is major type 1 (`0x3bffffffffffffffff`). -/
theorem encodeInt_neg_two_pow_64 : encodeInt (-2 ^ 64) = .nint (2 ^ 64 - 1) := by
  decide

/-- The withdrawn dossier form ("bignum iff `|z| ≥ 2^64`") is wrong at
`z = -2^64`: the magnitude condition holds, yet the preferred serialization is
major type 1, not a bignum. -/
theorem dossier_form_misclassifies_row13 :
    2 ^ 64 ≤ (-2 ^ 64 : Int).natAbs ∧ ¬ ∃ p, encodeInt (-2 ^ 64) = .tag 3 (.bytes p) := by
  refine ⟨by decide, ?_⟩
  rw [encodeInt_tag3_iff]
  decide

/-! ## Uniqueness of the preferred integer serialization -/

/-- An integer item in preferred serialization: major type 0/1 within range,
or a bignum whose definite byte string has no leading zero and whose
magnitude needs a bignum (`≥ 2^64`). -/
def Item.isPreferredInt : Item → Bool
  | .uint n => n < 2 ^ 64
  | .nint n => n < 2 ^ 64
  | .tag 2 (.bytes p) => p.head? != some 0 && 2 ^ 64 ≤ beValue p
  | .tag 3 (.bytes p) => p.head? != some 0 && 2 ^ 64 ≤ beValue p
  | _ => false

theorem isPreferredInt_encodeInt (z : Int) : (encodeInt z).isPreferredInt = true := by
  unfold encodeInt
  split
  · split
    · simp only [Item.isPreferredInt, decide_eq_true_eq]; omega
    · simp only [Item.isPreferredInt, beValue_minimalBE, Bool.and_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq]
      exact ⟨minimalBE_head_ne_zero _, by omega⟩
  · split
    · simp only [Item.isPreferredInt, decide_eq_true_eq]; omega
    · simp only [Item.isPreferredInt, beValue_minimalBE, Bool.and_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq]
      exact ⟨minimalBE_head_ne_zero _, by omega⟩

/-- Every integer has exactly one preferred serialization: any preferred
integer item denoting `z` is `encodeInt z`. -/
theorem eq_encodeInt_of_isPreferredInt {x : Item} {z : Int} (hv : x.intValue? = some z)
    (hp : x.isPreferredInt = true) : x = encodeInt z := by
  match x, hv, hp with
  | .uint n, hv, hp =>
    simp only [Item.intValue?, Option.some.injEq] at hv
    simp only [Item.isPreferredInt, decide_eq_true_eq] at hp
    subst hv
    rw [encodeInt, ite_eq_left (by omega), ite_eq_left (by omega)]
    simp
  | .nint n, hv, hp =>
    simp only [Item.intValue?, Option.some.injEq] at hv
    simp only [Item.isPreferredInt, decide_eq_true_eq] at hp
    subst hv
    have h1 : ¬ (0 : Int) ≤ -1 - (n : Int) := by omega
    have h2 : -2 ^ 64 ≤ -1 - (n : Int) := by omega
    rw [encodeInt, ite_eq_right h1, ite_eq_left h2, Item.nint.injEq]
    omega
  | .tag 2 (.bytes p), hv, hp =>
    simp only [Item.intValue?, Item.bignumValue?, Item.byteContent?, Option.map_some,
      Option.some.injEq] at hv
    simp only [Item.isPreferredInt, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hp
    subst hv
    have h1 : (0 : Int) ≤ (beValue p : Int) := by omega
    have h2 : ¬ (beValue p : Int) < 2 ^ 64 := by omega
    rw [encodeInt, ite_eq_left h1, ite_eq_right h2, Int.toNat_natCast, minimalBE_beValue hp.1]
  | .tag 3 (.bytes p), hv, hp =>
    simp only [Item.intValue?, Item.bignumValue?, Item.byteContent?, Option.map_some,
      Option.some.injEq] at hv
    simp only [Item.isPreferredInt, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hp
    subst hv
    have h1 : ¬ (0 : Int) ≤ -1 - (beValue p : Int) := by omega
    have h2 : ¬ -2 ^ 64 ≤ -1 - (beValue p : Int) := by omega
    have h3 : (-1 - (-1 - (beValue p : Int))).toNat = beValue p := by omega
    rw [encodeInt, ite_eq_right h1, ite_eq_right h2, h3, minimalBE_beValue hp.1]

end Cbor.Rfc8949
