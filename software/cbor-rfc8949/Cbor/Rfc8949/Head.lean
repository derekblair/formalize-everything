/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# RFC 8949 §3: heads and arguments

The initial byte of every encoded data item carries a 3-bit major type and
5 bits of additional information (§3). Additional information below 24 is
the argument itself; 24, 25, 26 and 27 announce a 1-, 2-, 4- or 8-byte
big-endian ("network byte order") argument; 28–30 are reserved (not
well-formed); 31 marks an indefinite length (major types 2–5), the "break"
stop code (major type 7), or is not well-formed (major types 0, 1, 6).

This file fixes the byte-level vocabulary: big-endian values, argument
`Width`s (which record *how* an argument was serialized, so that
non-preferred heads stay visible on the wire), head encoding, and the head
decoder used by the step-fueled parser.
-/

namespace Cbor.Rfc8949

/-- Value of a byte string read in network byte order (RFC 8949 §3). -/
def beValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + beValue bs

/-- The `k` low-order bytes of `n`, most significant first (§3: network byte order). -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n / 256 ^ k % 256) :: beBytes k n

/-- How a definite argument is serialized (§3): in the initial byte (`inline`,
argument < 24) or in 1, 2, 4 or 8 following bytes (additional information
24, 25, 26, 27). Recording the width keeps non-preferred heads visible. -/
inductive Width where
  | inline
  | w1
  | w2
  | w4
  | w8
  deriving DecidableEq, Repr

namespace Width

/-- Number of argument bytes following the initial byte. -/
def extra : Width → Nat
  | inline => 0
  | w1 => 1
  | w2 => 2
  | w4 => 4
  | w8 => 8

/-- Additional-information value announcing this width for argument `n`. -/
def ai (w : Width) (n : Nat) : Nat :=
  match w with
  | inline => n
  | w1 => 24
  | w2 => 25
  | w4 => 26
  | w8 => 27

/-- Whether width `w` can carry argument `n`. -/
def fits : Width → Nat → Bool
  | inline, n => n < 24
  | w1, n => n < 2 ^ 8
  | w2, n => n < 2 ^ 16
  | w4, n => n < 2 ^ 32
  | w8, n => n < 2 ^ 64

/-- The preferred serialization of an argument: the shortest width that
carries it (§4.1; §4.2.1 lists the exact ranges). -/
def preferred (n : Nat) : Width :=
  if n < 24 then inline
  else if n < 2 ^ 8 then w1
  else if n < 2 ^ 16 then w2
  else if n < 2 ^ 32 then w4
  else w8

end Width

/-- The head of a data item with major type `m` and a definite argument `n`
serialized in width `w`. -/
def encodeHead (m : Nat) (w : Width) (n : Nat) : List UInt8 :=
  UInt8.ofNat (m * 32 + w.ai n) :: beBytes w.extra n

/-- The width used for simple value `v`: in the initial byte for 0..23, in
one following byte for 32..255 (§3.3, Table 3). -/
def simpleWidth (v : Nat) : Width :=
  if v < 24 then .inline else .w1

/-- A decoded head (§3, Appendix B). `arg m w n` is a definite argument for
major types 0–6; `indef m` is additional information 31 on major types 2–5;
`brk` is the "break" stop code 0xff (§3.2.1); `simple v` is a major-type-7
simple value. Floating-point heads (0xf9, 0xfa, 0xfb) are outside the
float-free milestone-1 fragment and are not decoded. -/
inductive Head where
  | arg (m : Nat) (w : Width) (n : Nat)
  | indef (m : Nat)
  | brk
  | simple (v : Nat)
  deriving DecidableEq, Repr

/-- Read a `k`-byte big-endian argument. -/
def readArg (k : Nat) (bs : List UInt8) : Option (Nat × List UInt8) :=
  if k ≤ bs.length then some (beValue (bs.take k), bs.drop k) else none

/-- Width selected by additional information 24..27. -/
def widthOfAi (ai : Nat) : Width :=
  if ai = 24 then .w1 else if ai = 25 then .w2 else if ai = 26 then .w4 else .w8

/-- The head decoder after the initial byte has been split into its major
type `m` and additional information `ai`. -/
def decodeHeadAux (m ai : Nat) (rest : List UInt8) : Option (Head × List UInt8) :=
  if ai < 24 then
    if m = 7 then some (.simple ai, rest) else some (.arg m .inline ai, rest)
  else if ai < 28 then
    if m = 7 then
      if ai = 24 then
        match rest with
        | [] => none
        | c :: rest' => if c.toNat < 32 then none else some (.simple c.toNat, rest')
      else none
    else
      match readArg (widthOfAi ai).extra rest with
      | none => none
      | some (n, rest') => some (.arg m (widthOfAi ai) n, rest')
  else if ai = 31 then
    if m = 7 then some (.brk, rest)
    else if 2 ≤ m ∧ m ≤ 5 then some (.indef m, rest)
    else none
  else none

/-- Decode one head (§3). Returns `none` for an empty input, a truncated
argument, reserved additional information 28–30, additional information 31
on major types 0, 1, 6, a two-byte simple value below 32 (§3.3), and the
float heads 0xf9/0xfa/0xfb (outside milestone 1). -/
def decodeHead : List UInt8 → Option (Head × List UInt8)
  | [] => none
  | b :: rest => decodeHeadAux (b.toNat / 32) (b.toNat % 32) rest

/-! ## Byte-level lemmas -/

theorem beValue_lt (bs : List UInt8) : beValue bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [beValue]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have hmul := Nat.mul_le_mul_right (256 ^ bs.length) (show b.toNat ≤ 255 by omega)
    simp only [beValue, List.length_cons, Nat.pow_succ]
    omega

theorem beBytes_length (k n : Nat) : (beBytes k n).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [beBytes, ih]

theorem toNat_ofNat_byte (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp only [UInt8.toNat_ofNat', Nat.reducePow]

theorem beValue_beBytes (k n : Nat) : beValue (beBytes k n) = n % 256 ^ k := by
  induction k with
  | zero => simp [beBytes, beValue, Nat.mod_one]
  | succ k ih =>
    simp only [beBytes, beValue, beBytes_length, ih, toNat_ofNat_byte, Nat.mod_mod]
    rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (n / 256 ^ k % 256), Nat.add_comm]

theorem beValue_beBytes_of_lt {k n : Nat} (h : n < 256 ^ k) : beValue (beBytes k n) = n := by
  rw [beValue_beBytes, Nat.mod_eq_of_lt h]

/-- Big-endian values are injective on byte strings of one length. -/
theorem beValue_inj : ∀ {as bs : List UInt8}, as.length = bs.length →
    beValue as = beValue bs → as = bs
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [beValue] at hv
    have ha := beValue_lt as
    have hb := beValue_lt bs
    rw [hl] at ha hv
    have hpos : 0 < 256 ^ bs.length := Nat.pow_pos (by decide)
    have hdiv : (a.toNat * 256 ^ bs.length + beValue as) / 256 ^ bs.length =
        (b.toNat * 256 ^ bs.length + beValue bs) / 256 ^ bs.length := by rw [hv]
    have hmod : (a.toNat * 256 ^ bs.length + beValue as) % 256 ^ bs.length =
        (b.toNat * 256 ^ bs.length + beValue bs) % 256 ^ bs.length := by rw [hv]
    rw [Nat.add_comm (a.toNat * _), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt ha,
      Nat.add_comm (b.toNat * _), Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb] at hdiv
    rw [Nat.add_comm (a.toNat * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha,
      Nat.add_comm (b.toNat * _), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb] at hmod
    have hab : a = b := UInt8.toNat_inj.mp (by omega)
    rw [hab, beValue_inj hl hmod]

theorem beBytes_beValue (bs : List UInt8) : beBytes bs.length (beValue bs) = bs :=
  beValue_inj (by simp [beBytes_length]) (beValue_beBytes_of_lt (beValue_lt bs))

/-! ## Heads as bytes, and the head decoder's exact characterization -/

/-- The bytes of a head. -/
def Head.bytes : Head → List UInt8
  | .arg m w n => encodeHead m w n
  | .indef m => [UInt8.ofNat (m * 32 + 31)]
  | .brk => [0xff]
  | .simple v => encodeHead 7 (simpleWidth v) v

/-- Heads that §3 allows in the float-free fragment: definite arguments on
major types 0–6 in a width that carries them; indefinite markers on major
types 2–5; break; simple values 0..23 and 32..255 (§3.3). -/
def Head.Valid : Head → Prop
  | .arg m w n => m ≤ 6 ∧ w.fits n = true
  | .indef m => 2 ≤ m ∧ m ≤ 5
  | .brk => True
  | .simple v => v < 24 ∨ (32 ≤ v ∧ v < 256)

theorem readArg_beBytes {k n : Nat} (h : n < 256 ^ k) (rest : List UInt8) :
    readArg k (beBytes k n ++ rest) = some (n, rest) := by
  have hl := beBytes_length k n
  simp [readArg, hl, List.take_left' hl, List.drop_left' hl, beValue_beBytes_of_lt h]

theorem readArg_sound {k n : Nat} {bs rest : List UInt8}
    (h : readArg k bs = some (n, rest)) : n < 256 ^ k ∧ bs = beBytes k n ++ rest := by
  unfold readArg at h
  split at h
  · rename_i hk
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hlen : (bs.take k).length = k := by simp; omega
    have hv := beValue_lt (bs.take k)
    rw [hlen] at hv
    refine ⟨hv, ?_⟩
    have hbb := beBytes_beValue (bs.take k)
    rw [hlen] at hbb
    rw [hbb, List.take_append_drop]
  · simp at h

theorem Width.fits_lt {w : Width} {n : Nat} (h : w.fits n = true) (hw : w ≠ .inline) :
    n < 256 ^ w.extra := by
  cases w <;> simp only [Width.fits, Width.extra, decide_eq_true_eq, ne_eq,
    not_true_eq_false] at h hw ⊢ <;> omega

theorem Width.ai_lt {w : Width} {n : Nat} (h : w.fits n = true) : w.ai n < 28 := by
  cases w <;> simp only [Width.fits, Width.ai, decide_eq_true_eq] at h ⊢ <;> omega

theorem decodeHead_cons (b : UInt8) (rest : List UInt8) :
    decodeHead (b :: rest) = decodeHeadAux (b.toNat / 32) (b.toNat % 32) rest := rfl

theorem decodeHead_ofNat {m ai : Nat} (hai : ai < 32) (hm : m < 8) (rest : List UInt8) :
    decodeHead (UInt8.ofNat (m * 32 + ai) :: rest) = decodeHeadAux m ai rest := by
  have hb : (UInt8.ofNat (m * 32 + ai)).toNat = m * 32 + ai := by
    rw [toNat_ofNat_byte]; omega
  rw [decodeHead_cons, hb]
  congr 1 <;> omega

/-- Completeness of the head decoder: every valid head decodes to itself. -/
theorem decodeHead_bytes {h : Head} (hv : h.Valid) (rest : List UInt8) :
    decodeHead (h.bytes ++ rest) = some (h, rest) := by
  cases h with
  | arg m w n =>
    obtain ⟨hm, hf⟩ := hv
    have hm7 : m ≠ 7 := by omega
    simp only [Head.bytes, encodeHead, List.cons_append]
    rw [decodeHead_ofNat (by have := Width.ai_lt hf; omega) (by omega)]
    cases w with
    | inline =>
      simp only [Width.fits, decide_eq_true_eq] at hf
      simp [decodeHeadAux, Width.ai, Width.extra, beBytes, hf, hm7]
    | w1 => simp [decodeHeadAux, Width.ai, hm7, widthOfAi,
        readArg_beBytes (Width.fits_lt hf (by decide))]
    | w2 => simp [decodeHeadAux, Width.ai, hm7, widthOfAi,
        readArg_beBytes (Width.fits_lt hf (by decide))]
    | w4 => simp [decodeHeadAux, Width.ai, hm7, widthOfAi,
        readArg_beBytes (Width.fits_lt hf (by decide))]
    | w8 => simp [decodeHeadAux, Width.ai, hm7, widthOfAi,
        readArg_beBytes (Width.fits_lt hf (by decide))]
  | indef m =>
    obtain ⟨h2, h5⟩ := hv
    simp only [Head.bytes, List.cons_append, List.nil_append]
    rw [decodeHead_ofNat (by omega) (by omega)]
    have hm7 : m ≠ 7 := by omega
    simp [decodeHeadAux, hm7, h2, h5]
  | brk => rfl
  | simple v =>
    rcases hv with hv | ⟨hv1, hv2⟩
    · have hw : simpleWidth v = .inline := by simp [simpleWidth, hv]
      simp only [Head.bytes, hw, encodeHead, Width.ai, Width.extra, beBytes, List.cons_append,
        List.nil_append]
      rw [decodeHead_ofNat (m := 7) (ai := v) (by omega) (by decide)]
      simp [decodeHeadAux, hv]
    · have hw : simpleWidth v = .w1 := by simp [simpleWidth]; omega
      have hc : (UInt8.ofNat (v / 256 ^ 0 % 256)).toNat = v := by
        rw [toNat_ofNat_byte]; simp; omega
      simp only [Head.bytes, hw, encodeHead, Width.ai, Width.extra, beBytes, List.cons_append,
        List.nil_append]
      rw [decodeHead_ofNat (by decide) (by decide)]
      simp only [decodeHeadAux, hc]
      simp; omega

theorem ofNat_split (b : UInt8) : UInt8.ofNat (b.toNat / 32 * 32 + b.toNat % 32) = b := by
  rw [show b.toNat / 32 * 32 + b.toNat % 32 = b.toNat by omega, UInt8.ofNat_toNat]

/-- Soundness of the head decoder: whatever it returns is a valid head whose
bytes are exactly the consumed prefix. -/
theorem decodeHead_sound {bs rest : List UInt8} {h : Head}
    (hd : decodeHead bs = some (h, rest)) : h.Valid ∧ bs = h.bytes ++ rest := by
  match bs with
  | [] => simp [decodeHead] at hd
  | b :: tl =>
    have hb : b.toNat < 256 := b.toNat_lt
    have hsplit := ofNat_split b
    rw [decodeHead_cons] at hd
    unfold decodeHeadAux at hd
    split at hd
    · rename_i hai
      split at hd
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        refine ⟨Or.inl hai, ?_⟩
        have hw : simpleWidth (b.toNat % 32) = .inline := by simp [simpleWidth, hai]
        simp only [Head.bytes, hw, encodeHead, Width.ai, Width.extra, beBytes, List.cons_append,
          List.nil_append, List.cons.injEq, and_true]
        rw [← hm]; exact hsplit.symm
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        refine ⟨⟨by omega, by simp [Width.fits, hai]⟩, ?_⟩
        simp only [Head.bytes, encodeHead, Width.ai, Width.extra, beBytes, List.cons_append,
          List.nil_append, List.cons.injEq, and_true]
        exact hsplit.symm
    · rename_i hai
      split at hd
      · rename_i hai2
        split at hd
        · rename_i hm
          split at hd
          · rename_i hai3
            split at hd
            · simp at hd
            · rename_i c rest' 
              split at hd
              · simp at hd
              · rename_i hc
                simp only [Option.some.injEq, Prod.mk.injEq] at hd
                obtain ⟨rfl, rfl⟩ := hd
                have hc2 : c.toNat < 256 := c.toNat_lt
                refine ⟨Or.inr ⟨by omega, hc2⟩, ?_⟩
                have hw : simpleWidth c.toNat = .w1 := by simp [simpleWidth]; omega
                simp only [Head.bytes, hw, encodeHead, Width.ai, Width.extra, beBytes,
                  List.cons_append, List.nil_append, List.cons.injEq]
                refine ⟨?_, ?_, trivial⟩
                · rw [← hm, ← hai3]; exact hsplit.symm
                · simp [Nat.mod_eq_of_lt hc2]
          · simp at hd
        · rename_i hm
          split at hd
          · simp at hd
          · rename_i n rest' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            obtain ⟨hn, htl⟩ := readArg_sound hr
            have hw : (widthOfAi (b.toNat % 32)).ai n = b.toNat % 32 := by
              simp only [widthOfAi]; split <;> (try split) <;> (try split) <;> simp [Width.ai] <;> omega
            have hfit : (widthOfAi (b.toNat % 32)).fits n = true := by
              revert hn; simp only [widthOfAi]; split <;> (try split) <;> (try split) <;>
                simp [Width.fits, Width.extra] <;> omega
            refine ⟨⟨by omega, hfit⟩, ?_⟩
            simp only [Head.bytes, encodeHead, hw, List.cons_append, List.cons.injEq]
            exact ⟨hsplit.symm, htl⟩
      · split at hd
        · rename_i hai31
          split at hd
          · rename_i hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl⟩ := hd
            refine ⟨trivial, ?_⟩
            simp only [Head.bytes, List.cons_append, List.nil_append, List.cons.injEq, and_true]
            apply UInt8.toNat_inj.mp; simp; omega
          · split at hd
            · rename_i hm7 hm
              simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl⟩ := hd
              refine ⟨hm, ?_⟩
              simp only [Head.bytes, List.cons_append, List.nil_append, List.cons.injEq, and_true]
              rw [← hai31]; exact hsplit.symm
            · simp at hd
        · simp at hd

end Cbor.Rfc8949
