import Utf8.Spec

/-!
# An executable decoder, and the characterization of `Valid`

`decodeSeq?` reads one sequence off the front of a byte list, checking
exactly the byte ranges of Table 3-7 (as transcribed in `Utf8.Seq`) and
extracting the code point from the payload bits. `decode` iterates it.

This file proves the one-step facts the rest of the development uses:
accepted payloads are valid scalar values (`payload*_isValidChar`),
they re-encode to the original bytes (`encode_payload*`), encodings
are well-formed (`seq_encodeCodepoint`, `valid_encodeAll`), and the
decoder accepts exactly the encodings and exactly the well-formed
sequences (`decodeSeq?_encodeCodepoint`, `decodeSeq?_of_seq`).

The characterization itself —

    `valid_iff_decode : Valid l ↔ ∃ cs, decode l = some cs ∧ encodeAll cs = l`

together with `decode_encodeAll : decode (encodeAll cs) = some cs` —
is in `Utf8/Char.lean`; the agreement with Lean core
(`Valid l ↔ ByteArray.IsValidUTF8 l.toByteArray`, hence with core's
own validator `ByteArray.validateUTF8`) is in `Utf8/Core.lean`; the
overlong/shortest-form exclusions as theorems about byte sequences
are in `Utf8/Examples.lean`.
-/

namespace Utf8

/-- Pack a natural number as a character when it is a valid Unicode
scalar value (`Nat.isValidChar`: below U+110000 and not a surrogate). -/
def natToChar? (n : Nat) : Option Char :=
  if h : n.isValidChar then some (Char.ofNatAux n h) else none

theorem natToChar?_val {n : Nat} {c : Char} (h : natToChar? n = some c) :
    c.val.toNat = n := by
  unfold natToChar? at h
  split at h
  · cases h
    simp [Char.ofNatAux]
  · cases h

theorem natToChar?_of_isValidChar {n : Nat} (hn : n.isValidChar) :
    ∃ c : Char, natToChar? n = some c ∧ c.val.toNat = n :=
  ⟨Char.ofNatAux n hn, by simp [natToChar?, hn], by simp [Char.ofNatAux]⟩

theorem natToChar?_char (c : Char) : natToChar? c.val.toNat = some c := by
  obtain ⟨c', hc', hval⟩ := natToChar?_of_isValidChar (n := c.val.toNat) c.valid
  have : c' = c := Char.ext (UInt32.toNat_inj.1 hval)
  rw [this] at hc'
  exact hc'

/-- The second-byte condition for three-byte sequences, one disjunct per
three-byte row of Table 3-7 (rows `E0`, `E1–EC`, `ED`, `EE–EF`). -/
def secondOk3 (b₀ b₁ : UInt8) : Prop :=
  (b₀.toNat = 0xE0 ∧ 0xA0 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) ∨
  (0xE1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEC ∧ IsCont b₁) ∨
  (b₀.toNat = 0xED ∧ 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x9F) ∨
  (0xEE ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF ∧ IsCont b₁)

instance (b₀ b₁ : UInt8) : Decidable (secondOk3 b₀ b₁) :=
  inferInstanceAs (Decidable
    ((b₀.toNat = 0xE0 ∧ 0xA0 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) ∨
    (0xE1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEC ∧ IsCont b₁) ∨
    (b₀.toNat = 0xED ∧ 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x9F) ∨
    (0xEE ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF ∧ IsCont b₁)))

/-- The second-byte condition for four-byte sequences, one disjunct per
four-byte row of Table 3-7 (rows `F0`, `F1–F3`, `F4`). -/
def secondOk4 (b₀ b₁ : UInt8) : Prop :=
  (b₀.toNat = 0xF0 ∧ 0x90 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) ∨
  (0xF1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF3 ∧ IsCont b₁) ∨
  (b₀.toNat = 0xF4 ∧ 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x8F)

instance (b₀ b₁ : UInt8) : Decidable (secondOk4 b₀ b₁) :=
  inferInstanceAs (Decidable
    ((b₀.toNat = 0xF0 ∧ 0x90 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) ∨
    (0xF1 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF3 ∧ IsCont b₁) ∨
    (b₀.toNat = 0xF4 ∧ 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0x8F)))

/-- The code point carried by a two-byte sequence: the five payload bits
of the lead byte and the six payload bits of the continuation byte. -/
def payload2 (b₀ b₁ : UInt8) : Nat := (b₀.toNat % 32) * 64 + b₁.toNat % 64

/-- The code point carried by a three-byte sequence. -/
def payload3 (b₀ b₁ b₂ : UInt8) : Nat :=
  (b₀.toNat % 16) * 4096 + (b₁.toNat % 64) * 64 + b₂.toNat % 64

/-- The code point carried by a four-byte sequence. -/
def payload4 (b₀ b₁ b₂ b₃ : UInt8) : Nat :=
  (b₀.toNat % 8) * 262144 + (b₁.toNat % 64) * 4096 +
    (b₂.toNat % 64) * 64 + b₃.toNat % 64

/-- Read one well-formed sequence off the front of a byte list, returning
the decoded character and the number of bytes consumed. The range checks
are exactly those of Table 3-7; lead bytes `80–C1` and `F5–FF` match no
branch and are rejected, as are truncated sequences. -/
def decodeSeq? : List UInt8 → Option (Char × Nat)
  | [] => none
  | b₀ :: rest =>
    if b₀.toNat ≤ 0x7F then (natToChar? b₀.toNat).map fun c => (c, 1)
    else if 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF then
      match rest with
      | b₁ :: _ =>
        if IsCont b₁ then (natToChar? (payload2 b₀ b₁)).map fun c => (c, 2)
        else none
      | [] => none
    else if 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF then
      match rest with
      | b₁ :: b₂ :: _ =>
        if secondOk3 b₀ b₁ ∧ IsCont b₂ then
          (natToChar? (payload3 b₀ b₁ b₂)).map fun c => (c, 3)
        else none
      | _ => none
    else if 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 then
      match rest with
      | b₁ :: b₂ :: b₃ :: _ =>
        if secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃ then
          (natToChar? (payload4 b₀ b₁ b₂ b₃)).map fun c => (c, 4)
        else none
      | _ => none
    else none

theorem decodeSeq?_nil : decodeSeq? [] = none := rfl

theorem decodeSeq?_cons (b₀ : UInt8) (rest : List UInt8) :
    decodeSeq? (b₀ :: rest) =
      if b₀.toNat ≤ 0x7F then (natToChar? b₀.toNat).map fun c => (c, 1)
      else if 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF then
        match rest with
        | b₁ :: _ =>
          if IsCont b₁ then (natToChar? (payload2 b₀ b₁)).map fun c => (c, 2)
          else none
        | [] => none
      else if 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF then
        match rest with
        | b₁ :: b₂ :: _ =>
          if secondOk3 b₀ b₁ ∧ IsCont b₂ then
            (natToChar? (payload3 b₀ b₁ b₂)).map fun c => (c, 3)
          else none
        | _ => none
      else if 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 then
        match rest with
        | b₁ :: b₂ :: b₃ :: _ =>
          if secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃ then
            (natToChar? (payload4 b₀ b₁ b₂ b₃)).map fun c => (c, 4)
          else none
        | _ => none
      else none := rfl

/-- Decode a whole byte list by iterating `decodeSeq?`. Fuel is the
length of the input; every successful step consumes at least one byte,
so `l.length` units of fuel always suffice (proved below as
`decodeFuel_irrel`). -/
def decodeFuel : Nat → List UInt8 → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b₀ :: rest =>
    match decodeSeq? (b₀ :: rest) with
    | none => none
    | some (c, k) => (decodeFuel fuel ((b₀ :: rest).drop k)).map (c :: ·)

theorem decodeFuel_nil (f : Nat) : decodeFuel f [] = some [] := by
  cases f <;> rfl

/-- Decode a byte list to the characters it encodes, or fail. -/
def decode (l : List UInt8) : Option (List Char) :=
  decodeFuel l.length l

/-! ## Range projections for the second-byte conditions -/

theorem secondOk3_lead {b₀ b₁ : UInt8} (h : secondOk3 b₀ b₁) :
    0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF := by
  rcases h with ⟨h, -, -⟩ | ⟨h, h', -⟩ | ⟨h, -, -⟩ | ⟨h, h', -⟩ <;> omega

theorem secondOk3_second {b₀ b₁ : UInt8} (h : secondOk3 b₀ b₁) :
    0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := by
  rcases h with ⟨-, h, h'⟩ | ⟨-, -, h⟩ | ⟨-, h, h'⟩ | ⟨-, -, h⟩
  · omega
  · have h1 := h.1; have h2 := h.2; omega
  · omega
  · have h1 := h.1; have h2 := h.2; omega

/-- The top twelve payload bits of a three-byte sequence reach at least
`0x800`: in the `E0` row the second byte contributes at least `0x20` in
its low six bits, and in every other row the lead byte contributes at
least one in its low four bits. This is the shortest-form bound. -/
theorem secondOk3_payload_ge {b₀ b₁ : UInt8} (h : secondOk3 b₀ b₁) :
    0x20 ≤ (b₀.toNat % 16) * 64 + (b₁.toNat % 64) := by
  rcases h with ⟨h0, h1, h1'⟩ | ⟨h0, h0', h1⟩ | ⟨h0, h1, h1'⟩ | ⟨h0, h0', h1⟩
  · omega
  · have h1a := h1.1; have h1b := h1.2; omega
  · omega
  · have h1a := h1.1; have h1b := h1.2; omega

theorem secondOk4_lead {b₀ b₁ : UInt8} (h : secondOk4 b₀ b₁) :
    0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 := by
  rcases h with ⟨h, -, -⟩ | ⟨h, h', -⟩ | ⟨h, -, -⟩ <;> omega

theorem secondOk4_second {b₀ b₁ : UInt8} (h : secondOk4 b₀ b₁) :
    0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := by
  rcases h with ⟨-, h, h'⟩ | ⟨-, -, h⟩ | ⟨-, h, h'⟩
  · omega
  · have h1 := h.1; have h2 := h.2; omega
  · omega

/-- The top eighteen payload bits of a four-byte sequence reach at least
`0x10000`: in the `F0` row the second byte contributes at least `0x10` in
its low six bits, and in every other row the lead byte contributes at
least one in its low three bits. This is the shortest-form bound. -/
theorem secondOk4_payload_ge {b₀ b₁ : UInt8} (h : secondOk4 b₀ b₁) :
    0x10 ≤ (b₀.toNat % 8) * 64 + (b₁.toNat % 64) := by
  rcases h with ⟨h0, h1, h1'⟩ | ⟨h0, h0', h1⟩ | ⟨h0, h1, h1'⟩
  · omega
  · have h1a := h1.1; have h1b := h1.2; omega
  · omega

/-! ## Payload arithmetic: encoding a payload returns the original bytes -/

theorem encode_payload2 {b₀ b₁ : UInt8}
    (h₀ : 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF) (h₁ : IsCont b₁) :
    encodeCodepoint (payload2 b₀ b₁) = [b₀, b₁] := by
  have h1a : 0x80 ≤ b₁.toNat := h₁.1
  have h1b : b₁.toNat ≤ 0xBF := h₁.2
  have hb1 : b₁.toNat < 256 := UInt8.toNat_lt b₁
  unfold encodeCodepoint payload2
  have hp1 : ¬ (b₀.toNat % 32 * 64 + b₁.toNat % 64) ≤ 0x7F := by omega
  have hp2 : (b₀.toNat % 32 * 64 + b₁.toNat % 64) ≤ 0x7FF := by omega
  rw [if_neg hp1, if_pos hp2]
  congr 1
  · apply UInt8.toNat_inj.1; simp; omega
  · congr 1
    apply UInt8.toNat_inj.1; simp; omega

theorem encode_payload3 {b₀ b₁ b₂ : UInt8}
    (h₀ : secondOk3 b₀ b₁) (h₂ : IsCont b₂) :
    encodeCodepoint (payload3 b₀ b₁ b₂) = [b₀, b₁, b₂] := by
  have hb0 : 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF := secondOk3_lead h₀
  have hb1 : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := secondOk3_second h₀
  have h2a : 0x80 ≤ b₂.toNat := h₂.1
  have h2b : b₂.toNat ≤ 0xBF := h₂.2
  have hb2 : b₂.toNat < 256 := UInt8.toNat_lt b₂
  have hb1' : b₁.toNat < 256 := UInt8.toNat_lt b₁
  have hge : 0x20 ≤ (b₀.toNat % 16) * 64 + (b₁.toNat % 64) :=
    secondOk3_payload_ge h₀
  unfold encodeCodepoint payload3
  have hp1 : ¬ (b₀.toNat % 16 * 4096 + (b₁.toNat % 64) * 64 + b₂.toNat % 64) ≤ 0x7F := by
    omega
  have hp2 : ¬ (b₀.toNat % 16 * 4096 + (b₁.toNat % 64) * 64 + b₂.toNat % 64) ≤ 0x7FF := by
    omega
  have hp3 : (b₀.toNat % 16 * 4096 + (b₁.toNat % 64) * 64 + b₂.toNat % 64) ≤ 0xFFFF := by
    omega
  rw [if_neg hp1, if_neg hp2, if_pos hp3]
  congr 1
  · apply UInt8.toNat_inj.1; simp; omega
  · congr 1
    · apply UInt8.toNat_inj.1; simp; omega
    · congr 1
      apply UInt8.toNat_inj.1; simp; omega

theorem encode_payload4 {b₀ b₁ b₂ b₃ : UInt8}
    (h₀ : secondOk4 b₀ b₁) (h₂ : IsCont b₂) (h₃ : IsCont b₃) :
    encodeCodepoint (payload4 b₀ b₁ b₂ b₃) = [b₀, b₁, b₂, b₃] := by
  have hb0 : 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 := secondOk4_lead h₀
  have hb1 : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := secondOk4_second h₀
  have h2a : 0x80 ≤ b₂.toNat := h₂.1
  have h2b : b₂.toNat ≤ 0xBF := h₂.2
  have h3a : 0x80 ≤ b₃.toNat := h₃.1
  have h3b : b₃.toNat ≤ 0xBF := h₃.2
  have hb2 : b₂.toNat < 256 := UInt8.toNat_lt b₂
  have hb3 : b₃.toNat < 256 := UInt8.toNat_lt b₃
  have hb1' : b₁.toNat < 256 := UInt8.toNat_lt b₁
  have hge : 0x10 ≤ (b₀.toNat % 8) * 64 + (b₁.toNat % 64) :=
    secondOk4_payload_ge h₀
  unfold encodeCodepoint payload4
  have hp1 :
      ¬ (b₀.toNat % 8 * 262144 + (b₁.toNat % 64) * 4096 +
          (b₂.toNat % 64) * 64 + b₃.toNat % 64) ≤ 0x7F := by omega
  have hp2 :
      ¬ (b₀.toNat % 8 * 262144 + (b₁.toNat % 64) * 4096 +
          (b₂.toNat % 64) * 64 + b₃.toNat % 64) ≤ 0x7FF := by omega
  have hp3 :
      ¬ (b₀.toNat % 8 * 262144 + (b₁.toNat % 64) * 4096 +
          (b₂.toNat % 64) * 64 + b₃.toNat % 64) ≤ 0xFFFF := by omega
  rw [if_neg hp1, if_neg hp2, if_neg hp3]
  congr 1
  · apply UInt8.toNat_inj.1; simp; omega
  · congr 1
    · apply UInt8.toNat_inj.1; simp; omega
    · congr 1
      · apply UInt8.toNat_inj.1; simp; omega
      · congr 1
        apply UInt8.toNat_inj.1; simp; omega

/-! ## Payloads of accepted sequences are valid scalar values -/

theorem payload2_isValidChar {b₀ b₁ : UInt8}
    (h₀ : 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF) (h₁ : IsCont b₁) :
    (payload2 b₀ b₁).isValidChar := by
  have h1a : 0x80 ≤ b₁.toNat := h₁.1
  have h1b : b₁.toNat ≤ 0xBF := h₁.2
  have hb1 : b₁.toNat < 256 := UInt8.toNat_lt b₁
  unfold payload2
  refine Or.inl ?_
  omega

theorem payload3_isValidChar {b₀ b₁ b₂ : UInt8}
    (h₀ : secondOk3 b₀ b₁) (h₂ : IsCont b₂) :
    (payload3 b₀ b₁ b₂).isValidChar := by
  have h2a : 0x80 ≤ b₂.toNat := h₂.1
  have h2b : b₂.toNat ≤ 0xBF := h₂.2
  have hb2 : b₂.toNat < 256 := UInt8.toNat_lt b₂
  have hb1 : b₁.toNat < 256 := UInt8.toNat_lt b₁
  have hb0 : 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF := secondOk3_lead h₀
  have hb1r : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := secondOk3_second h₀
  unfold payload3
  rcases h₀ with ⟨h0, -, -⟩ | ⟨h0, h0', -⟩ | ⟨h0, h1, h1'⟩ | ⟨h0, -, -⟩
  · refine Or.inl ?_; omega
  · refine Or.inl ?_; omega
  · refine Or.inl ?_; omega
  · refine Or.inr ⟨?_, ?_⟩ <;> omega

theorem payload4_isValidChar {b₀ b₁ b₂ b₃ : UInt8}
    (h₀ : secondOk4 b₀ b₁) (h₂ : IsCont b₂) (h₃ : IsCont b₃) :
    (payload4 b₀ b₁ b₂ b₃).isValidChar := by
  have h2a : 0x80 ≤ b₂.toNat := h₂.1
  have h2b : b₂.toNat ≤ 0xBF := h₂.2
  have h3a : 0x80 ≤ b₃.toNat := h₃.1
  have h3b : b₃.toNat ≤ 0xBF := h₃.2
  have hb2 : b₂.toNat < 256 := UInt8.toNat_lt b₂
  have hb3 : b₃.toNat < 256 := UInt8.toNat_lt b₃
  have hb1 : b₁.toNat < 256 := UInt8.toNat_lt b₁
  have hb0 : 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 := secondOk4_lead h₀
  have hb1r : 0x80 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF := secondOk4_second h₀
  have hge : 0x10 ≤ (b₀.toNat % 8) * 64 + (b₁.toNat % 64) :=
    secondOk4_payload_ge h₀
  unfold payload4
  rcases h₀ with ⟨h0, h1, h1'⟩ | ⟨h0, h0', h1⟩ | ⟨h0, h1, h1'⟩
  · refine Or.inr ⟨?_, ?_⟩ <;> omega
  · have h1a := h1.1; have h1b := h1.2
    refine Or.inr ⟨?_, ?_⟩ <;> omega
  · refine Or.inr ⟨?_, ?_⟩ <;> omega

/-! ## The encoding of a character is a well-formed sequence -/

theorem seq_encodeCodepoint (c : Char) : Seq (encodeCodepoint c.val.toNat) := by
  have hn : c.val.toNat.isValidChar := c.valid
  have hcv : c.toNat = c.val.toNat := rfl
  unfold encodeCodepoint
  by_cases h1 : c.val.toNat ≤ 0x7F
  · rw [if_pos h1]
    exact Seq.one (by simp; omega)
  · by_cases h2 : c.val.toNat ≤ 0x7FF
    · rw [if_neg h1, if_pos h2]
      exact Seq.two ⟨by simp; omega, by simp; omega⟩
        ⟨by simp; omega, by simp; omega⟩
    · by_cases h3 : c.val.toNat ≤ 0xFFFF
      · rw [if_neg h1, if_neg h2, if_pos h3]
        by_cases hE0 : c.val.toNat ≤ 0xFFF
        · exact Seq.threeE0 (by simp; omega)
            ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
        · by_cases hGen : c.val.toNat ≤ 0xCFFF
          · exact Seq.three ⟨by simp; omega, by simp; omega⟩
              ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
          · by_cases hED : c.val.toNat ≤ 0xD7FF
            · exact Seq.threeED (by simp; omega)
                ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
            · exact Seq.threeEF ⟨by simp; omega, by simp; omega⟩
                ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
      · rw [if_neg h1, if_neg h2, if_neg h3]
        by_cases hF0 : c.val.toNat ≤ 0x3FFFF
        · exact Seq.fourF0 (by simp; omega)
            ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
            ⟨by simp; omega, by simp; omega⟩
        · by_cases hGen : c.val.toNat ≤ 0xFFFFF
          · exact Seq.four ⟨by simp; omega, by simp; omega⟩
              ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
              ⟨by simp; omega, by simp; omega⟩
          · exact Seq.fourF4 (by simp; omega)
              ⟨by simp; omega, by simp; omega⟩ ⟨by simp; omega, by simp; omega⟩
              ⟨by simp; omega, by simp; omega⟩

/-- The encoding of any list of characters is well-formed. -/
theorem valid_encodeAll (cs : List Char) : Valid (encodeAll cs) := by
  induction cs with
  | nil => exact Valid.nil
  | cons c cs ih =>
      unfold encodeAll
      rw [List.flatMap_cons]
      exact Valid.append (Valid.ofSeq (seq_encodeCodepoint c)) ih

/-! ## The decoder accepts exactly the encodings -/

theorem decodeSeq?_encodeCodepoint (c : Char) (rest : List UInt8) :
    decodeSeq? (encodeCodepoint c.val.toNat ++ rest) =
      some (c, (encodeCodepoint c.val.toNat).length) := by
  have hn : c.val.toNat.isValidChar := c.valid
  have hcv : c.toNat = c.val.toNat := rfl
  by_cases h1 : c.val.toNat ≤ 0x7F
  · have e : encodeCodepoint c.val.toNat = [UInt8.ofNat c.val.toNat] := by
      unfold encodeCodepoint; rw [if_pos h1]
    rw [e]
    show decodeSeq? (UInt8.ofNat c.val.toNat :: rest) = some (c, 1)
    have ht : (UInt8.ofNat c.val.toNat).toNat = c.val.toNat := by simp; omega
    rw [decodeSeq?_cons, if_pos (by omega : (UInt8.ofNat c.val.toNat).toNat ≤ 0x7F)]
    rw [ht, natToChar?_char]
    rfl
  · by_cases h2 : c.val.toNat ≤ 0x7FF
    · have e : encodeCodepoint c.val.toNat =
          [UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0),
            UInt8.ofNat (c.val.toNat % 64 + 0x80)] := by
        unfold encodeCodepoint; rw [if_neg h1, if_pos h2]
      rw [e]
      show decodeSeq? (UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0) ::
        UInt8.ofNat (c.val.toNat % 64 + 0x80) :: rest) = some (c, 2)
      have ht0 : (UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0)).toNat =
          c.val.toNat / 64 % 32 + 0xC0 := by simp; omega
      have ht1 : (UInt8.ofNat (c.val.toNat % 64 + 0x80)).toNat =
          c.val.toNat % 64 + 0x80 := by simp; omega
      rw [decodeSeq?_cons, if_neg (by omega : ¬ (UInt8.ofNat
        (c.val.toNat / 64 % 32 + 0xC0)).toNat ≤ 0x7F),
        if_pos (show 0xC2 ≤ (UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0)).toNat ∧
          (UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0)).toNat ≤ 0xDF by omega)]
      simp only
      rw [if_pos (show IsCont (UInt8.ofNat (c.val.toNat % 64 + 0x80)) from
        ⟨by omega, by omega⟩)]
      have hpay : payload2 (UInt8.ofNat (c.val.toNat / 64 % 32 + 0xC0))
          (UInt8.ofNat (c.val.toNat % 64 + 0x80)) = c.val.toNat := by
        unfold payload2; omega
      rw [hpay, natToChar?_char]
      rfl
    · by_cases h3 : c.val.toNat ≤ 0xFFFF
      · have e : encodeCodepoint c.val.toNat =
            [UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0),
              UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80),
              UInt8.ofNat (c.val.toNat % 64 + 0x80)] := by
          unfold encodeCodepoint; rw [if_neg h1, if_neg h2, if_pos h3]
        rw [e]
        show decodeSeq? (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0) ::
          UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80) ::
          UInt8.ofNat (c.val.toNat % 64 + 0x80) :: rest) = some (c, 3)
        have ht0 : (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0)).toNat =
            c.val.toNat / 4096 % 16 + 0xE0 := by simp; omega
        have ht1 : (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80)).toNat =
            c.val.toNat / 64 % 64 + 0x80 := by simp; omega
        have ht2 : (UInt8.ofNat (c.val.toNat % 64 + 0x80)).toNat =
            c.val.toNat % 64 + 0x80 := by simp; omega
        have hok : secondOk3 (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0))
            (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80)) := by
          by_cases hE0 : c.val.toNat ≤ 0xFFF
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · by_cases hGen : c.val.toNat ≤ 0xCFFF
            · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
            · by_cases hED : c.val.toNat ≤ 0xD7FF
              · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega⟩))
              · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega,
                  by omega, by omega⟩))
        rw [decodeSeq?_cons,
          if_neg (by omega : ¬ (UInt8.ofNat
            (c.val.toNat / 4096 % 16 + 0xE0)).toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ (UInt8.ofNat
            (c.val.toNat / 4096 % 16 + 0xE0)).toNat ∧
            (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0)).toNat ≤ 0xDF)),
          if_pos (show 0xE0 ≤ (UInt8.ofNat
            (c.val.toNat / 4096 % 16 + 0xE0)).toNat ∧
            (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0)).toNat ≤ 0xEF by omega)]
        simp only
        rw [if_pos (show secondOk3 (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0))
            (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80)) ∧
            IsCont (UInt8.ofNat (c.val.toNat % 64 + 0x80)) from
          ⟨hok, by omega, by omega⟩)]
        have hpay : payload3 (UInt8.ofNat (c.val.toNat / 4096 % 16 + 0xE0))
            (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80))
            (UInt8.ofNat (c.val.toNat % 64 + 0x80)) = c.val.toNat := by
          unfold payload3; omega
        rw [hpay, natToChar?_char]
        rfl
      · have e : encodeCodepoint c.val.toNat =
            [UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0),
              UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80),
              UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80),
              UInt8.ofNat (c.val.toNat % 64 + 0x80)] := by
          unfold encodeCodepoint; rw [if_neg h1, if_neg h2, if_neg h3]
        rw [e]
        show decodeSeq? (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0) ::
          UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80) ::
          UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80) ::
          UInt8.ofNat (c.val.toNat % 64 + 0x80) :: rest) = some (c, 4)
        have ht0 : (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0)).toNat =
            c.val.toNat / 262144 % 8 + 0xF0 := by simp; omega
        have ht1 : (UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80)).toNat =
            c.val.toNat / 4096 % 64 + 0x80 := by simp; omega
        have ht2 : (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80)).toNat =
            c.val.toNat / 64 % 64 + 0x80 := by simp; omega
        have ht3 : (UInt8.ofNat (c.val.toNat % 64 + 0x80)).toNat =
            c.val.toNat % 64 + 0x80 := by simp; omega
        have hok : secondOk4 (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0))
            (UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80)) := by
          by_cases hF0 : c.val.toNat ≤ 0x3FFFF
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · by_cases hGen : c.val.toNat ≤ 0xFFFFF
            · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)
            · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
        rw [decodeSeq?_cons,
          if_neg (by omega : ¬ (UInt8.ofNat
            (c.val.toNat / 262144 % 8 + 0xF0)).toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ (UInt8.ofNat
            (c.val.toNat / 262144 % 8 + 0xF0)).toNat ∧
            (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0)).toNat ≤ 0xDF)),
          if_neg (by omega : ¬ (0xE0 ≤ (UInt8.ofNat
            (c.val.toNat / 262144 % 8 + 0xF0)).toNat ∧
            (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0)).toNat ≤ 0xEF)),
          if_pos (show 0xF0 ≤ (UInt8.ofNat
            (c.val.toNat / 262144 % 8 + 0xF0)).toNat ∧
            (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0)).toNat ≤ 0xF4 by omega)]
        simp only
        rw [if_pos (show secondOk4 (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0))
            (UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80)) ∧
            IsCont (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80)) ∧
            IsCont (UInt8.ofNat (c.val.toNat % 64 + 0x80)) from
          ⟨hok, ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩⟩)]
        have hpay : payload4 (UInt8.ofNat (c.val.toNat / 262144 % 8 + 0xF0))
            (UInt8.ofNat (c.val.toNat / 4096 % 64 + 0x80))
            (UInt8.ofNat (c.val.toNat / 64 % 64 + 0x80))
            (UInt8.ofNat (c.val.toNat % 64 + 0x80)) = c.val.toNat := by
          unfold payload4; omega
        rw [hpay, natToChar?_char]
        rfl

/-! ## The decoder accepts every well-formed sequence -/

theorem decodeSeq?_of_seq {s : List UInt8} (hs : Seq s) (rest : List UInt8) :
    ∃ c : Char, decodeSeq? (s ++ rest) = some (c, s.length) ∧
      encodeCodepoint c.val.toNat = s := by
  cases hs with
  | one h =>
      rename_i b
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (n := b.toNat) (Or.inl (by omega))
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b :: rest) = some (c, 1)
        rw [decodeSeq?_cons, if_pos h, hc]
        rfl
      · rw [hval]
        unfold encodeCodepoint
        rw [if_pos h]
        simp
  | two h₀ h₁ =>
      rename_i b₀ b₁
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload2_isValidChar h₀ h₁)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: rest) = some (c, 2)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_pos h₀]
        simp only
        rw [if_pos h₁, hc]
        rfl
      · rw [hval]; exact encode_payload2 h₀ h₁
  | threeE0 h₀ h₁ h₂ =>
      rename_i b₀ b₁ b₂
      have hok : secondOk3 b₀ b₁ := Or.inl ⟨h₀, h₁.1, h₁.2⟩
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload3_isValidChar hok h₂)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: rest) = some (c, 3)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_pos (show 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF by omega)]
        simp only
        rw [if_pos (show secondOk3 b₀ b₁ ∧ IsCont b₂ from ⟨hok, h₂⟩), hc]
        rfl
      · rw [hval]; exact encode_payload3 hok h₂
  | three h₀ h₁ h₂ =>
      rename_i b₀ b₁ b₂
      have hok : secondOk3 b₀ b₁ := Or.inr (Or.inl ⟨h₀.1, h₀.2, h₁⟩)
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload3_isValidChar hok h₂)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: rest) = some (c, 3)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_pos (show 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF by omega)]
        simp only
        rw [if_pos (show secondOk3 b₀ b₁ ∧ IsCont b₂ from ⟨hok, h₂⟩), hc]
        rfl
      · rw [hval]; exact encode_payload3 hok h₂
  | threeED h₀ h₁ h₂ =>
      rename_i b₀ b₁ b₂
      have hok : secondOk3 b₀ b₁ := Or.inr (Or.inr (Or.inl ⟨h₀, h₁.1, h₁.2⟩))
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload3_isValidChar hok h₂)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: rest) = some (c, 3)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_pos (show 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF by omega)]
        simp only
        rw [if_pos (show secondOk3 b₀ b₁ ∧ IsCont b₂ from ⟨hok, h₂⟩), hc]
        rfl
      · rw [hval]; exact encode_payload3 hok h₂
  | threeEF h₀ h₁ h₂ =>
      rename_i b₀ b₁ b₂
      have hok : secondOk3 b₀ b₁ := Or.inr (Or.inr (Or.inr ⟨h₀.1, h₀.2, h₁⟩))
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload3_isValidChar hok h₂)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: rest) = some (c, 3)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_pos (show 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF by omega)]
        simp only
        rw [if_pos (show secondOk3 b₀ b₁ ∧ IsCont b₂ from ⟨hok, h₂⟩), hc]
        rfl
      · rw [hval]; exact encode_payload3 hok h₂
  | fourF0 h₀ h₁ h₂ h₃ =>
      rename_i b₀ b₁ b₂ b₃
      have hok : secondOk4 b₀ b₁ := Or.inl ⟨h₀, h₁.1, h₁.2⟩
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload4_isValidChar hok h₂ h₃)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: b₃ :: rest) = some (c, 4)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_neg (by omega : ¬ (0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF)),
          if_pos (show 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 by omega)]
        simp only
        rw [if_pos (show secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃ from
          ⟨hok, h₂, h₃⟩), hc]
        rfl
      · rw [hval]; exact encode_payload4 hok h₂ h₃
  | four h₀ h₁ h₂ h₃ =>
      rename_i b₀ b₁ b₂ b₃
      have hok : secondOk4 b₀ b₁ := Or.inr (Or.inl ⟨h₀.1, h₀.2, h₁⟩)
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload4_isValidChar hok h₂ h₃)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: b₃ :: rest) = some (c, 4)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_neg (by omega : ¬ (0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF)),
          if_pos (show 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 by omega)]
        simp only
        rw [if_pos (show secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃ from
          ⟨hok, h₂, h₃⟩), hc]
        rfl
      · rw [hval]; exact encode_payload4 hok h₂ h₃
  | fourF4 h₀ h₁ h₂ h₃ =>
      rename_i b₀ b₁ b₂ b₃
      have hok : secondOk4 b₀ b₁ := Or.inr (Or.inr ⟨h₀, h₁.1, h₁.2⟩)
      obtain ⟨c, hc, hval⟩ := natToChar?_of_isValidChar
        (payload4_isValidChar hok h₂ h₃)
      refine ⟨c, ?_, ?_⟩
      · show decodeSeq? (b₀ :: b₁ :: b₂ :: b₃ :: rest) = some (c, 4)
        rw [decodeSeq?_cons, if_neg (by omega : ¬ b₀.toNat ≤ 0x7F),
          if_neg (by omega : ¬ (0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF)),
          if_neg (by omega : ¬ (0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF)),
          if_pos (show 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4 by omega)]
        simp only
        rw [if_pos (show secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃ from
          ⟨hok, h₂, h₃⟩), hc]
        rfl
      · rw [hval]; exact encode_payload4 hok h₂ h₃

end Utf8
