import Utf8.Core

/-!
# Kernel-checked examples: RFC 3629 / Unicode Table 3-7

Every example is a theorem proved by kernel computation (`decide`)
through the characterization `valid_iff_decode` — no `native_decide`
anywhere. Valid examples pin both the decoded characters and the
re-encoding; invalid examples pin `decode … = none` and `¬ Valid …`.

The invalid list is the standard rogues' gallery of RFC 3629 §3 and
the Unicode conformance discussion: overlong (non-shortest) forms in
every width, the UTF-16 surrogates U+D800–U+DFFF (`ED A0 …` /
`ED BF …`), the first code point above U+10FFFF (`F4 90 …`), lead
bytes that begin no row of Table 3-7 (`80`, `C0`, `C1`, `F5`, `FF`),
bad continuation bytes, and truncated sequences.

The file ends with general exclusion theorems: whole families of
byte sequences (overlong two-byte leads `C0`/`C1`, surrogate second
bytes after `ED`, second bytes below the `E0`/`F0` floors, second
bytes above the `F4` ceiling) are invalid for *every* choice of the
remaining bytes.
-/

namespace Utf8.Examples

/-! ## Valid sequences -/

theorem valid_empty : Valid [] :=
  valid_iff_decode.2 ⟨[], by decide, by decide⟩

theorem valid_dollar : Valid [0x24] ∧ decode [0x24] = some ['$'] :=
  ⟨valid_iff_decode.2 ⟨['$'], by decide, by decide⟩, by decide⟩

/-- U+00A2 CENT SIGN: the smallest interesting two-byte row value
in RFC 3629's examples. -/
theorem valid_cent : Valid [0xC2, 0xA2] ∧ decode [0xC2, 0xA2] = some ['¢'] :=
  ⟨valid_iff_decode.2 ⟨['¢'], by decide, by decide⟩, by decide⟩

/-- U+00E9 LATIN SMALL LETTER E WITH ACUTE. -/
theorem valid_e_acute : Valid [0xC3, 0xA9] ∧ decode [0xC3, 0xA9] = some ['é'] :=
  ⟨valid_iff_decode.2 ⟨['é'], by decide, by decide⟩, by decide⟩

/-- U+0800: the smallest three-byte encoding (the `E0` floor). -/
theorem valid_smallest_three :
    Valid [0xE0, 0xA0, 0x80] ∧ decode [0xE0, 0xA0, 0x80] = some ['ࠀ'] :=
  ⟨valid_iff_decode.2 ⟨['ࠀ'], by decide, by decide⟩, by decide⟩

/-- U+20AC EURO SIGN. -/
theorem valid_euro :
    Valid [0xE2, 0x82, 0xAC] ∧ decode [0xE2, 0x82, 0xAC] = some ['€'] :=
  ⟨valid_iff_decode.2 ⟨['€'], by decide, by decide⟩, by decide⟩

/-- U+D7FF: the last code point below the surrogate range. -/
theorem valid_below_surrogates : Valid [0xED, 0x9F, 0xBF] :=
  valid_iff_decode.2 ⟨['퟿'], by decide, by decide⟩

/-- U+E000: the first code point above the surrogate range. -/
theorem valid_above_surrogates : Valid [0xEE, 0x80, 0x80] :=
  valid_iff_decode.2 ⟨[''], by decide, by decide⟩

/-- U+10000: the smallest four-byte encoding (the `F0` floor). -/
theorem valid_smallest_four : Valid [0xF0, 0x90, 0x80, 0x80] :=
  valid_iff_decode.2 ⟨['𐀀'], by decide, by decide⟩

/-- U+10348 (Gothic letter hwair), RFC 3629's four-byte example. -/
theorem valid_gothic :
    Valid [0xF0, 0x90, 0x8D, 0x88] ∧
      decode [0xF0, 0x90, 0x8D, 0x88] = some ['𐍈'] :=
  ⟨valid_iff_decode.2 ⟨['𐍈'], by decide, by decide⟩, by decide⟩

/-- U+1F600, a four-byte encoding from the `F1–F3` rows' range. -/
theorem valid_emoji :
    Valid [0xF0, 0x9F, 0x98, 0x80] ∧
      decode [0xF0, 0x9F, 0x98, 0x80] = some ['😀'] :=
  ⟨valid_iff_decode.2 ⟨['😀'], by decide, by decide⟩, by decide⟩

/-- U+10FFFF: the largest code point (the `F4` ceiling). -/
theorem valid_max : Valid [0xF4, 0x8F, 0xBF, 0xBF] :=
  valid_iff_decode.2 ⟨[Char.ofNat 0x10FFFF], by decide, by decide⟩

/-- A mixed-width concatenation: `a`, `¢`, `€`, U+10348. -/
theorem valid_mixed :
    Valid [0x61, 0xC2, 0xA2, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88] ∧
      decode [0x61, 0xC2, 0xA2, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88] =
        some ['a', '¢', '€', '𐍈'] :=
  ⟨valid_iff_decode.2 ⟨['a', '¢', '€', '𐍈'], by decide, by decide⟩,
   by decide⟩

/-! ## Invalid sequences -/

theorem invalid_overlong_nul :
    decode [0xC0, 0x80] = none ∧ ¬ Valid [0xC0, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_overlong_c1 :
    decode [0xC1, 0xBF] = none ∧ ¬ Valid [0xC1, 0xBF] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- Overlong three-byte form of U+0000's range: `E0` with second
byte below `A0`. -/
theorem invalid_overlong_three_low :
    decode [0xE0, 0x80, 0x80] = none ∧ ¬ Valid [0xE0, 0x80, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_overlong_three_edge :
    decode [0xE0, 0x9F, 0xBF] = none ∧ ¬ Valid [0xE0, 0x9F, 0xBF] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- Overlong four-byte form: `F0` with second byte below `90`. -/
theorem invalid_overlong_four :
    decode [0xF0, 0x80, 0x80, 0x80] = none ∧ ¬ Valid [0xF0, 0x80, 0x80, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_overlong_four_edge :
    decode [0xF0, 0x8F, 0xBF, 0xBF] = none ∧
      ¬ Valid [0xF0, 0x8F, 0xBF, 0xBF] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- U+D800, the first UTF-16 surrogate: `ED A0 80`. -/
theorem invalid_surrogate_low :
    decode [0xED, 0xA0, 0x80] = none ∧ ¬ Valid [0xED, 0xA0, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- U+DFFF, the last UTF-16 surrogate: `ED BF BF`. -/
theorem invalid_surrogate_high :
    decode [0xED, 0xBF, 0xBF] = none ∧ ¬ Valid [0xED, 0xBF, 0xBF] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- The first byte sequence past U+10FFFF: `F4 90 80 80`. -/
theorem invalid_above_max :
    decode [0xF4, 0x90, 0x80, 0x80] = none ∧
      ¬ Valid [0xF4, 0x90, 0x80, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_lead_f5 :
    decode [0xF5, 0x80, 0x80, 0x80] = none ∧
      ¬ Valid [0xF5, 0x80, 0x80, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_lead_ff :
    decode [0xFF] = none ∧ ¬ Valid [0xFF] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_lone_continuation :
    decode [0x80] = none ∧ ¬ Valid [0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_bad_continuation :
    decode [0xC2, 0x41] = none ∧ ¬ Valid [0xC2, 0x41] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_truncated_two :
    decode [0xC2] = none ∧ ¬ Valid [0xC2] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_truncated_three :
    decode [0xE2, 0x82] = none ∧ ¬ Valid [0xE2, 0x82] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

theorem invalid_truncated_four :
    decode [0xF0, 0x90, 0x8D] = none ∧ ¬ Valid [0xF0, 0x90, 0x8D] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-- A valid prefix does not rescue an invalid tail. -/
theorem invalid_after_valid_prefix :
    decode [0x61, 0xC0, 0x80] = none ∧ ¬ Valid [0x61, 0xC0, 0x80] :=
  ⟨by decide, decode_eq_none_iff.1 (by decide)⟩

/-! ## General exclusions -/

/-- A lead byte matching no row of Table 3-7 is rejected outright,
whatever follows it. -/
theorem decodeSeq?_lead_invalid {b : UInt8} (rest : List UInt8)
    (h1 : ¬ b.toNat ≤ 0x7F)
    (h2 : ¬ (0xC2 ≤ b.toNat ∧ b.toNat ≤ 0xDF))
    (h3 : ¬ (0xE0 ≤ b.toNat ∧ b.toNat ≤ 0xEF))
    (h4 : ¬ (0xF0 ≤ b.toNat ∧ b.toNat ≤ 0xF4)) :
    decodeSeq? (b :: rest) = none := by
  rw [decodeSeq?_cons, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- No byte sequence beginning with `C0` or `C1` decodes: those
leads could only start overlong two-byte forms. -/
theorem decodeSeq?_overlong_lead (rest : List UInt8) :
    decodeSeq? (0xC0 :: rest) = none ∧ decodeSeq? (0xC1 :: rest) = none :=
  ⟨decodeSeq?_lead_invalid rest (by decide) (by decide) (by decide)
      (by decide),
   decodeSeq?_lead_invalid rest (by decide) (by decide) (by decide)
      (by decide)⟩

/-- No byte sequence beginning with a continuation byte, or with a
lead `F5`–`FF`, decodes. -/
theorem decodeSeq?_bad_lead (rest : List UInt8) :
    decodeSeq? (0x80 :: rest) = none ∧ decodeSeq? (0xF5 :: rest) = none ∧
      decodeSeq? (0xFF :: rest) = none :=
  ⟨decodeSeq?_lead_invalid rest (by decide) (by decide) (by decide)
      (by decide),
   decodeSeq?_lead_invalid rest (by decide) (by decide) (by decide)
      (by decide),
   decodeSeq?_lead_invalid rest (by decide) (by decide) (by decide)
      (by decide)⟩

/-- If the first step of decoding a nonempty list fails, the whole
decode fails. (The empty list is not a counterexample: its first
step fails by convention but `decode [] = some []`.) -/
theorem decode_eq_none_of_decodeSeq?_eq_none {b : UInt8}
    {rest : List UInt8} (h : decodeSeq? (b :: rest) = none) :
    decode (b :: rest) = none := by
  obtain ⟨f, hf⟩ : ∃ f, (b :: rest).length = f + 1 :=
    ⟨rest.length, by simp⟩
  show decodeFuel (b :: rest).length (b :: rest) = none
  rw [hf, decodeFuel_succ, h]

/-- Every two-byte sequence with lead `C0` or `C1` is invalid, for
every second byte: the overlong two-byte forms are excluded as a
family, not just at the tested points. -/
theorem not_valid_overlong_two {b₀ b₁ : UInt8}
    (h : b₀ = 0xC0 ∨ b₀ = 0xC1) : ¬ Valid [b₀, b₁] := by
  apply decode_eq_none_iff.1
  apply decode_eq_none_of_decodeSeq?_eq_none
  rcases h with rfl | rfl
  · exact (decodeSeq?_overlong_lead [b₁]).1
  · exact (decodeSeq?_overlong_lead [b₁]).2

/-- Every `ED` sequence whose second byte is in `A0`–`BF` is
invalid, for every third byte: those are exactly the surrogate
encodings U+D800–U+DFFF. -/
theorem not_valid_surrogate {b₁ b₂ : UInt8}
    (h₁ : 0xA0 ≤ b₁.toNat ∧ b₁.toNat ≤ 0xBF) : ¬ Valid [0xED, b₁, b₂] := by
  apply decode_eq_none_iff.1
  apply decode_eq_none_of_decodeSeq?_eq_none
  have hso : ¬ secondOk3 (0xED : UInt8) b₁ := by
    have hED : (0xED : UInt8).toNat = 0xED := rfl
    intro h
    rcases h with ⟨h0, -, -⟩ | ⟨h0, h0', -⟩ | ⟨h0, -, h1'⟩ | ⟨h0, -, -⟩
    · omega
    · omega
    · omega
    · omega
  rw [decodeSeq?_cons, if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  dsimp only
  rw [if_neg (fun h => hso h.1)]

/-- Every `E0` sequence whose second byte is below `A0` is invalid,
for every third byte: the overlong three-byte forms. -/
theorem not_valid_overlong_e0 {b₁ b₂ : UInt8}
    (h₁ : IsCont b₁) (h₁' : b₁.toNat < 0xA0) :
    ¬ Valid [0xE0, b₁, b₂] := by
  apply decode_eq_none_iff.1
  apply decode_eq_none_of_decodeSeq?_eq_none
  have hso : ¬ secondOk3 (0xE0 : UInt8) b₁ := by
    have hE0 : (0xE0 : UInt8).toNat = 0xE0 := rfl
    intro h
    rcases h with ⟨-, h1a, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · omega
    · omega
    · omega
    · omega
  rw [decodeSeq?_cons, if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  dsimp only
  rw [if_neg (fun h => hso h.1)]

/-- Every `F0` sequence whose second byte is below `90` is invalid,
for every choice of the remaining bytes: the overlong four-byte
forms. -/
theorem not_valid_overlong_f0 {b₁ b₂ b₃ : UInt8}
    (h₁ : IsCont b₁) (h₁' : b₁.toNat < 0x90) :
    ¬ Valid [0xF0, b₁, b₂, b₃] := by
  apply decode_eq_none_iff.1
  apply decode_eq_none_of_decodeSeq?_eq_none
  have hso : ¬ secondOk4 (0xF0 : UInt8) b₁ := by
    have hF0 : (0xF0 : UInt8).toNat = 0xF0 := rfl
    intro h
    rcases h with ⟨-, h1a, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
    · omega
    · omega
    · omega
  rw [decodeSeq?_cons, if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  dsimp only
  rw [if_neg (fun h => hso h.1)]

/-- Every `F4` sequence whose second byte is above `8F` is invalid,
for every choice of the remaining bytes: those encode code points
above U+10FFFF. -/
theorem not_valid_above_max {b₁ b₂ b₃ : UInt8}
    (h₁ : IsCont b₁) (h₁' : 0x8F < b₁.toNat) :
    ¬ Valid [0xF4, b₁, b₂, b₃] := by
  apply decode_eq_none_iff.1
  apply decode_eq_none_of_decodeSeq?_eq_none
  have hso : ¬ secondOk4 (0xF4 : UInt8) b₁ := by
    have hF4 : (0xF4 : UInt8).toNat = 0xF4 := rfl
    intro h
    rcases h with ⟨h0, -, -⟩ | ⟨h0, h0', -⟩ | ⟨-, -, h1b⟩
    · omega
    · omega
    · omega
  rw [decodeSeq?_cons, if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]
  dsimp only
  rw [if_neg (fun h => hso h.1)]

end Utf8.Examples
