import Utf8.Decode

/-!
# The characterization: `Valid` iff `decode` succeeds

`decodeFuel` is fuelled by the input length; the stepping lemma below
reduces one fuel unit against one `decodeSeq?` step for an arbitrary
byte list, which is what both directions of the characterization use.

* `decodeFuel_of_valid` — every well-formed list decodes under any
  sufficient fuel, and the decoded characters re-encode to exactly
  the original bytes;
* `valid_of_decodeFuel` — every list the decoder accepts (under any
  fuel) is well-formed, and again the decoded characters re-encode
  to it;
* `valid_iff_decode` — the two together, for `decode` itself;
* `decode_encodeAll` — decoding an encoding is the identity.
-/

namespace Utf8

/-- One fuel unit of `decodeFuel` against one `decodeSeq?` step. -/
theorem decodeFuel_succ (f : Nat) (b : UInt8) (rest : List UInt8) :
    decodeFuel (f + 1) (b :: rest) =
      match decodeSeq? (b :: rest) with
      | none => none
      | some (c, k) => (decodeFuel f ((b :: rest).drop k)).map (c :: ·) :=
  rfl

/-- Stepping `decodeFuel` along a successful `decodeSeq?`, for an
arbitrary (not syntactically cons-shaped) byte list. -/
theorem decodeFuel_step_of_decodeSeq? {f : Nat} {l : List UInt8}
    {c : Char} {k : Nat} (h : decodeSeq? l = some (c, k)) :
    decodeFuel (f + 1) l = (decodeFuel f (l.drop k)).map (c :: ·) := by
  cases l with
  | nil => simp [decodeSeq?_nil] at h
  | cons b rest => rw [decodeFuel_succ, h]

/-- Every well-formed sequence has positive length (every row of
Table 3-7 has at least one byte). -/
theorem Seq.length_pos {s : List UInt8} (hs : Seq s) : 0 < s.length := by
  cases hs <;> simp

/-- `encodeAll` on a cons splits as one encoding followed by the rest. -/
theorem encodeAll_cons (c : Char) (cs : List Char) :
    encodeAll (c :: cs) = encodeCodepoint c.val.toNat ++ encodeAll cs :=
  rfl

/-- The encoding of a code point is nonempty. -/
theorem encodeCodepoint_length_pos (n : Nat) :
    0 < (encodeCodepoint n).length := by
  unfold encodeCodepoint
  by_cases h1 : n ≤ 0x7F
  · rw [if_pos h1]; simp
  · by_cases h2 : n ≤ 0x7FF
    · rw [if_neg h1, if_pos h2]; simp
    · by_cases h3 : n ≤ 0xFFFF
      · rw [if_neg h1, if_neg h2, if_pos h3]; simp
      · rw [if_neg h1, if_neg h2, if_neg h3]; simp

/-! ## Inverting one decoder step -/

/-- Invert the `Option.map` that `decodeSeq?` applies to `natToChar?`:
a successful step determines the character's value and the count. -/
theorem natToChar?_map_inj {n : Nat} {c : Char} {k m : Nat}
    (h : (natToChar? n).map (fun c => (c, m)) = some (c, k)) :
    c.val.toNat = n ∧ k = m := by
  cases hn : natToChar? n with
  | none => simp [hn] at h
  | some c' =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨natToChar?_val hn, rfl⟩

/-- A successful `decodeSeq?` step reads off a well-formed sequence:
the consumed prefix is a `Seq`, it is exactly the re-encoding of the
decoded character, and the step count is its length. -/
theorem seq_of_decodeSeq? {l : List UInt8} {c : Char} {k : Nat}
    (h : decodeSeq? l = some (c, k)) :
    ∃ s, Seq s ∧ encodeCodepoint c.val.toNat = s ∧
      l = s ++ l.drop s.length ∧ k = s.length := by
  cases l with
  | nil => simp [decodeSeq?_nil] at h
  | cons b₀ rest =>
      rw [decodeSeq?_cons] at h
      by_cases h1 : b₀.toNat ≤ 0x7F
      · rw [if_pos h1] at h
        obtain ⟨hcv, rfl⟩ := natToChar?_map_inj h
        refine ⟨[b₀], Seq.one h1, ?_, ?_, rfl⟩
        · rw [hcv]
          show encodeCodepoint b₀.toNat = [b₀]
          unfold encodeCodepoint
          rw [if_pos h1]
          simp
        · show b₀ :: rest = [b₀] ++ (b₀ :: rest).drop 1
          simp
      · rw [if_neg h1] at h
        by_cases h2 : 0xC2 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xDF
        · rw [if_pos h2] at h
          cases rest with
          | nil => simp at h
          | cons b₁ rest =>
              dsimp only at h
              by_cases hc : IsCont b₁
              · rw [if_pos hc] at h
                obtain ⟨hcv, rfl⟩ := natToChar?_map_inj h
                refine ⟨[b₀, b₁], Seq.two h2 hc, ?_, ?_, rfl⟩
                · rw [hcv]; exact encode_payload2 h2 hc
                · show b₀ :: b₁ :: rest = [b₀, b₁] ++ (b₀ :: b₁ :: rest).drop 2
                  simp
              · rw [if_neg hc] at h
                simp at h
        · rw [if_neg h2] at h
          by_cases h3 : 0xE0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xEF
          · rw [if_pos h3] at h
            cases rest with
            | nil => simp at h
            | cons b₁ rest =>
                cases rest with
                | nil => simp at h
                | cons b₂ rest =>
                    dsimp only at h
                    by_cases hc : secondOk3 b₀ b₁ ∧ IsCont b₂
                    · rw [if_pos hc] at h
                      obtain ⟨hcv, rfl⟩ := natToChar?_map_inj h
                      obtain ⟨hok, hc₂⟩ := hc
                      have hseq : Seq [b₀, b₁, b₂] := by
                        rcases hok with ⟨h0, h1a, h1b⟩ | ⟨h0, h0', hc1⟩ |
                          ⟨h0, h1a, h1b⟩ | ⟨h0, h0', hc1⟩
                        · exact Seq.threeE0 h0 ⟨h1a, h1b⟩ hc₂
                        · exact Seq.three ⟨h0, h0'⟩ hc1 hc₂
                        · exact Seq.threeED h0 ⟨h1a, h1b⟩ hc₂
                        · exact Seq.threeEF ⟨h0, h0'⟩ hc1 hc₂
                      refine ⟨[b₀, b₁, b₂], hseq, ?_, ?_, rfl⟩
                      · rw [hcv]; exact encode_payload3 hok hc₂
                      · show b₀ :: b₁ :: b₂ :: rest =
                          [b₀, b₁, b₂] ++ (b₀ :: b₁ :: b₂ :: rest).drop 3
                        simp
                    · rw [if_neg hc] at h
                      simp at h
          · rw [if_neg h3] at h
            by_cases h4 : 0xF0 ≤ b₀.toNat ∧ b₀.toNat ≤ 0xF4
            · rw [if_pos h4] at h
              cases rest with
              | nil => simp at h
              | cons b₁ rest =>
                  cases rest with
                  | nil => simp at h
                  | cons b₂ rest =>
                      cases rest with
                      | nil => simp at h
                      | cons b₃ rest =>
                          dsimp only at h
                          by_cases hc : secondOk4 b₀ b₁ ∧ IsCont b₂ ∧ IsCont b₃
                          · rw [if_pos hc] at h
                            obtain ⟨hcv, rfl⟩ := natToChar?_map_inj h
                            obtain ⟨hok, hc₂, hc₃⟩ := hc
                            have hseq : Seq [b₀, b₁, b₂, b₃] := by
                              rcases hok with ⟨h0, h1a, h1b⟩ | ⟨h0, h0', hc1⟩ |
                                ⟨h0, h1a, h1b⟩
                              · exact Seq.fourF0 h0 ⟨h1a, h1b⟩ hc₂ hc₃
                              · exact Seq.four ⟨h0, h0'⟩ hc1 hc₂ hc₃
                              · exact Seq.fourF4 h0 ⟨h1a, h1b⟩ hc₂ hc₃
                            refine ⟨[b₀, b₁, b₂, b₃], hseq, ?_, ?_, rfl⟩
                            · rw [hcv]; exact encode_payload4 hok hc₂ hc₃
                            · show b₀ :: b₁ :: b₂ :: b₃ :: rest =
                                [b₀, b₁, b₂, b₃] ++
                                  (b₀ :: b₁ :: b₂ :: b₃ :: rest).drop 4
                              simp
                          · rw [if_neg hc] at h
                            simp at h
            · rw [if_neg h4] at h
              simp at h

/-! ## Forward: well-formed lists decode -/

/-- Every well-formed byte list decodes under any sufficient fuel,
and the decoded characters re-encode to exactly the original bytes. -/
theorem decodeFuel_of_valid : ∀ (f : Nat) (l : List UInt8),
    l.length ≤ f → Valid l →
    ∃ cs, decodeFuel f l = some cs ∧ encodeAll cs = l := by
  intro f
  induction f with
  | zero =>
      intro l hl hv
      have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact ⟨[], decodeFuel_nil 0, rfl⟩
  | succ f ih =>
      intro l hl hv
      cases hv with
      | nil => exact ⟨[], decodeFuel_nil _, rfl⟩
      | cons hs hr =>
          rename_i s rest
          obtain ⟨c, hdec, henc⟩ := decodeSeq?_of_seq hs rest
          have hslen : 0 < s.length := Seq.length_pos hs
          have hrest : rest.length ≤ f := by
            simp only [List.length_append] at hl
            omega
          obtain ⟨cs, hcs, hencs⟩ := ih rest hrest hr
          refine ⟨c :: cs, ?_, ?_⟩
          · rw [decodeFuel_step_of_decodeSeq? hdec, List.drop_left, hcs]
            simp
          · rw [encodeAll_cons, henc, hencs]

/-! ## Backward: decoded lists are well-formed -/

/-- Every list the decoder accepts, under any fuel, is well-formed,
and the decoded characters re-encode to exactly that list. -/
theorem valid_of_decodeFuel : ∀ (f : Nat) (l : List UInt8)
    (cs : List Char),
    decodeFuel f l = some cs → Valid l ∧ encodeAll cs = l := by
  intro f
  induction f with
  | zero =>
      intro l cs h
      cases l with
      | nil =>
          have hcs : cs = [] := by
            have h0 : decodeFuel 0 ([] : List UInt8) = some [] :=
              decodeFuel_nil 0
            rw [h0] at h
            exact (Option.some.inj h).symm
          subst hcs
          exact ⟨Valid.nil, rfl⟩
      | cons b rest =>
          have h0 : decodeFuel 0 (b :: rest) = none := rfl
          rw [h0] at h
          cases h
  | succ f ih =>
      intro l cs h
      cases l with
      | nil =>
          have hcs : cs = [] := by
            have h0 : decodeFuel (f + 1) ([] : List UInt8) = some [] :=
              decodeFuel_nil _
            rw [h0] at h
            exact (Option.some.inj h).symm
          subst hcs
          exact ⟨Valid.nil, rfl⟩
      | cons b rest =>
          cases hds : decodeSeq? (b :: rest) with
          | none =>
              rw [decodeFuel_succ, hds] at h
              cases h
          | some p =>
              obtain ⟨c, k⟩ := p
              rw [decodeFuel_succ, hds] at h
              dsimp only at h
              cases hdf : decodeFuel f ((b :: rest).drop k) with
              | none =>
                  rw [hdf] at h
                  simp at h
              | some cs' =>
                  rw [hdf] at h
                  simp only [Option.map_some, Option.some.injEq] at h
                  subst h
                  obtain ⟨s, hs, henc, hleq, hk⟩ := seq_of_decodeSeq? hds
                  obtain ⟨hv, henc'⟩ := ih _ _ hdf
                  refine ⟨?_, ?_⟩
                  · rw [hleq, ← hk]
                    exact Valid.cons hs hv
                  · rw [encodeAll_cons, henc, henc']
                    rw [← hk] at hleq
                    exact hleq.symm

/-! ## The characterization for `decode` -/

/-- Decoding an encoding is the identity, under any sufficient fuel. -/
theorem decodeFuel_encodeAll : ∀ (f : Nat) (cs : List Char),
    (encodeAll cs).length ≤ f → decodeFuel f (encodeAll cs) = some cs := by
  intro f
  induction f with
  | zero =>
      intro cs h
      cases cs with
      | nil => exact decodeFuel_nil 0
      | cons c cs =>
          have hpos : 0 < (encodeAll (c :: cs)).length := by
            rw [encodeAll_cons, List.length_append]
            have := encodeCodepoint_length_pos c.val.toNat
            omega
          omega
  | succ f ih =>
      intro cs h
      cases cs with
      | nil => exact decodeFuel_nil _
      | cons c cs =>
          have hrest : (encodeAll cs).length ≤ f := by
            rw [encodeAll_cons, List.length_append] at h
            have := encodeCodepoint_length_pos c.val.toNat
            omega
          rw [encodeAll_cons,
            decodeFuel_step_of_decodeSeq?
              (decodeSeq?_encodeCodepoint c (encodeAll cs)),
            List.drop_left, ih cs hrest]
          simp only [Option.map_some]

/-- **Decoding an encoding is the identity.** -/
theorem decode_encodeAll (cs : List Char) :
    decode (encodeAll cs) = some cs :=
  decodeFuel_encodeAll _ cs (Nat.le_refl _)

/-- **The characterization.** A byte list is well-formed UTF-8 in the
sense of Table 3-7 (`Valid`) if and only if the executable decoder
accepts it — and then the decoded characters re-encode to exactly
the original bytes. -/
theorem valid_iff_decode {l : List UInt8} :
    Valid l ↔ ∃ cs, decode l = some cs ∧ encodeAll cs = l := by
  constructor
  · intro hv
    exact decodeFuel_of_valid l.length l (Nat.le_refl _) hv
  · rintro ⟨cs, hdec, henc⟩
    obtain ⟨hv, -⟩ := valid_of_decodeFuel l.length l cs hdec
    exact hv

/-- The decoder rejects exactly the lists that are not well-formed. -/
theorem decode_eq_none_iff {l : List UInt8} :
    decode l = none ↔ ¬ Valid l := by
  constructor
  · intro h hv
    obtain ⟨cs, hdec, -⟩ := valid_iff_decode.1 hv
    rw [h] at hdec
    cases hdec
  · intro hv
    cases hdec : decode l with
    | some cs =>
        obtain ⟨-, henc⟩ := valid_of_decodeFuel l.length l cs hdec
        exact absurd (valid_iff_decode.2 ⟨cs, hdec, henc⟩) hv
    | none => rfl

end Utf8
