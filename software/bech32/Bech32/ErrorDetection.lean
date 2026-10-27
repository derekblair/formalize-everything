import Bech32.Distance
import Bech32.Codec

/-! # Bech32 / Bech32m error detection (milestone 2)

The machine-checked error-detection guarantee for the Bech32/Bech32m
checksums, following the design dossier
`lane-reports/argon-bech32-m2-dossier.md` (its §5.2 is the build spec;
§1.3–§1.4 give the statements).

Contents:
* parser inversion for `splitLast` and `decodeChars` (dossier L5.1–L5.3);
* the string-level guarantees in their refined, true forms (L5.5):
  fixed-HRP form, separator-preserving + high-bit-preserving form,
  alphabetic-HRP form, and the single-substitution form;
* the BIP-350 insertion point (L5.6): Bech32 admits inserted `q`
  characters undetected, Bech32m detects them (all counts `1 ≤ k ≤ 1022`),
  and the two variants are disjoint at distance `≤ 2` in range;
* kernel-checked counterexamples for every failure mechanism of the
  naive string-level claim (L5.7).
-/

namespace Bech32

/-!
# Error detection at the string level (milestone 2, ticket #16)

Parser inversion (`splitLast` / `decodeChars`), the refined string-level
substitution guarantees (Form A: fixed expected HRP; Form B:
separator-preserving + Footnote-4 high-bit-preserving; the alphabetic-HRP
specialization; unconditional single substitution), the BIP-350
`'q'`-insertion weakness of Bech32 and its Bech32m repair, the
cross-variant distance-3 bound, and the kernel-checked counterexamples
showing every hypothesis of the refined statements is necessary
(dossier §1.3/§1.4, §5.2 L5.1–L5.7).
-/


/-! ## Local mirrors of the three `Codec` helpers the dossier names

The dossier (§5.2) allows dropping `private` on these three helpers;
instead they are re-proved here under local names, leaving milestone 1
untouched (dossier §5.2 line 351 sanctions this fallback). -/

/-- Local mirror of Codec's private `toLower_eq_self_of_not_upper`. -/
theorem toLower_eq_self_of_not_upper_local {c : Char} (h : c.isUpper = false) :
    c.toLower = c := by
  simp only [Char.isUpper, decide_eq_false_iff_not] at h
  unfold Char.toLower
  rw [dite_eq_right h]

/-- Local mirror of Codec's private `map_toLower_of_not_upper`. -/
theorem map_toLower_of_not_upper_local {cs : List Char}
    (h : cs.any Char.isUpper = false) : cs.map Char.toLower = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp [toLower_eq_self_of_not_upper_local h.1, ih h.2]

/-- Local mirror of Codec's private `lower_printable`. -/
theorem lower_printable_local {c : Char} (h : printable c = true) :
    printable c.toLower = true ∧ c.toLower.isUpper = false := by
  have hlt : c.toNat < 128 := by
    simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  have finite : ∀ n : Fin 128, printable (Char.ofNat n.val) = true →
      printable (Char.ofNat n.val).toLower = true ∧
      (Char.ofNat n.val).toLower.isUpper = false := by decide
  simpa using finite ⟨c.toNat, hlt⟩ (by simpa using h)

/-! ## `splitLast` inversion (dossier L5.1) -/

/-- `splitLast` finds no separator in a list with no `'1'`. -/
theorem splitLast_eq_none_of_not_mem {cs : List Char} (h : '1' ∉ cs) :
    splitLast cs = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '1' := fun hc => h (hc ▸ List.mem_cons_self)
    have hcs : '1' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
    simp only [splitLast, ih hcs]
    rw [if_neg (by simp [hc])]

/-- One `splitLast` step over a successful split. -/
theorem splitLast_cons_of_some {c : Char} {l hrp raw : List Char}
    (h : splitLast l = some (hrp, raw)) :
    splitLast (c :: l) = some (c :: hrp, raw) := by
  show (match splitLast l with
      | some (a, b) => some (c :: a, b)
      | none => if c == '1' then some ([], l) else none) =
    some (c :: hrp, raw)
  rw [h]

/-- One `splitLast` step over a failed split. -/
theorem splitLast_cons_of_none {c : Char} {l : List Char}
    (h : splitLast l = none) :
    splitLast (c :: l) = if c == '1' then some ([], l) else none := by
  show (match splitLast l with
      | some (a, b) => some (c :: a, b)
      | none => if c == '1' then some ([], l) else none) =
    (if c == '1' then some ([], l) else none)
  rw [h]

/-- If `splitLast` returns `none`, the list has no `'1'`. -/
theorem not_mem_of_splitLast_eq_none :
    ∀ {cs : List Char}, splitLast cs = none → '1' ∉ cs := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons c cs ih =>
    intro h hm
    cases hcs : splitLast cs with
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [splitLast_cons_of_some hcs] at h
      cases h
    | none =>
      rw [splitLast_cons_of_none hcs] at h
      by_cases hc : c = '1'
      · rw [if_pos (by simp [hc])] at h
        cases h
      · rcases List.mem_cons.mp hm with rfl | hm'
        · exact hc rfl
        · exact ih hcs hm'

/-- `splitLast cs = none` iff there is no separator (dossier L5.1). -/
theorem splitLast_eq_none_iff {cs : List Char} :
    splitLast cs = none ↔ '1' ∉ cs :=
  ⟨not_mem_of_splitLast_eq_none, splitLast_eq_none_of_not_mem⟩

/-- Forward direction of L5.1: a successful `splitLast` exhibits the split. -/
theorem splitLast_eq_some_imp {cs hrp raw : List Char}
    (h : splitLast cs = some (hrp, raw)) :
    cs = hrp ++ '1' :: raw ∧ '1' ∉ raw := by
  induction cs generalizing hrp raw with
  | nil => simp [splitLast] at h
  | cons c cs ih =>
    cases hcs : splitLast cs with
    | some p =>
      obtain ⟨a, b⟩ := p
      rw [splitLast_cons_of_some hcs] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      subst h1; subst h2
      obtain ⟨e1, e2⟩ := ih hcs
      exact ⟨by rw [e1]; rfl, e2⟩
    | none =>
      rw [splitLast_cons_of_none hcs] at h
      have hnm : '1' ∉ cs := not_mem_of_splitLast_eq_none hcs
      by_cases hc : c = '1'
      · rw [if_pos (by simp [hc])] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
        subst h1; subst h2
        exact ⟨by simp [hc], hnm⟩
      · rw [if_neg (by simp [hc])] at h
        cases h

/-- Backward direction of L5.1: the exhibited split is found. -/
theorem splitLast_eq_some_of {hrp raw : List Char} (h : '1' ∉ raw) :
    splitLast (hrp ++ '1' :: raw) = some (hrp, raw) := by
  induction hrp with
  | nil =>
    show splitLast ('1' :: raw) = some ([], raw)
    rw [splitLast_cons_of_none (splitLast_eq_none_of_not_mem h)]
    exact if_pos (by decide)
  | cons c cs ih =>
    rw [List.cons_append, splitLast_cons_of_some ih]

/-- L5.1 (dossier): `splitLast` inversion. -/
theorem splitLast_eq_some_iff {cs hrp raw : List Char} :
    splitLast cs = some (hrp, raw) ↔
      cs = hrp ++ '1' :: raw ∧ '1' ∉ raw :=
  ⟨splitLast_eq_some_imp,
   fun h => h.1 ▸ splitLast_eq_some_of h.2⟩

/-- A successful split puts a `'1'` in the list. -/
theorem mem_of_splitLast_eq_some {cs hrp raw : List Char}
    (h : splitLast cs = some (hrp, raw)) : '1' ∈ cs := by
  obtain ⟨e, _⟩ := splitLast_eq_some_imp h
  rw [e]
  exact List.mem_append_right _ List.mem_cons_self

/-! ## BIP-350 insertion weakness (dossier L5.6), Bech32 side -/

/-- If one symbol `1` fixes a state, then a zero symbol annihilates it:
    `polymodStep` is XOR-linear and `polymodStep 0 1 = 1`. -/
theorem polymodStep_zero_of_step_one {s : BitVec 30}
    (h : polymodStep s 1 = 1) : polymodStep s 0 = 0 := by
  have e : polymodStep s 1 = polymodStep s 0 ^^^ 1 := by
    have e1 := polymodStep_xor s 0 0 1
    have hz1 : s ^^^ (0 : BitVec 30) = s := BitVec.xor_zero
    have hz2 : (0 : Word) ^^^ (1 : Word) = 1 := BitVec.zero_xor
    rw [hz1, hz2] at e1
    rw [e1, polymodStep_zero_left]
    rfl
  rw [e] at h
  have h2 := congrArg (fun z => z ^^^ (1 : BitVec 30)) h
  have hz : (1 : BitVec 30) ^^^ (1 : BitVec 30) = 0 := BitVec.xor_self
  rw [BitVec.xor_assoc, hz] at h2
  have hxz : polymodStep s 0 ^^^ (0 : BitVec 30) = polymodStep s 0 :=
    BitVec.xor_zero
  rw [hxz] at h2
  exact h2

/-- Zero symbols fed into the zero state never leave it. -/
theorem foldl_polymodStep_replicate_zero (k : Nat) :
    (List.replicate k (0 : Word)).foldl polymodStep 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, polymodStep_zero]
    exact ih

/-- BIP-350's `'q'`-insertion weakness, Bech32 form (dossier L5.6):
    if `pfx ++ [1]` verifies, then inserting any number of `'q'` (zero)
    symbols just before the final `1` still verifies. -/
theorem bech32_q_insertion_undetected (hrp : List Char) (pfx : List Word)
    (k : Nat)
    (hvalid : verifyChecksum Variant.bech32 hrp (pfx ++ [1]) = true) :
    verifyChecksum Variant.bech32 hrp
      (pfx ++ List.replicate k 0 ++ [1]) = true := by
  have hstep : polymodStep ((hrpExpand hrp ++ pfx).foldl polymodStep 1) 1
      = 1 := by
    have hv := hvalid
    simp only [verifyChecksum, beq_iff_eq] at hv
    have hconst : Variant.bech32.constant = (1 : BitVec 30) := rfl
    rw [hconst] at hv
    unfold polymod at hv
    rw [← List.append_assoc, List.foldl_append] at hv
    exact hv
  have hzero := polymodStep_zero_of_step_one hstep
  have hfold : ∀ j : Nat, (List.replicate j (0 : Word)).foldl polymodStep
      ((hrpExpand hrp ++ pfx).foldl polymodStep 1) =
      if j = 0 then (hrpExpand hrp ++ pfx).foldl polymodStep 1 else 0 := by
    intro j
    cases j with
    | zero => rfl
    | succ j =>
      rw [List.replicate_succ, List.foldl_cons, hzero,
        foldl_polymodStep_replicate_zero]
      exact (if_neg (Nat.succ_ne_zero j)).symm
  simp only [verifyChecksum, beq_iff_eq]
  show polymod (hrpExpand hrp ++ (pfx ++ List.replicate k 0 ++ [1])) = 1
  rw [show hrpExpand hrp ++ (pfx ++ List.replicate k 0 ++ [1]) =
      (hrpExpand hrp ++ pfx) ++ (List.replicate k 0 ++ [1]) by
      simp [List.append_assoc]]
  show ((hrpExpand hrp ++ pfx) ++ (List.replicate k 0 ++ [1])).foldl
      polymodStep 1 = 1
  rw [List.foldl_append, List.foldl_append, hfold]
  cases k with
  | zero => exact hstep
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    show polymodStep 0 1 = 1
    decide

/-- L5.2 (dossier): `mapM charToWord` inversion. -/
theorem mapM_charToWord_eq_some_iff {raw : List Char} {words : List Word} :
    raw.mapM charToWord = some words ↔ raw = words.map charOfWord := by
  constructor
  · intro h
    induction raw generalizing words with
    | nil =>
      simp at h
      subst h
      rfl
    | cons c cs ih =>
      rw [List.mapM_cons] at h
      obtain ⟨w, hw, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ws, hws, hww⟩ := Option.bind_eq_some_iff.mp hrest
      change some (w :: ws) = some words at hww
      rw [Option.some.injEq] at hww
      subst hww
      have hc : charOfWord w = c := charOfWord_charToWord hw
      rw [ih hws, ← hc]
      rfl
  · intro h
    rw [h]
    exact map_charToWord words

/-- Reduction of `decodeChars` when the textual guards pass. -/
theorem decodeChars_reduce {v : Variant} {s : List Char}
    (hlen : s.length ≤ 90) (hprint : s.all printable = true)
    (hcase : s.any Char.isUpper = false ∨ s.any Char.isLower = false) :
    decodeChars v s = (splitLast (s.map Char.toLower)).bind
      (fun (hrp, raw) =>
        if hrp.isEmpty || raw.length < 6 then none
        else (raw.mapM charToWord).bind (fun words =>
          if verifyChecksum v hrp words then
            some (hrp, words.take (words.length - 6))
          else none)) := by
  have hg : (s.length > 90 || !(s.all printable) ||
      (s.any Char.isUpper && s.any Char.isLower)) = false := by
    have h1 : (decide (s.length > 90)) = false :=
      decide_eq_false_iff_not.mpr (Nat.not_lt.mpr hlen)
    have h3 : (s.any Char.isUpper && s.any Char.isLower) = false := by
      cases hcase with
      | inl h => simp [h]
      | inr h => simp [h]
    simp only [h1, h3, hprint, Bool.not_true, Bool.false_or]
  unfold decodeChars
  rw [if_neg (by simp [hg])]
  cases hsplit : splitLast (s.map Char.toLower) with
  | none => rfl
  | some p =>
    obtain ⟨hrp, raw⟩ := p
    rfl

/-- L5.3 (dossier): complete inversion of `decodeChars`. -/
theorem decodeChars_eq_some_iff {v : Variant} {s : List Char}
    {hrp : List Char} {payload : List Word} :
    decodeChars v s = some (hrp, payload) ↔
      s.length ≤ 90 ∧ s.all printable = true ∧
      (s.any Char.isUpper = false ∨ s.any Char.isLower = false) ∧
      ∃ (raw : List Char) (words : List Word),
        splitLast (s.map Char.toLower) = some (hrp, raw) ∧
        hrp ≠ [] ∧ 6 ≤ raw.length ∧ raw = words.map charOfWord ∧
        verifyChecksum v hrp words = true ∧
        payload = words.take (words.length - 6) := by
  constructor
  · intro h
    have hg : (s.length > 90 || !(s.all printable) ||
        (s.any Char.isUpper && s.any Char.isLower)) = false := by
      apply Classical.byContradiction
      intro hg
      have hg' : (s.length > 90 || !(s.all printable) ||
          (s.any Char.isUpper && s.any Char.isLower)) = true := by
        cases hb : (s.length > 90 || !(s.all printable) ||
            (s.any Char.isUpper && s.any Char.isLower)) <;> simp_all
      have hnone : decodeChars v s = none := by
        unfold decodeChars
        rw [if_pos hg']
      rw [hnone] at h
      cases h
    have hlen : s.length ≤ 90 := by
      apply Classical.byContradiction
      intro hcon
      have h1 : (decide (s.length > 90)) = true := by
        rw [decide_eq_true_eq]
        exact Nat.lt_of_not_le hcon
      rw [h1, Bool.true_or, Bool.true_or] at hg
      cases hg
    have hprint : s.all printable = true := by
      apply Classical.byContradiction
      intro hcon
      have h1 : s.all printable = false := by
        cases hb : s.all printable <;> simp_all
      rw [h1] at hg
      simp only [Bool.not_false, Bool.or_true, Bool.true_or] at hg
      cases hg
    have hcase : s.any Char.isUpper = false ∨ s.any Char.isLower = false := by
      apply Classical.byContradiction
      intro hcon
      have ha : s.any Char.isUpper = true := by
        cases hb : s.any Char.isUpper <;> simp_all
      have hb2 : s.any Char.isLower = true := by
        cases hb : s.any Char.isLower <;> simp_all
      have h3 : (s.any Char.isUpper && s.any Char.isLower) = true := by
        rw [Bool.and_eq_true]
        exact ⟨ha, hb2⟩
      rw [h3, Bool.or_true] at hg
      cases hg
    rw [decodeChars_reduce hlen hprint hcase] at h
    obtain ⟨⟨hrp', raw⟩, hsplit, hrest⟩ := Option.bind_eq_some_iff.mp h
    have hrest' : (if hrp'.isEmpty || raw.length < 6 then none
        else (raw.mapM charToWord).bind (fun words =>
          if verifyChecksum v hrp' words then
            some (hrp', words.take (words.length - 6))
          else none)) = some (hrp, payload) := hrest
    cases hcond : (hrp'.isEmpty || raw.length < 6) with
    | true =>
      rw [if_pos hcond] at hrest'
      cases hrest'
    | false =>
      rw [if_neg (by simp [hcond])] at hrest'
      obtain ⟨he, hl⟩ := Bool.or_eq_false_iff.mp hcond
      obtain ⟨words, hmapM, hfin⟩ := Option.bind_eq_some_iff.mp hrest'
      have hfin' : (if verifyChecksum v hrp' words then
            some (hrp', words.take (words.length - 6))
          else none) = some (hrp, payload) := hfin
      cases hv : verifyChecksum v hrp' words with
      | false =>
        rw [if_neg (by simp [hv])] at hfin'
        cases hfin'
      | true =>
        rw [if_pos hv] at hfin'
        rw [Option.some.injEq] at hfin'
        obtain ⟨hhrp, hpayload⟩ := Prod.mk.inj hfin'
        subst hhrp
        refine ⟨hlen, hprint, hcase, raw, words, hsplit, ?_, ?_, ?_, hv,
          hpayload.symm⟩
        · intro hnil
          rw [hnil] at he
          simp at he
        · have hl' : ¬ raw.length < 6 := decide_eq_false_iff_not.mp hl
          omega
        · exact mapM_charToWord_eq_some_iff.mp hmapM
  · rintro ⟨hlen, hprint, hcase, raw, words, hsplit, hhrp, hrawlen, hraw,
      hverify, hpayload⟩
    rw [decodeChars_reduce hlen hprint hcase, hsplit]
    simp only [Option.bind_some]
    have hcond : (hrp.isEmpty || raw.length < 6) = false := by
      have e1 : hrp.isEmpty = false := by
        cases hrp with
        | nil => exact absurd rfl hhrp
        | cons c cs => rfl
      have e2 : (decide (raw.length < 6)) = false :=
        decide_eq_false_iff_not.mpr (by omega)
      simp [e1, e2]
    rw [if_neg (by simp [hcond])]
    rw [show raw.mapM charToWord = some words from
      mapM_charToWord_eq_some_iff.mpr hraw]
    simp only [Option.bind_some]
    rw [if_pos hverify, hpayload]

/-- Extract the `decodeChars` content of a successful `decode`. -/
theorem decode_eq_some_extract {v : Variant} {s : String}
    {hrp : String} {payload : List Word}
    (h : decode v s = some (hrp, payload)) :
    decodeChars v s.toList = some (hrp.toList, payload) := by
  have h2 : (decodeChars v s.toList).map
      (fun (h, d) => (String.ofList h, d)) = some (hrp, payload) := h
  rw [Option.map_eq_some_iff] at h2
  obtain ⟨⟨h', d'⟩, hdc, hmap⟩ := h2
  have hmap' : (String.ofList h', d') = (hrp, payload) := hmap
  rw [Prod.mk.injEq] at hmap'
  obtain ⟨hh, hd⟩ := hmap'
  have hheq : h' = hrp.toList := by
    have h3 := congrArg String.toList hh
    rwa [String.toList_ofList] at h3
  subst hheq
  subst hd
  exact hdc

/-- `charOfWord` is injective (kernel-checked over all word pairs). -/
theorem charOfWord_injective : Function.Injective charOfWord := by
  have h : ∀ a b : Word, charOfWord a = charOfWord b → a = b := by decide
  exact fun a b hab => h a b hab

/-- Hamming distance is preserved by an injective map. -/
theorem hammingDist_map_eq_of_injective {α β : Type} [DecidableEq α]
    [DecidableEq β] (f : α → β) (hf : Function.Injective f)
    (xs ys : List α) :
    hammingDist (xs.map f) (ys.map f) = hammingDist xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have ih' := ih ys
      rw [hammingDist_eq_countP, hammingDist_eq_countP] at ih'
      rw [hammingDist_eq_countP, hammingDist_eq_countP]
      rw [List.map_cons, List.map_cons, List.zip_cons_cons,
        List.zip_cons_cons, List.countP_cons, List.countP_cons, ih']
      by_cases hxy : x = y
      · subst hxy
        have h1 : (if (decide ((f x, f x).1 ≠ (f x, f x).2)) = true
            then (1 : Nat) else 0) = 0 := by simp
        have h2 : (if (decide ((x, x).1 ≠ (x, x).2)) = true
            then (1 : Nat) else 0) = 0 := by simp
        rw [h1, h2]
      · have hfx : f x ≠ f y := fun hcon => hxy (hf hcon)
        have h1 : (if (decide ((f x, f y).1 ≠ (f x, f y).2)) = true
            then (1 : Nat) else 0) = 1 := by simp [hfx]
        have h2 : (if (decide ((x, y).1 ≠ (x, y).2)) = true
            then (1 : Nat) else 0) = 1 := by simp [hxy]
        rw [h1, h2]

theorem hammingDist_self {α : Type} [DecidableEq α] (xs : List α) :
    hammingDist xs xs = 0 := by
  have hzip : ∀ (l : List α) (p : α × α), p ∈ l.zip l → p.1 = p.2 := by
    intro l
    induction l with
    | nil =>
      intro p hp
      simp at hp
    | cons x xs ih =>
      intro p hp
      rw [List.zip_cons_cons] at hp
      cases hp with
      | head => rfl
      | tail _ hp' => exact ih p hp'
  rw [hammingDist_eq_countP]
  refine List.countP_eq_zero.mpr (fun p hp => ?_)
  rw [decide_eq_true_eq]
  exact fun h => h (hzip xs p hp)

/-- Generic `hammingDist = 0 → equal` for Char lists. -/
theorem hammingDist_eq_zero_imp_char {xs ys : List Char}
    (h : hammingDist xs ys = 0) (hlen : xs.length = ys.length) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hxy : x = y := by
        by_cases hxy : x = y
        · exact hxy
        · have hge : 1 ≤ hammingDist (x :: xs) (y :: ys) := by
            simp [hammingDist, List.zip_cons_cons, hxy]
          omega
      subst hxy
      congr 1
      apply ih _ hlen
      have h2 : hammingDist (x :: xs) (x :: ys) = hammingDist xs ys := by
        simp [hammingDist, List.zip_cons_cons]
      omega

/-- Every character of a successfully decoded HRP is a lowered printable
    char, hence has `toNat ≤ 126`. -/
theorem hrp_chars_toNat_le {s : List Char} {hrp raw : List Char}
    (hprint : s.all printable = true)
    (hsplit : splitLast (s.map Char.toLower) = some (hrp, raw)) :
    ∀ c ∈ hrp, c.toNat ≤ 126 := by
  intro c hc
  obtain ⟨e, _⟩ := splitLast_eq_some_imp hsplit
  have hcmem : c ∈ s.map Char.toLower := by
    rw [e]
    exact List.mem_append_left _ hc
  obtain ⟨c', hc', hcc'⟩ := List.mem_map.mp hcmem
  have hpc' : printable c' = true := List.all_eq_true.mp hprint c' hc'
  have h := (lower_printable_local hpc').1
  simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← hcc']
  exact h.2

/-- Printable chars are below 128. -/
theorem toNat_lt_of_printable {s : List Char} (hprint : s.all printable = true) :
    ∀ c ∈ s, c.toNat < 128 := by
  intro c hc
  have h := List.all_eq_true.mp hprint c hc
  simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- The lowered separator pattern agrees with the original's. -/
theorem toLower_beq_one (c : Char) (hc : c.toNat < 128) :
    (c.toLower == '1') = (c == '1') := by
  have finite : ∀ n : Fin 128,
      ((Char.ofNat n.val).toLower == '1') = ((Char.ofNat n.val) == '1') := by
    decide
  simpa using finite ⟨c.toNat, hc⟩

theorem map_beq_one_map_toLower (s : List Char)
    (h : ∀ c ∈ s, c.toNat < 128) :
    (s.map Char.toLower).map (· == '1') = s.map (· == '1') := by
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp_apply]
  exact toLower_beq_one c (h c hc)

/-- Separator-preserving splits have equal component lengths. -/
theorem splitLast_same_len_of_sep_eq :
    ∀ (l₁ l₂ : List Char), l₁.length = l₂.length →
    l₁.map (· == '1') = l₂.map (· == '1') →
    ∀ (h₁ d₁ h₂ d₂ : List Char),
    splitLast l₁ = some (h₁, d₁) → splitLast l₂ = some (h₂, d₂) →
    h₁.length = h₂.length ∧ d₁.length = d₂.length := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ h₁ d₁ h₂ d₂ hs₁ _
    simp [splitLast] at hs₁
  | cons c₁ cs₁ ih =>
    intro l₂ hlen hsep h₁ d₁ h₂ d₂ hs₁ hs₂
    cases l₂ with
    | nil => simp at hlen
    | cons c₂ cs₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.cons.injEq] at hsep
      obtain ⟨hbeq, hsep'⟩ := hsep
      cases hcs₁ : splitLast cs₁ with
      | some p₁ =>
        obtain ⟨a₁, b₁⟩ := p₁
        rw [splitLast_cons_of_some hcs₁] at hs₁
        simp only [Option.some.injEq, Prod.mk.injEq] at hs₁
        obtain ⟨rfl, rfl⟩ := hs₁
        cases hcs₂ : splitLast cs₂ with
        | some p₂ =>
          obtain ⟨a₂, b₂⟩ := p₂
          rw [splitLast_cons_of_some hcs₂] at hs₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hs₂
          obtain ⟨rfl, rfl⟩ := hs₂
          obtain ⟨e1, e2⟩ := ih cs₂ hlen hsep' a₁ b₁ a₂ b₂ hcs₁ hcs₂
          exact ⟨by simp [e1], e2⟩
        | none =>
          exfalso
          rw [splitLast_cons_of_none hcs₂] at hs₂
          have h1mem : '1' ∈ cs₁ := mem_of_splitLast_eq_some hcs₁
          have h2not : '1' ∉ cs₂ := not_mem_of_splitLast_eq_none hcs₂
          have ht1 : true ∈ cs₁.map (· == '1') := by
            rw [List.mem_map]
            exact ⟨'1', h1mem, by decide⟩
          have ht2 : true ∉ cs₂.map (· == '1') := by
            rw [List.mem_map]
            rintro ⟨c, hc, hce⟩
            have hc1 : c = '1' := beq_iff_eq.mp hce
            exact h2not (hc1 ▸ hc)
          rw [hsep'] at ht1
          exact ht2 ht1
      | none =>
        rw [splitLast_cons_of_none hcs₁] at hs₁
        cases hcs₂ : splitLast cs₂ with
        | some p₂ =>
          exfalso
          obtain ⟨a₂, b₂⟩ := p₂
          rw [splitLast_cons_of_some hcs₂] at hs₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hs₂
          obtain ⟨rfl, rfl⟩ := hs₂
          have h1not : '1' ∉ cs₁ := not_mem_of_splitLast_eq_none hcs₁
          have h2mem : '1' ∈ cs₂ := mem_of_splitLast_eq_some hcs₂
          have ht1 : true ∈ cs₂.map (· == '1') := by
            rw [List.mem_map]
            exact ⟨'1', h2mem, by decide⟩
          have ht2 : true ∉ cs₁.map (· == '1') := by
            rw [List.mem_map]
            rintro ⟨c, hc, hce⟩
            have hc1 : c = '1' := beq_iff_eq.mp hce
            exact h1not (hc1 ▸ hc)
          rw [← hsep'] at ht1
          exact ht2 ht1
        | none =>
          rw [splitLast_cons_of_none hcs₂] at hs₂
          by_cases hc₁ : c₁ = '1'
          · rw [if_pos (by simp [hc₁])] at hs₁
            simp only [Option.some.injEq, Prod.mk.injEq] at hs₁
            obtain ⟨rfl, rfl⟩ := hs₁
            have hc₂ : c₂ = '1' := by
              have e : (c₂ == '1') = true := by
                rw [← hbeq, hc₁]
                decide
              exact beq_iff_eq.mp e
            rw [if_pos (by simp [hc₂])] at hs₂
            simp only [Option.some.injEq, Prod.mk.injEq] at hs₂
            obtain ⟨rfl, rfl⟩ := hs₂
            exact ⟨rfl, hlen⟩
          · rw [if_neg (by simp [hc₁])] at hs₁
            cases hs₁

/-! ## Form A: fixed expected HRP (dossier §1.3 B) -/

/-- Form A: with the HRP fixed, at most four substitutions in a valid
    string never produce another string decoding to the same HRP. -/
theorem decode_ne_same_hrp_of_substitutions_le_four
    (variant : Variant) (s₁ s₂ : String) (hrp : String)
    (payload₁ payload₂ : List Word)
    (hvalid : decode variant s₁ = some (hrp, payload₁))
    (hlen : s₁.toList.length = s₂.toList.length)
    (hne : s₁.toList.map Char.toLower ≠ s₂.toList.map Char.toLower)
    (hdist : hammingDist s₁.toList s₂.toList ≤ 4) :
    decode variant s₂ ≠ some (hrp, payload₂) := by
  intro hbad
  have hdc₁ := decode_eq_some_extract hvalid
  have hdc₂ := decode_eq_some_extract hbad
  rw [decodeChars_eq_some_iff] at hdc₁ hdc₂
  obtain ⟨hlen₁, -, -, raw₁, words₁, hsplit₁, hhrp₁, -, hraw₁, hverify₁, -⟩ :=
    hdc₁
  obtain ⟨-, -, -, raw₂, words₂, hsplit₂, -, -, hraw₂, hverify₂, -⟩ := hdc₂
  obtain ⟨hL₁, -⟩ := splitLast_eq_some_imp hsplit₁
  obtain ⟨hL₂, -⟩ := splitLast_eq_some_imp hsplit₂
  have hraw_len : raw₁.length = raw₂.length := by
    have e1 : (s₁.toList.map Char.toLower).length =
        hrp.toList.length + 1 + raw₁.length := by
      rw [hL₁, List.length_append, List.length_cons]; omega
    have e2 : (s₂.toList.map Char.toLower).length =
        hrp.toList.length + 1 + raw₂.length := by
      rw [hL₂, List.length_append, List.length_cons]; omega
    simp only [List.length_map] at e1 e2
    omega
  have hwords_len : words₁.length = words₂.length := by
    have w1 : words₁.length = raw₁.length := by
      rw [hraw₁]; simp [List.length_map]
    have w2 : words₂.length = raw₂.length := by
      rw [hraw₂]; simp [List.length_map]
    omega
  have hwords_bound : words₁.length ≤ 89 := by
    have w1 : words₁.length = raw₁.length := by
      rw [hraw₁]; simp [List.length_map]
    have e1 : (s₁.toList.map Char.toLower).length =
        hrp.toList.length + 1 + raw₁.length := by
      rw [hL₁, List.length_append, List.length_cons]; omega
    simp only [List.length_map] at e1
    have hhrp_len : 1 ≤ hrp.toList.length := by
      cases hh : hrp.toList with
      | nil => rw [hh] at hhrp₁; exact absurd rfl hhrp₁
      | cons c cs => rw [List.length_cons]; omega
    omega
  have hdist_words : hammingDist words₁ words₂ ≤ 4 := by
    have e1 : hammingDist (s₁.toList.map Char.toLower)
        (s₂.toList.map Char.toLower) ≤ 4 := by
      have h1 := hammingDist_map_le Char.toLower s₁.toList s₂.toList
      omega
    rw [hL₁, hL₂, hammingDist_append _ _ _ _
      (by simp : hrp.toList.length = hrp.toList.length),
      hammingDist_self, Nat.zero_add] at e1
    have e2 : hammingDist ('1' :: raw₁) ('1' :: raw₂) =
        hammingDist raw₁ raw₂ := by
      rw [show ('1' :: raw₁) = ['1'] ++ raw₁ from rfl,
        show ('1' :: raw₂) = ['1'] ++ raw₂ from rfl,
        hammingDist_append _ _ _ _ (by simp), hammingDist_self,
        Nat.zero_add]
    rw [e2, hraw₁, hraw₂,
      hammingDist_map_eq_of_injective charOfWord charOfWord_injective] at e1
    exact e1
  by_cases hww : words₁ = words₂
  · apply hne
    rw [hL₁, hL₂, hraw₁, hraw₂, hww]
  · have hcontra := verifyChecksum_false_of_data_substitutions_le_four
      variant hrp.toList words₁ words₂ hwords_len hwords_bound hww
      hdist_words hverify₁
    rw [hverify₂] at hcontra
    exact Bool.noConfusion hcontra

/-- `Char.toLower` is idempotent: on ASCII by a finite check, and
    outside ASCII it is the identity (only `A`–`Z` are affected). -/
theorem toLower_toLower (c : Char) : (c.toLower).toLower = c.toLower := by
  by_cases hc : c.toNat < 128
  · have finite : ∀ n : Fin 128,
        ((Char.ofNat n.val).toLower).toLower = (Char.ofNat n.val).toLower := by
      decide
    simpa using finite ⟨c.toNat, hc⟩
  · have hup : c.isUpper = false := by
      by_cases hb : c.isUpper = true
      · exfalso
        have h3 : c.val ≥ ('A' : Char).val ∧ c.val ≤ ('Z' : Char).val := by
          simpa only [Char.isUpper, decide_eq_true_eq] using hb
        have hle : c.val.toNat ≤ 90 := by
          have e := UInt32.le_iff_toNat_le.mp h3.2
          have hZ : (('Z' : Char).val).toNat = 90 := by decide
          rwa [hZ] at e
        have htn : c.toNat = c.val.toNat := rfl
        omega
      · cases hb2 : c.isUpper <;> simp_all
    have e : c.toLower = c := toLower_eq_self_of_not_upper_local hup
    rw [e, e]

/-- The encoder's output is already lowercase. -/
theorem encodeChars_toLower (variant : Variant) (hrp : List Char)
    (data : List Word) :
    (encodeChars variant hrp data).map Char.toLower =
      encodeChars variant hrp data := by
  have hform : encodeChars variant hrp data =
      hrp.map Char.toLower ++ '1' ::
        (data ++ createChecksum variant (hrp.map Char.toLower) data).map
          charOfWord := rfl
  rw [hform, List.map_append, List.map_cons]
  have h1 : (hrp.map Char.toLower).map Char.toLower =
      hrp.map Char.toLower := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact toLower_toLower c
  have h2 : ((data ++ createChecksum variant (hrp.map Char.toLower) data).map
        charOfWord).map Char.toLower =
      (data ++ createChecksum variant (hrp.map Char.toLower) data).map
        charOfWord := by
    rw [List.map_map]
    apply List.map_congr_left
    intro w _
    have hfin : ∀ x : Word, (charOfWord x).toLower = charOfWord x := by
      decide
    exact hfin w
  have h3 : ('1' : Char).toLower = '1' := by decide
  rw [h1, h2, h3]

/-- Form A, `encode` specialization (dossier §1.3 B). -/
theorem decode_encode_ne_same_hrp_of_substitutions_le_four
    (variant : Variant) (hrp : String) (data payload₂ : List Word)
    (s₂ : String)
    (hvalid : ValidInput hrp data)
    (hlen : (encode variant hrp data).toList.length = s₂.toList.length)
    (hne : (encode variant hrp data).toList ≠ s₂.toList.map Char.toLower)
    (hdist : hammingDist (encode variant hrp data).toList s₂.toList ≤ 4) :
    decode variant s₂ ≠ some (hrp, payload₂) := by
  have h1 : decode variant (encode variant hrp data) = some (hrp, data) :=
    decode_encode variant hrp data hvalid
  have hne' : (encode variant hrp data).toList.map Char.toLower ≠
      s₂.toList.map Char.toLower := by
    have e : (encode variant hrp data).toList.map Char.toLower =
        (encode variant hrp data).toList := by
      have henc : encode variant hrp data =
          String.ofList (encodeChars variant hrp.toList data) := rfl
      rw [henc, String.toList_ofList]
      exact encodeChars_toLower variant hrp.toList data
    rw [e]
    exact hne
  exact decode_ne_same_hrp_of_substitutions_le_four variant
    (encode variant hrp data) s₂ hrp data payload₂ h1 hlen hne' hdist

/-! ## Form B: separator-preserving + high-bit-preserving (dossier §1.3 B)

The core lemma is parameterized by how the high-bit agreement is derived,
so the plain Footnote-4 form and the alphabetic-HRP form share it. -/

/-- Core of Form B: given both decodings, the joint checksum theorem
    applies once the HRP high bits agree. -/
theorem decode_eq_none_core
    (variant : Variant) (s₁ s₂ : String) (hrp₁ : String) (payload₁ : List Word)
    (hvalid : decode variant s₁ = some (hrp₁, payload₁))
    (hlen : s₁.toList.length = s₂.toList.length)
    (hne : s₁.toList.map Char.toLower ≠ s₂.toList.map Char.toLower)
    (hsep : s₁.toList.map (· == '1') = s₂.toList.map (· == '1'))
    (hdist : hammingDist s₁.toList s₂.toList ≤ 4)
    (hhi_gen : ∀ (hrp₂L raw₂ : List Char) (words₂ : List Word),
      decodeChars variant s₂.toList =
        some (hrp₂L, words₂.take (words₂.length - 6)) →
      splitLast (s₂.toList.map Char.toLower) = some (hrp₂L, raw₂) →
      hrp₁.toList.map (fun c => c.toNat >>> 5) =
        hrp₂L.map (fun c => c.toNat >>> 5)) :
    decode variant s₂ = none := by
  cases h₂ : decode variant s₂ with
  | none => rfl
  | some p =>
    obtain ⟨hrp₂, payload₂⟩ := p
    exfalso
    have hdc₁raw := decode_eq_some_extract hvalid
    have hdc₂raw := decode_eq_some_extract h₂
    have hdc₁ := hdc₁raw
    have hdc₂ := hdc₂raw
    rw [decodeChars_eq_some_iff] at hdc₁ hdc₂
    obtain ⟨hlen₁, hprint₁, -, raw₁, words₁, hsplit₁, hhrp₁, -, hraw₁,
      hverify₁, -⟩ := hdc₁
    obtain ⟨-, hprint₂, -, raw₂, words₂, hsplit₂, -, -, hraw₂, hverify₂,
      hpayload₂⟩ := hdc₂
    obtain ⟨hL₁, -⟩ := splitLast_eq_some_imp hsplit₁
    obtain ⟨hL₂, -⟩ := splitLast_eq_some_imp hsplit₂
    have hsepL : (s₁.toList.map Char.toLower).map (· == '1') =
        (s₂.toList.map Char.toLower).map (· == '1') := by
      rw [map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₁),
        map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₂)]
      exact hsep
    have hlenL : (s₁.toList.map Char.toLower).length =
        (s₂.toList.map Char.toLower).length := by
      simp only [List.length_map, hlen]
    obtain ⟨hhrp_len, hraw_len⟩ := splitLast_same_len_of_sep_eq _ _ hlenL
      hsepL _ _ _ _ hsplit₁ hsplit₂
    have hascii₁ : ∀ c ∈ hrp₁.toList, c.toNat ≤ 126 :=
      hrp_chars_toNat_le (s := s₁.toList) hprint₁ hsplit₁
    have hascii₂ : ∀ c ∈ hrp₂.toList, c.toNat ≤ 126 :=
      hrp_chars_toNat_le (s := s₂.toList) hprint₂ hsplit₂
    have hhiW : hrp₁.toList.map (fun c => c.toNat >>> 5) =
        hrp₂.toList.map (fun c => c.toNat >>> 5) := by
      rw [hpayload₂] at hdc₂raw
      exact hhi_gen hrp₂.toList raw₂ words₂ hdc₂raw hsplit₂
    have hwords_len : words₁.length = words₂.length := by
      have w1 : words₁.length = raw₁.length := by
        rw [hraw₁]; simp [List.length_map]
      have w2 : words₂.length = raw₂.length := by
        rw [hraw₂]; simp [List.length_map]
      omega
    have hbound : hrp₁.toList.length + words₁.length ≤ 89 := by
      have w1 : words₁.length = raw₁.length := by
        rw [hraw₁]; simp [List.length_map]
      have e1 : (s₁.toList.map Char.toLower).length =
          hrp₁.toList.length + 1 + raw₁.length := by
        rw [hL₁, List.length_append, List.length_cons]; omega
      simp only [List.length_map] at e1
      omega
    have hdist_total : hammingDist hrp₁.toList hrp₂.toList +
        hammingDist words₁ words₂ ≤ 4 := by
      have e1 : hammingDist (s₁.toList.map Char.toLower)
          (s₂.toList.map Char.toLower) ≤ 4 := by
        have h1 := hammingDist_map_le Char.toLower s₁.toList s₂.toList
        omega
      rw [hL₁, hL₂, hammingDist_append _ _ _ _ hhrp_len] at e1
      have e2 : hammingDist ('1' :: raw₁) ('1' :: raw₂) =
          hammingDist raw₁ raw₂ := by
        rw [show ('1' :: raw₁) = ['1'] ++ raw₁ from rfl,
          show ('1' :: raw₂) = ['1'] ++ raw₂ from rfl,
          hammingDist_append _ _ _ _ (by simp), hammingDist_self,
          Nat.zero_add]
      have e3 : hammingDist raw₁ raw₂ = hammingDist words₁ words₂ := by
        rw [hraw₁, hraw₂,
          hammingDist_map_eq_of_injective charOfWord charOfWord_injective]
      omega
    have hne' : hrp₁.toList ≠ hrp₂.toList ∨ words₁ ≠ words₂ := by
      apply Classical.byContradiction
      intro hcon
      have e1 : hrp₁.toList = hrp₂.toList := by
        apply Classical.byContradiction
        intro hc
        exact hcon (Or.inl hc)
      have e2 : words₁ = words₂ := by
        apply Classical.byContradiction
        intro hc
        exact hcon (Or.inr hc)
      apply hne
      rw [hL₁, hL₂, e1, hraw₁, hraw₂, e2]
    have hcontra := verifyChecksum_false_of_substitutions_le_four variant
      hrp₁.toList hrp₂.toList words₁ words₂ hhrp_len hwords_len hbound
      hascii₁ hascii₂ hhiW hne' hdist_total hverify₁
    rw [hverify₂] at hcontra
    exact Bool.noConfusion hcontra

/-- Taking an appended list at the length of its first component. -/
theorem take_append_length {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).take l₁.length = l₁ :=
  List.take_left

/-- High-bit agreement transfers from the string prefixes to the split
    HRPs. -/
theorem hi_map_eq_of_take_eq {s₁ s₂ : List Char} {n : Nat}
    {hrp₁L raw₁ hrp₂L raw₂ : List Char}
    (hsplit₁ : splitLast (s₁.map Char.toLower) = some (hrp₁L, raw₁))
    (hsplit₂ : splitLast (s₂.map Char.toLower) = some (hrp₂L, raw₂))
    (hlen : hrp₁L.length = hrp₂L.length)
    (hn : n = hrp₁L.length)
    (hhi : (s₁.take n).map (fun c => c.toLower.toNat >>> 5) =
      (s₂.take n).map (fun c => c.toLower.toNat >>> 5)) :
    hrp₁L.map (fun c => c.toNat >>> 5) =
      hrp₂L.map (fun c => c.toNat >>> 5) := by
  obtain ⟨hL₁, -⟩ := splitLast_eq_some_imp hsplit₁
  obtain ⟨hL₂, -⟩ := splitLast_eq_some_imp hsplit₂
  have t1 : hrp₁L = (s₁.take n).map Char.toLower := by
    have e : (s₁.map Char.toLower).take n = hrp₁L := by
      rw [hL₁, hn]
      exact take_append_length _ _
    rw [← List.map_take] at e
    exact e.symm
  have t2 : hrp₂L = (s₂.take n).map Char.toLower := by
    have e : (s₂.map Char.toLower).take n = hrp₂L := by
      rw [hL₂, hn, hlen]
      exact take_append_length _ _
    rw [← List.map_take] at e
    exact e.symm
  rw [t1, t2, List.map_map, List.map_map]
  exact hhi

/-- Form B (dossier §1.3 B): separator-preserving + Footnote-4
    high-bit-preserving substitutions never produce a decoding string. -/
theorem decode_eq_none_of_substitutions_le_four
    (variant : Variant) (s₁ s₂ : String) (hrp₁ : String) (payload₁ : List Word)
    (hvalid : decode variant s₁ = some (hrp₁, payload₁))
    (hlen : s₁.toList.length = s₂.toList.length)
    (hne : s₁.toList.map Char.toLower ≠ s₂.toList.map Char.toLower)
    (hsep : s₁.toList.map (· == '1') = s₂.toList.map (· == '1'))
    (hhi : (s₁.toList.take hrp₁.toList.length).map
        (fun c => c.toLower.toNat >>> 5) =
      (s₂.toList.take hrp₁.toList.length).map
        (fun c => c.toLower.toNat >>> 5))
    (hdist : hammingDist s₁.toList s₂.toList ≤ 4) :
    decode variant s₂ = none := by
  have hdc₁raw := decode_eq_some_extract hvalid
  have hdc₁ := hdc₁raw
  rw [decodeChars_eq_some_iff] at hdc₁
  obtain ⟨-, hprint₁, -, raw₁, -, hsplit₁, -, -, -, -, -⟩ := hdc₁
  apply decode_eq_none_core variant s₁ s₂ hrp₁ payload₁ hvalid hlen hne
    hsep hdist
  intro hrp₂L raw₂ words₂ hdc₂raw hsplit₂
  have hdc₂ := hdc₂raw
  rw [decodeChars_eq_some_iff] at hdc₂
  obtain ⟨-, hprint₂, -, raw₂', -, hsplit₂', -, -, -, -, -⟩ := hdc₂
  have hsepL : (s₁.toList.map Char.toLower).map (· == '1') =
      (s₂.toList.map Char.toLower).map (· == '1') := by
    rw [map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₁),
      map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₂)]
    exact hsep
  have hlenL : (s₁.toList.map Char.toLower).length =
      (s₂.toList.map Char.toLower).length := by
    simp only [List.length_map, hlen]
  obtain ⟨hhrp_len, -⟩ := splitLast_same_len_of_sep_eq _ _ hlenL hsepL _ _
    _ _ hsplit₁ hsplit₂
  exact hi_map_eq_of_take_eq hsplit₁ hsplit₂ hhrp_len rfl hhi

/-- In the alphabetic region, lowered high bits are constantly `3`. -/
theorem map_toLower_hi_of_all_alpha {l : List Char}
    (halpha : l.all Char.isAlpha = true)
    (hprint : ∀ c ∈ l, printable c = true) :
    l.map (fun c => c.toLower.toNat >>> 5) = List.replicate l.length 3 := by
  have pt : ∀ c ∈ l, (fun c => c.toLower.toNat >>> 5) c = 3 := by
    intro c hc
    have ha : c.isAlpha = true := List.all_eq_true.mp halpha c hc
    have hp := hprint c hc
    have hlt : c.toNat < 128 := by
      simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at hp
      omega
    have finite : ∀ n : Fin 128, (Char.ofNat n.val).isAlpha = true →
        printable (Char.ofNat n.val) = true →
        (Char.ofNat n.val).toLower.toNat >>> 5 = 3 := by decide
    have h2 : (Char.ofNat c.toNat).isAlpha = true ∧
        printable (Char.ofNat c.toNat) = true := by
      rw [Char.ofNat_toNat]
      exact ⟨ha, hp⟩
    have h3 := finite ⟨c.toNat, hlt⟩ h2.1 h2.2
    rwa [Char.ofNat_toNat] at h3
  have e : l.map (fun c => c.toLower.toNat >>> 5) =
      l.map (Function.const Char 3) := List.map_congr_left pt
  rw [e, List.map_const]

/-- Alphabetic-HRP Form B (dossier §1.3 B): Footnote 4's high-bit
    condition is automatic for alphabetic HRPs. -/
theorem decode_eq_none_of_alpha_hrp_substitutions_le_four
    (variant : Variant) (s₁ s₂ : String) (hrp₁ : String) (payload₁ : List Word)
    (hvalid : decode variant s₁ = some (hrp₁, payload₁))
    (hlen : s₁.toList.length = s₂.toList.length)
    (hne : s₁.toList.map Char.toLower ≠ s₂.toList.map Char.toLower)
    (hsep : s₁.toList.map (· == '1') = s₂.toList.map (· == '1'))
    (halpha₁ : (s₁.toList.take hrp₁.toList.length).all Char.isAlpha = true)
    (halpha₂ : (s₂.toList.take hrp₁.toList.length).all Char.isAlpha = true)
    (hdist : hammingDist s₁.toList s₂.toList ≤ 4) :
    decode variant s₂ = none := by
  have hdc₁raw := decode_eq_some_extract hvalid
  have hdc₁ := hdc₁raw
  rw [decodeChars_eq_some_iff] at hdc₁
  obtain ⟨hlen₁, hprint₁, -, raw₁, -, hsplit₁, -, -, -, -, -⟩ := hdc₁
  obtain ⟨hL₁, -⟩ := splitLast_eq_some_imp hsplit₁
  have hn1 : hrp₁.toList.length ≤ s₁.toList.length := by
    have e : (s₁.toList.map Char.toLower).length =
        hrp₁.toList.length + 1 + raw₁.length := by
      rw [hL₁, List.length_append, List.length_cons]; omega
    simp only [List.length_map] at e
    omega
  apply decode_eq_none_core variant s₁ s₂ hrp₁ payload₁ hvalid hlen hne
    hsep hdist
  intro hrp₂L raw₂ words₂ hdc₂raw hsplit₂
  have hdc₂ := hdc₂raw
  rw [decodeChars_eq_some_iff] at hdc₂
  obtain ⟨-, hprint₂, -, raw₂', -, hsplit₂', -, -, -, -, -⟩ := hdc₂
  have hsepL : (s₁.toList.map Char.toLower).map (· == '1') =
      (s₂.toList.map Char.toLower).map (· == '1') := by
    rw [map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₁),
      map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₂)]
    exact hsep
  have hlenL : (s₁.toList.map Char.toLower).length =
      (s₂.toList.map Char.toLower).length := by
    simp only [List.length_map, hlen]
  obtain ⟨hhrp_len, -⟩ := splitLast_same_len_of_sep_eq _ _ hlenL hsepL _ _
    _ _ hsplit₁ hsplit₂
  -- both hi take-maps are constantly 3
  have pr1 : ∀ c ∈ s₁.toList.take hrp₁.toList.length, printable c = true :=
    fun c hc => List.all_eq_true.mp hprint₁ c (List.mem_of_mem_take hc)
  have pr2 : ∀ c ∈ s₂.toList.take hrp₁.toList.length, printable c = true :=
    fun c hc => List.all_eq_true.mp hprint₂ c (List.mem_of_mem_take hc)
  have m1 := map_toLower_hi_of_all_alpha halpha₁ pr1
  have m2 := map_toLower_hi_of_all_alpha halpha₂ pr2
  have len1 : (s₁.toList.take hrp₁.toList.length).length =
      hrp₁.toList.length := by
    rw [List.length_take, Nat.min_eq_left hn1]
  have len2 : (s₂.toList.take hrp₁.toList.length).length =
      hrp₁.toList.length := by
    rw [List.length_take, Nat.min_eq_left]
    omega
  rw [len1] at m1
  rw [len2] at m2
  have hhieq : (s₁.toList.take hrp₁.toList.length).map
        (fun c => c.toLower.toNat >>> 5) =
      (s₂.toList.take hrp₁.toList.length).map
        (fun c => c.toLower.toNat >>> 5) := m1.trans m2.symm
  exact hi_map_eq_of_take_eq hsplit₁ hsplit₂ hhrp_len rfl hhieq

/-- Append injectivity at a known length (generic form). -/
theorem append_inj_of_len' {α : Type} {a b c d : List α}
    (hlen : a.length = b.length) (h : a ++ c = b ++ d) :
    a = b ∧ c = d := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, h⟩
    | cons x xs => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxy, hrest⟩ := h
      obtain ⟨e1, e2⟩ := ih hlen hrest
      exact ⟨by rw [hxy, e1], e2⟩

/-- Length of an HRP expansion. -/
theorem length_hrpExpand' (hrp : List Char) :
    (hrpExpand hrp).length = 2 * hrp.length + 1 := by
  simp only [hrpExpand, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  omega

/-- Unconditional single-substitution guarantee (dossier §1.3 B): one
    substitution is always detected, at any HRP, via the expanded
    codeword at length `≤ 173` and weight `≤ 3`. -/
theorem decode_eq_none_of_single_substitution
    (variant : Variant) (s₁ s₂ : String) (hrp₁ : String) (payload₁ : List Word)
    (hvalid : decode variant s₁ = some (hrp₁, payload₁))
    (hlen : s₁.toList.length = s₂.toList.length)
    (hne : s₁.toList.map Char.toLower ≠ s₂.toList.map Char.toLower)
    (hsep : s₁.toList.map (· == '1') = s₂.toList.map (· == '1'))
    (hdist : hammingDist s₁.toList s₂.toList ≤ 1) :
    decode variant s₂ = none := by
  cases h₂ : decode variant s₂ with
  | none => rfl
  | some p =>
    obtain ⟨hrp₂, payload₂⟩ := p
    exfalso
    have hdc₁ := decode_eq_some_extract hvalid
    have hdc₂ := decode_eq_some_extract h₂
    rw [decodeChars_eq_some_iff] at hdc₁ hdc₂
    obtain ⟨hlen₁, hprint₁, -, raw₁, words₁, hsplit₁, hhrp₁, hrawlen₁,
      hraw₁, hverify₁, -⟩ := hdc₁
    obtain ⟨-, hprint₂, -, raw₂, words₂, hsplit₂, -, -, hraw₂, hverify₂,
      -⟩ := hdc₂
    obtain ⟨hL₁, -⟩ := splitLast_eq_some_imp hsplit₁
    obtain ⟨hL₂, -⟩ := splitLast_eq_some_imp hsplit₂
    have hsepL : (s₁.toList.map Char.toLower).map (· == '1') =
        (s₂.toList.map Char.toLower).map (· == '1') := by
      rw [map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₁),
        map_beq_one_map_toLower _ (toNat_lt_of_printable hprint₂)]
      exact hsep
    have hlenL : (s₁.toList.map Char.toLower).length =
        (s₂.toList.map Char.toLower).length := by
      simp only [List.length_map, hlen]
    obtain ⟨hhrp_len, hraw_len⟩ := splitLast_same_len_of_sep_eq _ _ hlenL
      hsepL _ _ _ _ hsplit₁ hsplit₂
    have hascii₁ : ∀ c ∈ hrp₁.toList, c.toNat ≤ 126 :=
      hrp_chars_toNat_le (s := s₁.toList) hprint₁ hsplit₁
    have hascii₂ : ∀ c ∈ hrp₂.toList, c.toNat ≤ 126 :=
      hrp_chars_toNat_le (s := s₂.toList) hprint₂ hsplit₂
    have hwords_len : words₁.length = words₂.length := by
      have w1 : words₁.length = raw₁.length := by
        rw [hraw₁]; simp [List.length_map]
      have w2 : words₂.length = raw₂.length := by
        rw [hraw₂]; simp [List.length_map]
      omega
    -- distance split
    have hdistL : hammingDist (s₁.toList.map Char.toLower)
        (s₂.toList.map Char.toLower) ≤ 1 := by
      have h1 := hammingDist_map_le Char.toLower s₁.toList s₂.toList
      omega
    rw [hL₁, hL₂, hammingDist_append _ _ _ _ hhrp_len] at hdistL
    have e2 : hammingDist ('1' :: raw₁) ('1' :: raw₂) =
        hammingDist raw₁ raw₂ := by
      rw [show ('1' :: raw₁) = ['1'] ++ raw₁ from rfl,
        show ('1' :: raw₂) = ['1'] ++ raw₂ from rfl,
        hammingDist_append _ _ _ _ (by simp), hammingDist_self,
        Nat.zero_add]
    rw [e2] at hdistL
    have hword_dist : hammingDist words₁ words₂ = hammingDist raw₁ raw₂ := by
      rw [hraw₁, hraw₂,
        hammingDist_map_eq_of_injective charOfWord charOfWord_injective]
    -- case (0,0): the lowered lists agree
    by_cases hcase : hammingDist hrp₁.toList hrp₂.toList = 0 ∧
        hammingDist words₁ words₂ = 0
    · obtain ⟨hz1, hz2⟩ := hcase
      have e1 : hrp₁.toList = hrp₂.toList :=
        hammingDist_eq_zero_imp_char hz1 hhrp_len
      have e2' : words₁ = words₂ :=
        hammingDist_eq_zero_imp hz2 hwords_len
      apply hne
      rw [hL₁, hL₂, e1, hraw₁, hraw₂, e2']
    · -- expanded codewords
      have hEne : hrpExpand hrp₁.toList ++ words₁ ≠
          hrpExpand hrp₂.toList ++ words₂ := by
        intro hE
        have hlenE1 : (hrpExpand hrp₁.toList).length =
            (hrpExpand hrp₂.toList).length := by
          rw [length_hrpExpand', length_hrpExpand', hhrp_len]
        obtain ⟨hExp, hWords⟩ := append_inj_of_len' hlenE1 hE
        have hhi : hrp₁.toList.map (fun c => c.toNat >>> 5) =
            hrp₂.toList.map (fun c => c.toNat >>> 5) := by
          have hT := congrArg (List.map BitVec.toNat) hExp
          rw [hrpExpand_toNat _ hascii₁, hrpExpand_toNat _ hascii₂] at hT
          have hl1 : (hrp₁.toList.map (fun c => c.toNat >>> 5)).length =
              hrp₁.toList.length := by simp [List.length_map]
          have hl2 : (hrp₂.toList.map (fun c => c.toNat >>> 5)).length =
              hrp₂.toList.length := by simp [List.length_map]
          obtain ⟨e0, -⟩ := append_inj_of_len'
            (a := (hrp₁.toList.map (fun c => c.toNat >>> 5)) ++ [0])
            (b := (hrp₂.toList.map (fun c => c.toNat >>> 5)) ++ [0])
            (c := hrp₁.toList.map (fun c => c.toNat &&& 31))
            (d := hrp₂.toList.map (fun c => c.toNat &&& 31))
            (by simp only [List.length_append, List.length_cons,
              List.length_nil, hl1, hl2, hhrp_len]) hT
          obtain ⟨e, -⟩ := append_inj_of_len'
            (a := hrp₁.toList.map (fun c => c.toNat >>> 5))
            (b := hrp₂.toList.map (fun c => c.toNat >>> 5))
            (c := [0]) (d := [0])
            (by simp only [hl1, hl2, hhrp_len]) e0
          exact e
        have hlo : hrp₁.toList.map
            (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) =
            hrp₂.toList.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) := by
          -- from hExp: hrpExpand = hi ++ [0] ++ lo; strip hi ++ [0]
          have e1 : (hrpExpand hrp₁.toList) =
              (hrp₁.toList.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5))) ++
              [0] ++ hrp₁.toList.map
                (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) := rfl
          have e2' : (hrpExpand hrp₂.toList) =
              (hrp₂.toList.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5))) ++
              [0] ++ hrp₂.toList.map
                (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) := rfl
          rw [e1] at hExp
          rw [e2'] at hExp
          obtain ⟨-, hrest⟩ := append_inj_of_len'
            (by simp [List.length_map, hhrp_len] :
              ((hrp₁.toList.map
                  (fun c : Char => BitVec.ofNat 5 (c.toNat >>> 5))) ++
                [0]).length =
              ((hrp₂.toList.map
                  (fun c : Char => BitVec.ofNat 5 (c.toNat >>> 5))) ++
                [0]).length) hExp
          exact hrest
        have hhrp_eq : hrp₁.toList = hrp₂.toList :=
          char_list_eq_of_hi_lo _ _ hhrp_len hhi hlo hascii₁ hascii₂
        -- now either the HRP distance or the word distance is positive
        by_cases hz1 : hammingDist hrp₁.toList hrp₂.toList = 0
        · have hz2 : hammingDist words₁ words₂ ≠ 0 := by
            intro hz
            exact hcase ⟨hz1, hz⟩
          have : words₁ ≠ words₂ := by
            intro hEq
            apply hz2
            rw [hEq, hammingDist_self]
          exact this hWords
        · have : hrp₁.toList ≠ hrp₂.toList := by
            intro hEq
            apply hz1
            rw [hEq, hammingDist_self]
          exact this hhrp_eq
      -- polymod contradiction at weight ≤ 3, length ≤ 173
      have hlenE : (hrpExpand hrp₁.toList ++ words₁).length =
          (hrpExpand hrp₂.toList ++ words₂).length := by
        simp only [List.length_append, length_hrpExpand', hhrp_len,
          hwords_len]
      have hlenE_le : (hrpExpand hrp₁.toList ++ words₁).length ≤ 173 := by
        have e1 : (s₁.toList.map Char.toLower).length =
            hrp₁.toList.length + 1 + raw₁.length := by
          rw [hL₁, List.length_append, List.length_cons]; omega
        simp only [List.length_map] at e1
        have w1 : words₁.length = raw₁.length := by
          rw [hraw₁]; simp [List.length_map]
        simp only [List.length_append, length_hrpExpand']
        omega
      have hdistE : hammingDist (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂) ≤ 3 := by
        have step1 : hammingDist (hrpExpand hrp₁.toList ++ words₁)
            (hrpExpand hrp₂.toList ++ words₂) =
            hammingDist (hrpExpand hrp₁.toList) (hrpExpand hrp₂.toList) +
              hammingDist words₁ words₂ := by
          apply hammingDist_append
          rw [length_hrpExpand', length_hrpExpand', hhrp_len]
        have step2 : hammingDist (hrpExpand hrp₁.toList)
            (hrpExpand hrp₂.toList) ≤
            2 * hammingDist hrp₁.toList hrp₂.toList := by
          have e1 : hrpExpand hrp₁.toList =
              ((hrp₁.toList.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5))) ++
                [0]) ++ hrp₁.toList.map
                  (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) := by
            simp [hrpExpand, List.append_assoc]
          have e2' : hrpExpand hrp₂.toList =
              ((hrp₂.toList.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5))) ++
                [0]) ++ hrp₂.toList.map
                  (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) := by
            simp [hrpExpand, List.append_assoc]
          rw [e1, e2', hammingDist_append _ _ _ _
            (by simp [List.length_append, List.length_map, hhrp_len]),
            hammingDist_append _ _ _ _
            (by simp [List.length_map, hhrp_len]), hammingDist_self,
            Nat.add_zero]
          have m1 := hammingDist_map_le
            (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) hrp₁.toList hrp₂.toList
          have m2 := hammingDist_map_le
            (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) hrp₁.toList hrp₂.toList
          omega
        omega
      have hweight : hammingWeight (List.zipWith (· ^^^ ·)
          (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂)) ≤ 3 := by
        rw [← hammingDist_eq_hammingWeight_xor _ _ hlenE]
        exact hdistE
      have hpos : 0 < hammingWeight (List.zipWith (· ^^^ ·)
          (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂)) := by
        rw [← hammingDist_eq_hammingWeight_xor _ _ hlenE]
        apply Classical.byContradiction
        intro hcon
        have hz : hammingDist (hrpExpand hrp₁.toList ++ words₁)
            (hrpExpand hrp₂.toList ++ words₂) = 0 := by omega
        exact hEne (hammingDist_eq_zero_imp hz hlenE)
      have hfold : (List.zipWith (· ^^^ ·)
          (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂)).foldl polymodStep 0 = 0 := by
        have hZ : (List.zipWith (· ^^^ ·)
            (hrpExpand hrp₁.toList ++ words₁)
            (hrpExpand hrp₂.toList ++ words₂)).foldl polymodStep 0 =
            polymod (hrpExpand hrp₁.toList ++ words₁) ^^^
              polymod (hrpExpand hrp₂.toList ++ words₂) :=
          foldl_polymodStep_xor _ _ 1 1 hlenE
        rw [hZ]
        have hp1 : polymod (hrpExpand hrp₁.toList ++ words₁) =
            variant.constant := by
          have hv := hverify₁
          simp only [verifyChecksum, beq_iff_eq] at hv
          exact hv
        have hp2 : polymod (hrpExpand hrp₂.toList ++ words₂) =
            variant.constant := by
          have hv := hverify₂
          simp only [verifyChecksum, beq_iff_eq] at hv
          exact hv
        rw [hp1, hp2]
        exact BitVec.xor_self
      have hlenZ : (List.zipWith (· ^^^ ·)
          (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂)).length ≤ 173 := by
        rw [List.length_zipWith,
          Nat.min_eq_left (by omega)]
        exact hlenE_le
      have hne0 := foldl_polymodStep_zero_ne_zero_of_weight_le_three
        (List.zipWith (· ^^^ ·) (hrpExpand hrp₁.toList ++ words₁)
          (hrpExpand hrp₂.toList ++ words₂)) hlenZ hpos hweight
      exact hne0 hfold

/-! ## BIP-350 insertion analysis (dossier §1.3 C, L5.6)

Evaluation at the generator root `r = γ^172` intertwines the checksum
transition: `stateEval (polymodStep s v) = r * stateEval s + v`.  A run
of `k` inserted zero words multiplies the evaluated state by `r^k`;
since `r` has order `1023`, Bech32m insertion is detected for
`1 ≤ k ≤ 1022` because the Bech32m constant is not fixed by the
evaluation. -/

/-- The generator root `r = γ^172`, of order exactly 1023. -/
def rVal : GF1024 := gf1024Exp 172

/-- Powers of `rVal`, in the nested form used by `gf1024GEval`. -/
def xPow : Nat → GF1024
  | 0 => 1
  | 1 => rVal
  | n + 2 => gf1024Mul rVal (xPow (n + 1))

theorem xPow_zero : xPow 0 = 1 := rfl

theorem xPow_one : xPow 1 = rVal := rfl

theorem xPow_succ (j : Nat) : xPow (j + 1) = gf1024Mul rVal (xPow j) := by
  cases j with
  | zero =>
    have h1 : xPow (0 + 1) = rVal := rfl
    have h2 : xPow 0 = 1 := rfl
    rw [h1, h2, gf1024Mul_one]
  | succ n => rfl

theorem xPow_eq_exp : ∀ j : Nat, xPow j = gf1024Exp (172 * j) := by
  intro j
  induction j with
  | zero => rfl
  | succ n ih =>
    rw [xPow_succ, ih]
    have e : 172 + 172 * n = 172 * (n + 1) := by omega
    show gf1024Mul (gf1024Exp 172) (gf1024Exp (172 * n)) = _
    rw [← gf1024Exp_add, e]

/-- `rPow` in the dossier's exponential form. -/
def rPow (k : Nat) : GF1024 := gf1024Exp (172 * k)

theorem rPow_eq_xPow (k : Nat) : rPow k = xPow k := (xPow_eq_exp k).symm

theorem gf1024Exp_ne_zero_nat (n : Nat) : gf1024Exp n ≠ 0 := by
  have hmod : (BitVec.ofNat 10 (n % 1023) : BitVec 10).toNat = n % 1023 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by
      have h := Nat.mod_lt n (show 0 < 1023 by decide)
      omega)
  have hne := gf1024Exp_ne_zero (BitVec.ofNat 10 (n % 1023)) (by
    rw [hmod]
    exact Nat.mod_lt _ (by decide))
  rw [hmod] at hne
  intro h
  apply hne
  have hc := gf1024Exp_congr (a := n) (b := n % 1023) (by rw [Nat.mod_mod])
  rwa [hc] at h

theorem rPow_ne_zero (k : Nat) : rPow k ≠ 0 := gf1024Exp_ne_zero_nat _

theorem gf1024Log_one : gf1024Log 1 = 0 := by
  have h := gf1024Log_exp_nat 0
  rwa [gf1024Exp_zero] at h

set_option maxRecDepth 8192 in
/-- `r^k ≠ 1` for `1 ≤ k ≤ 1022`: the logarithm of `r^k` is
    `172 * k % 1023 ≠ 0`. -/
theorem rPow_ne_one {k : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 1022) :
    rPow k ≠ 1 := by
  intro h
  have hlog : gf1024Log (rPow k) = 0 := by rw [h]; exact gf1024Log_one
  have hlog2 : gf1024Log (gf1024Exp (172 * k)) = 0 := hlog
  rw [gf1024Log_exp_nat] at hlog2
  have hlog := hlog2
  -- (172 * k) % 1023 = 0 with 1 ≤ k ≤ 1022: impossible
  have hfin : ∀ m : Fin 1023, m.val ≠ 0 → (172 * m.val) % 1023 ≠ 0 := by
    decide
  exact hfin ⟨k, by omega⟩ (by simp; omega) (by
    have e : (172 * (⟨k, by omega⟩ : Fin 1023).val) = 172 * k := rfl
    rw [e]; exact hlog)

/-- `gf1024Add` is xor: it vanishes on equal arguments and is
    cancellative. -/
theorem gf1024Add_self (x : GF1024) : gf1024Add x x = 0 :=
  BitVec.xor_self

theorem gf1024Add_eq_zero_imp {x y : GF1024} (h : gf1024Add x y = 0) :
    x = y := by
  have h' : x ^^^ y = 0 := h
  calc x = x ^^^ 0 := BitVec.xor_zero.symm
    _ = x ^^^ (x ^^^ y) := by rw [h']
    _ = y := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem gf1024Add_left_cancel {a b c : GF1024}
    (h : gf1024Add a b = gf1024Add a c) : b = c := by
  have h2 : gf1024Add a (gf1024Add a b) = gf1024Add a (gf1024Add a c) := by
    rw [h]
  rwa [← gf1024Add_assoc, gf1024Add_self, gf1024Add_comm 0 b, gf1024Add_zero,
    ← gf1024Add_assoc, gf1024Add_self, gf1024Add_comm 0 c, gf1024Add_zero] at h2

/-- The embedding of a word is additive (xor) — a finite check. -/
theorem emb_xor : ∀ a b : Word,
    gf1024Emb (a ^^^ b) = gf1024Add (gf1024Emb a) (gf1024Emb b) := by
  decide

theorem emb_zero : gf1024Emb 0 = 0 := by decide

/-- The six generator coefficients as a sum at `rVal`. -/
def genSum : GF1024 :=
  gf1024Add (gf1024Mul (gf1024Emb 18) (xPow 0))
    (gf1024Add (gf1024Mul (gf1024Emb 29) (xPow 1))
      (gf1024Add (gf1024Mul (gf1024Emb 21) (xPow 2))
        (gf1024Add (gf1024Mul (gf1024Emb 20) (xPow 3))
          (gf1024Add (gf1024Mul (gf1024Emb 22) (xPow 4))
            (gf1024Mul (gf1024Emb 29) (xPow 5))))))

/-- The generator polynomial vanishes at `rVal`, so its six lower
    coefficients sum to `rVal^6`. -/
theorem genSum_eq : genSum = xPow 6 := by
  have hroot : gf1024GEval rVal = 0 := gf1024Zeta_root_25
  have hge : gf1024Add genSum (xPow 6) = 0 := by
    have h := hroot
    unfold gf1024GEval at h
    -- reassociate the right-nested sum
    unfold genSum
    rw [xPow_zero, gf1024Mul_one]
    -- now the goal's LHS tree matches GEval's tree up to association
    rw [gf1024Add_assoc, gf1024Add_assoc, gf1024Add_assoc, gf1024Add_assoc,
      gf1024Add_assoc]
    exact h
  exact gf1024Add_eq_zero_imp hge

/-! ## The BIP-350 insertion theorems (dossier §1.3 C, L5.6), via
    evaluation at the generator root (stage E provides `xPow`,
    `genSum`, and the field facts). -/

/-- Evaluation of a checksum state at the generator root:
    `stateEval s = Σ_j emb (chunkW s j) * r^j` over the six chunks. -/
def stateEval (s : BitVec 30) : GF1024 :=
  ([0, 1, 2, 3, 4, 5].map (fun j =>
    gf1024Mul (gf1024Emb (chunkW s j)) (xPow j))).foldr gf1024Add 0

theorem genChunk_zero : genChunk 0 = 18 := by decide
theorem genChunk_one : genChunk 1 = 29 := by decide
theorem genChunk_two : genChunk 2 = 21 := by decide
theorem genChunk_three : genChunk 3 = 20 := by decide
theorem genChunk_four : genChunk 4 = 22 := by decide
theorem genChunk_five : genChunk 5 = 29 := by decide

/-- Four-term swap for the additive fold splitting. -/
theorem add_swap_mid (a b c d : GF1024) :
    gf1024Add (gf1024Add a b) (gf1024Add c d) =
      gf1024Add (gf1024Add a c) (gf1024Add b d) := by
  show (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d)
  ac_rfl

/-- Splitting a fold of sums into a sum of folds. -/
theorem foldr_add_split (f g : Nat → GF1024) (l : List Nat) :
    (l.map (fun j => gf1024Add (f j) (g j))).foldr gf1024Add 0 =
      gf1024Add ((l.map f).foldr gf1024Add 0)
        ((l.map g).foldr gf1024Add 0) := by
  induction l with
  | nil => simp only [List.map_nil, List.foldr_nil, gf1024Add_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    exact add_swap_mid _ _ _ _

/-- Factoring a constant out of a fold of products. -/
theorem foldr_add_factor (c : GF1024) (f : Nat → GF1024) (l : List Nat) :
    (l.map (fun j => gf1024Mul c (f j))).foldr gf1024Add 0 =
      gf1024Mul c ((l.map f).foldr gf1024Add 0) := by
  induction l with
  | nil => simp only [List.map_nil, List.foldr_nil, gf1024Mul_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, ih, gf1024Mul_add]

theorem xPow_succ' (j : Nat) : xPow (j + 1) = gf1024Mul (xPow j) rVal := by
  rw [xPow_succ, gf1024Mul_comm]

/-- Coherence: multiplication by `r` shifts the evaluation index. -/
theorem mul_rVal_pow (y : GF1024) (j : Nat) :
    gf1024Mul rVal (gf1024Mul y (xPow j)) = gf1024Mul y (xPow (j + 1)) := by
  rw [xPow_succ, ← gf1024Mul_assoc, gf1024Mul_comm rVal y, gf1024Mul_assoc]

/-- The generator-part fold factors through `emb (chunkW s 5)`. -/
theorem gen_fold_eq (s : BitVec 30) :
    ([0, 1, 2, 3, 4, 5].map (fun j =>
      gf1024Mul (gf1024Emb (gf32Mul (chunkW s 5) (genChunk j)))
        (xPow j))).foldr gf1024Add 0 =
      gf1024Mul (gf1024Emb (chunkW s 5)) genSum := by
  have hpt : ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb (gf32Mul (chunkW s 5) (genChunk j)))
          (xPow j))) =
      ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb (chunkW s 5))
          (gf1024Mul (gf1024Emb (genChunk j)) (xPow j)))) := by
    apply List.map_congr_left
    intro j _
    rw [gf1024Emb_mul, gf1024Mul_assoc]
  rw [hpt, foldr_add_factor]
  -- the remaining fold is `genSum` computed out
  unfold genSum
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    genChunk_zero, genChunk_one, genChunk_two, genChunk_three, genChunk_four,
    genChunk_five, xPow_zero, gf1024Mul_one, gf1024Add_zero]

/-- The intertwining: one checksum step multiplies the evaluation
    by `r` and adds the embedded input word. -/
theorem stateEval_step (s : BitVec 30) (v : Word) :
    stateEval (polymodStep s v) =
      gf1024Add (gf1024Mul rVal (stateEval s)) (gf1024Emb v) := by
  have hsplit : ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb (chunkW (polymodStep s v) j)) (xPow j))) =
      ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Add
          (gf1024Mul (gf1024Emb
            ((if j = 0 then (0 : Word) else chunkW s (j - 1)) ^^^
              (if j = 0 then v else (0 : Word)))) (xPow j))
          (gf1024Mul (gf1024Emb (gf32Mul (chunkW s 5) (genChunk j)))
            (xPow j)))) := by
    apply List.map_congr_left
    intro j hj
    have hj6 : j < 6 := by
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
        simpa using hj
      omega
    rw [polymodStep_chunk s v j hj6, emb_xor, gf1024Add_mul]
  have hA : ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb
          ((if j = 0 then (0 : Word) else chunkW s (j - 1)) ^^^
            (if j = 0 then v else (0 : Word)))) (xPow j))).foldr
        gf1024Add 0 =
      gf1024Add (gf1024Mul (gf1024Emb v) (xPow 0))
        (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 0)) (xPow 1))
          (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 1)) (xPow 2))
            (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 2)) (xPow 3))
              (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 3)) (xPow 4))
                (gf1024Mul (gf1024Emb (chunkW s 4)) (xPow 5)))))) := by
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      gf1024Add_zero]
    simp [BitVec.zero_xor, BitVec.xor_zero]
  have hdef : ∀ t : BitVec 30, stateEval t =
      ([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb (chunkW t j)) (xPow j))).foldr gf1024Add 0 :=
    fun t => rfl
  rw [hdef, hdef, hsplit, foldr_add_split, hA, gen_fold_eq, genSum_eq]
  -- RHS: distribute rVal over the evaluation of s
  have hR : gf1024Mul rVal
      (([0, 1, 2, 3, 4, 5].map (fun j =>
        gf1024Mul (gf1024Emb (chunkW s j)) (xPow j))).foldr gf1024Add 0) =
      gf1024Add (gf1024Mul (gf1024Emb (chunkW s 0)) (xPow 1))
        (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 1)) (xPow 2))
          (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 2)) (xPow 3))
            (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 3)) (xPow 4))
              (gf1024Add (gf1024Mul (gf1024Emb (chunkW s 4)) (xPow 5))
                (gf1024Mul (gf1024Emb (chunkW s 5)) (xPow 6)))))) := by
    rw [← foldr_add_factor]
    have hpt : ([0, 1, 2, 3, 4, 5].map (fun j =>
          gf1024Mul rVal (gf1024Mul (gf1024Emb (chunkW s j)) (xPow j)))) =
        ([0, 1, 2, 3, 4, 5].map (fun j =>
          gf1024Mul (gf1024Emb (chunkW s j)) (xPow (j + 1)))) := by
      apply List.map_congr_left
      intro j _
      exact mul_rVal_pow _ _
    rw [hpt]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
      gf1024Add_zero, Nat.reduceAdd]
  rw [hR, xPow_zero, gf1024Mul_one]
  unfold gf1024Add
  ac_rfl

/-- Folding a run of zero words multiplies the evaluation by `r^k`. -/
theorem stateEval_fold_replicate_zero (S : BitVec 30) (k : Nat) :
    stateEval ((List.replicate k 0).foldl polymodStep S) =
      gf1024Mul (xPow k) (stateEval S) := by
  induction k generalizing S with
  | zero =>
    show stateEval S = gf1024Mul (xPow 0) (stateEval S)
    rw [xPow_zero, gf1024Mul_comm, gf1024Mul_one]
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, stateEval_step, emb_zero,
      gf1024Add_zero, xPow_succ', gf1024Mul_assoc]

/-- The Bech32m constant is not fixed by the root evaluation. -/
theorem stateEval_const_hi : gf1024Hi (stateEval 0x2bc830a3) ≠ 0 := by
  decide

theorem add_eq_of_add_right {a b c : GF1024} (h : gf1024Add a c = b) :
    a = gf1024Add b c := by
  rw [← h, gf1024Add_assoc, gf1024Add_self, gf1024Add_zero]

theorem mul_right_cancel {a b c : GF1024} (hc : c ≠ 0)
    (h : gf1024Mul a c = gf1024Mul b c) : a = b := by
  have h2 := congrArg (fun z => gf1024Mul z (gf1024Inv c)) h
  rwa [gf1024Mul_assoc, gf1024Mul_assoc, gf1024Mul_inv_cancel hc,
    gf1024Mul_one, gf1024Mul_one] at h2

theorem mul_left_cancel {a b c : GF1024} (ha : a ≠ 0)
    (h : gf1024Mul a b = gf1024Mul a c) : b = c := by
  have h2 := congrArg (fun z => gf1024Mul (gf1024Inv a) z) h
  have hinv : gf1024Mul (gf1024Inv a) a = 1 := by
    rw [gf1024Mul_comm]
    exact gf1024Mul_inv_cancel ha
  rwa [← gf1024Mul_assoc, ← gf1024Mul_assoc, hinv,
    gf1024Mul_comm (1 : GF1024) b, gf1024Mul_comm (1 : GF1024) c,
    gf1024Mul_one, gf1024Mul_one] at h2

/-- **BIP-350, Bech32m side.**  Inserting `k` zero words (`q` characters)
    before the final data word is always detected for `1 ≤ k ≤ 1022`:
    the checksum constant is moved by the factor `r^k ≠ 1`. -/
theorem bech32m_q_insertion_detected (hrp : List Char) (pfx : List Word)
    (w : Word) (k : Nat) (hk_lo : 1 ≤ k) (hk_hi : k ≤ 1022)
    (hvalid : verifyChecksum Variant.bech32m hrp (pfx ++ [w]) = true) :
    verifyChecksum Variant.bech32m hrp (pfx ++ List.replicate k 0 ++ [w])
      = false := by
  by_cases hcon :
      verifyChecksum Variant.bech32m hrp (pfx ++ List.replicate k 0 ++ [w])
        = false
  · exact hcon
  · exfalso
    have hv2 : verifyChecksum Variant.bech32m hrp
        (pfx ++ List.replicate k 0 ++ [w]) = true := by
      cases h : verifyChecksum Variant.bech32m hrp
          (pfx ++ List.replicate k 0 ++ [w]) with
      | false => exact absurd h hcon
      | true => rfl
    have hp1 : polymod (hrpExpand hrp ++ (pfx ++ [w])) = 0x2bc830a3 := by
      have hv := hvalid
      simp only [verifyChecksum, beq_iff_eq] at hv
      exact hv
    have hp2 : polymod (hrpExpand hrp ++ (pfx ++ List.replicate k 0 ++ [w]))
        = 0x2bc830a3 := by
      have hv := hv2
      simp only [verifyChecksum, beq_iff_eq] at hv
      exact hv
    -- state-level equations
    obtain ⟨S0, hS0⟩ : ∃ s : BitVec 30,
        s = (hrpExpand hrp ++ pfx).foldl polymodStep 1 := ⟨_, rfl⟩
    have eq1 : polymodStep S0 w = 0x2bc830a3 := by
      have e : polymod (hrpExpand hrp ++ (pfx ++ [w])) =
          polymodStep S0 w := by
        have h1 : hrpExpand hrp ++ (pfx ++ [w]) =
            (hrpExpand hrp ++ pfx) ++ [w] := by
          rw [List.append_assoc]
        rw [h1]
        show ((hrpExpand hrp ++ pfx) ++ [w]).foldl polymodStep 1 = _
        rw [List.foldl_append, ← hS0]
        rfl
      rwa [e] at hp1
    have eq2 : polymodStep ((List.replicate k 0).foldl polymodStep S0) w
        = 0x2bc830a3 := by
      have e : polymod (hrpExpand hrp ++ (pfx ++ List.replicate k 0 ++ [w]))
          = polymodStep ((List.replicate k 0).foldl polymodStep S0) w := by
        have h1 : hrpExpand hrp ++ (pfx ++ List.replicate k 0 ++ [w]) =
            ((hrpExpand hrp ++ pfx) ++ List.replicate k 0) ++ [w] := by
          simp [List.append_assoc]
        rw [h1]
        show (((hrpExpand hrp ++ pfx) ++ List.replicate k 0) ++ [w]).foldl
            polymodStep 1 = _
        rw [List.foldl_append, List.foldl_append, ← hS0]
        rfl
      rwa [e] at hp2
    -- evaluate both equations at the root
    have hse1 : gf1024Add (gf1024Mul rVal (stateEval S0)) (gf1024Emb w) =
        stateEval 0x2bc830a3 := by
      have h := congrArg stateEval eq1
      rwa [stateEval_step] at h
    have hse2 : gf1024Add
        (gf1024Mul rVal (stateEval ((List.replicate k 0).foldl
          polymodStep S0))) (gf1024Emb w) = stateEval 0x2bc830a3 := by
      have h := congrArg stateEval eq2
      rwa [stateEval_step] at h
    rw [stateEval_fold_replicate_zero] at hse2
    have key1 : gf1024Mul rVal (stateEval S0) =
        gf1024Add (stateEval 0x2bc830a3) (gf1024Emb w) :=
      add_eq_of_add_right hse1
    have key2 : gf1024Mul rVal (gf1024Mul (xPow k) (stateEval S0)) =
        gf1024Add (stateEval 0x2bc830a3) (gf1024Emb w) :=
      add_eq_of_add_right hse2
    by_cases hX : stateEval S0 = 0
    · -- then the constant's evaluation equals `emb w`, whose high
      -- chunk vanishes — but the constant's does not
      rw [hX, gf1024Mul_zero] at key1
      have hEq : stateEval 0x2bc830a3 = gf1024Emb w :=
        gf1024Add_eq_zero_imp key1.symm
      have hHi := congrArg gf1024Hi hEq
      rw [gf1024Hi_emb] at hHi
      exact stateEval_const_hi hHi
    · -- cancel `rVal`, then `stateEval S0`: `xPow k = 1`
      have hmul : gf1024Mul (xPow k) (stateEval S0) = stateEval S0 := by
        apply mul_left_cancel (a := rVal) (gf1024Exp_ne_zero_nat 172)
        rw [key2, ← key1]
      have hone : xPow k = 1 := by
        apply mul_right_cancel (c := stateEval S0) hX
        rw [gf1024Mul_comm (1 : GF1024) (stateEval S0), gf1024Mul_one]
        exact hmul
      have hr1 : rPow k = 1 := by
        rw [rPow_eq_xPow]
        exact hone
      exact rPow_ne_one hk_lo hk_hi hr1

/-! ## Cross-variant disjointness (dossier §1.3 C / M5) -/

/-- The difference of the two checksum constants. -/
def crossD : BitVec 30 := (1 : BitVec 30) ^^^ 0x2bc830a3

theorem crossD_ne_zero : crossD ≠ 0 := by decide

def crossDNat : Nat := crossD.toNat

def minorD2Ok (x : Nat) : Bool :=
  coordPairs.any (fun p => det2Nat x crossDNat p.1 p.2 != 0)

def minorD3Ok (x y : Nat) : Bool :=
  coordTriples.any (fun p => det3Nat x y crossDNat p.1 p.2.1 p.2.2 != 0)

/-- Certificate: every syndrome `syn d 1` (`1 ≤ d ≤ 88`) is independent
    of the cross-variant difference state. -/
def certD2 : Bool :=
  (List.range 88).all (fun i => minorD2Ok (synEntry (i + 1)))

/-- Certificate: any two syndromes at distances `1 ≤ d2 < d1 ≤ 88`
    together with the difference state are independent. -/
def certD3 : Bool :=
  (List.range 87).all (fun i =>
    (List.range (i + 1)).all (fun j =>
      minorD3Ok (synEntry (i + 2)) (synEntry (j + 1))))

theorem certD2_eq : certD2 = true := by decide

theorem certD3_eq : certD3 = true := by decide

theorem exists_detD2 (d : Nat) (hd : 1 ≤ d) (hd2 : d ≤ 88) :
    ∃ i j : Nat, (i, j) ∈ coordPairs ∧ det2W (syn d 1) crossD i j ≠ 0 := by
  have hc := certD2_eq
  unfold certD2 at hc
  have h1' := List.all_eq_true.mp hc (d - 1) (List.mem_range.mpr (by omega))
  simp only [show d - 1 + 1 = d by omega] at h1'
  unfold minorD2Ok at h1'
  obtain ⟨p, hp_mem, hp_ne⟩ := List.any_eq_true.mp h1'
  have hp_ne : (det2Nat (synEntry d) crossDNat p.1 p.2 != 0) = true := hp_ne
  refine ⟨p.1, p.2, hp_mem, ?_⟩
  have hne : det2Nat (synEntry d) crossDNat p.1 p.2 ≠ 0 := by
    intro hz
    rw [hz] at hp_ne
    simp at hp_ne
  intro hzero
  apply hne
  have h3 : (det2W (syn d 1) crossD p.1 p.2).toNat = 0 := by
    rw [hzero]; rfl
  rw [det2W_toNat, ← synEntry_ofNat d (by omega)] at h3
  exact h3

theorem exists_detD3 (d1 d2 : Nat) (h2 : 1 ≤ d2) (h12 : d2 < d1)
    (h1 : d1 ≤ 88) :
    ∃ i j k : Nat, (i, j, k) ∈ coordTriples ∧
      det3W (syn d1 1) (syn d2 1) crossD i j k ≠ 0 := by
  have hc := certD3_eq
  unfold certD3 at hc
  have h1' := List.all_eq_true.mp hc (d1 - 2) (List.mem_range.mpr (by omega))
  have h2' := List.all_eq_true.mp h1' (d2 - 1) (List.mem_range.mpr (by omega))
  simp only [show d1 - 2 + 2 = d1 by omega, show d2 - 1 + 1 = d2 by omega]
    at h2'
  unfold minorD3Ok at h2'
  obtain ⟨p, hp_mem, hp_ne⟩ := List.any_eq_true.mp h2'
  have hp_ne : (det3Nat (synEntry d1) (synEntry d2) crossDNat
    p.1 p.2.1 p.2.2 != 0) = true := hp_ne
  refine ⟨p.1, p.2.1, p.2.2, hp_mem, ?_⟩
  have hne : det3Nat (synEntry d1) (synEntry d2) crossDNat p.1 p.2.1 p.2.2 ≠ 0 := by
    intro hz
    rw [hz] at hp_ne
    simp at hp_ne
  intro hzero
  apply hne
  have h4 : (det3W (syn d1 1) (syn d2 1) crossD p.1 p.2.1 p.2.2).toNat = 0 := by
    rw [hzero]; rfl
  rw [det3W_toNat, ← synEntry_ofNat d1 (by omega),
    ← synEntry_ofNat d2 (by omega)] at h4
  exact h4

/-- Chunk equations for a one-term decomposition. -/
theorem chunk_eq_of_syn_eq {d : Nat} {v : Word} {t : Nat} (ht : t < 6)
    (h : syn d v = crossD) :
    gf32Mul v (chunkW (syn d 1) t) = chunkW crossD t := by
  have h2 : syn d v = scaleState v (syn d 1) := by
    have h3 := syn_scale v d 1
    rwa [gf32Mul_one] at h3
  rw [h2] at h
  rw [← h, chunkW_scaleState _ _ _ ht]

/-- Cross-variant minimum distance at least 3 within the distance-5
    shortening range (dossier M5): with the separator structure and HRP
    high bits fixed, two substitutions never turn a Bech32 string into
    a Bech32m string. -/
theorem verifyChecksum_bech32_bech32m_disjoint_of_dist_le_two
    (hrp₁ hrp₂ : List Char) (data₁ data₂ : List Word)
    (hhrp_len : hrp₁.length = hrp₂.length)
    (hdata_len : data₁.length = data₂.length)
    (hbound : hrp₁.length + data₁.length ≤ 89)
    (hascii₁ : ∀ c ∈ hrp₁, c.toNat ≤ 126)
    (hascii₂ : ∀ c ∈ hrp₂, c.toNat ≤ 126)
    (hhi : hrp₁.map (fun c => c.toNat >>> 5) =
      hrp₂.map (fun c => c.toNat >>> 5))
    (hdist : hammingDist hrp₁ hrp₂ + hammingDist data₁ data₂ ≤ 2)
    (hv1 : verifyChecksum Variant.bech32 hrp₁ data₁ = true) :
    verifyChecksum Variant.bech32m hrp₂ data₂ = false := by
  by_cases hcon : verifyChecksum Variant.bech32m hrp₂ data₂ = false
  · exact hcon
  · exfalso
    have hv2 : verifyChecksum Variant.bech32m hrp₂ data₂ = true := by
      cases h : verifyChecksum Variant.bech32m hrp₂ data₂ with
      | false => exact absurd h hcon
      | true => rfl
    have hp1 : polymod (hrpExpand hrp₁ ++ data₁) = 1 := by
      have hv := hv1
      simp only [verifyChecksum, beq_iff_eq] at hv
      exact hv
    have hp2 : polymod (hrpExpand hrp₂ ++ data₂) = 0x2bc830a3 := by
      have hv := hv2
      simp only [verifyChecksum, beq_iff_eq] at hv
      exact hv
    have hhiW : hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) =
        hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) :=
      hrpExpand_hi_eq hrp₁ hrp₂ hhrp_len hhi
    have hexp1 : hrpExpand hrp₁ ++ data₁ =
        (hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0]) ++
          (hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₁) := by
      simp [hrpExpand, List.append_assoc]
    have hexp2 : hrpExpand hrp₂ ++ data₂ =
        (hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0]) ++
          (hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₂) := by
      simp [hrpExpand, List.append_assoc]
    -- fold the common prefix once
    obtain ⟨P, hP⟩ : ∃ l : List Word,
        l = hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0] :=
      ⟨_, rfl⟩
    obtain ⟨R₁, hR₁⟩ : ∃ l : List Word,
        l = hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₁ :=
      ⟨_, rfl⟩
    obtain ⟨R₂, hR₂⟩ : ∃ l : List Word,
        l = hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₂ :=
      ⟨_, rfl⟩
    have hfold1 : polymod (hrpExpand hrp₁ ++ data₁) =
        R₁.foldl polymodStep (P.foldl polymodStep 1) := by
      rw [hexp1, ← hP, ← hR₁]
      exact List.foldl_append
    have hfold2 : polymod (hrpExpand hrp₂ ++ data₂) =
        R₂.foldl polymodStep (P.foldl polymodStep 1) := by
      rw [hexp2, ← hhiW, ← hP, ← hR₂]
      exact List.foldl_append
    have hlenR : R₁.length = R₂.length := by
      simp only [hR₁, hR₂, List.length_append, List.length_map, hhrp_len,
        hdata_len]
    have hZ : (List.zipWith (· ^^^ ·) R₁ R₂).foldl polymodStep 0 =
        crossD := by
      have hx := foldl_polymodStep_xor R₁ R₂ (P.foldl polymodStep 1)
        (P.foldl polymodStep 1) hlenR
      rw [BitVec.xor_self] at hx
      rw [hfold1] at hp1
      rw [hfold2] at hp2
      rw [hp1, hp2] at hx
      exact hx
    have hZlen : (List.zipWith (· ^^^ ·) R₁ R₂).length ≤ 89 := by
      rw [List.length_zipWith, Nat.min_eq_left (by omega)]
      simp only [hR₁, List.length_append, List.length_map]
      exact hbound
    have hZweight : hammingWeight (List.zipWith (· ^^^ ·) R₁ R₂) ≤ 2 := by
      have e : hammingWeight (List.zipWith (· ^^^ ·) R₁ R₂) =
          hammingDist R₁ R₂ :=
        (hammingDist_eq_hammingWeight_xor R₁ R₂ hlenR).symm
      rw [e, hR₁, hR₂, hammingDist_append _ _ _ _
        (by simp [List.length_map, hhrp_len])]
      have m := hammingDist_map_le
        (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) hrp₁ hrp₂
      omega
    -- decompose the difference stream
    have hfoldZ : (List.zipWith (· ^^^ ·) R₁ R₂).foldl polymodStep 0 =
        (decomp (List.zipWith (· ^^^ ·) R₁ R₂)).foldr
          (fun p acc => syn p.1 p.2 ^^^ acc) 0 :=
      fold_eq_xorsum _
    rw [hZ] at hfoldZ
    have hdeclen : (decomp (List.zipWith (· ^^^ ·) R₁ R₂)).length ≤ 2 := by
      rw [decomp_length]
      exact hZweight
    -- case split on the decomposition shape
    cases hdec : decomp (List.zipWith (· ^^^ ·) R₁ R₂) with
    | nil =>
      rw [hdec] at hfoldZ
      simp only [List.foldr_nil] at hfoldZ
      exact crossD_ne_zero hfoldZ
    | cons p rest =>
      have hp_ne : p.2 ≠ 0 := decomp_snd_ne (by rw [hdec]; exact List.mem_cons_self)
      have hp_lt : p.1 < (List.zipWith (· ^^^ ·) R₁ R₂).length :=
        decomp_fst_lt (by rw [hdec]; exact List.mem_cons_self)
      cases rest with
      | nil =>
        -- crossD = syn p.1 p.2
        rw [hdec] at hfoldZ
        simp only [List.foldr_cons, List.foldr_nil] at hfoldZ
        have hxz : syn p.1 p.2 ^^^ (0 : BitVec 30) = syn p.1 p.2 :=
          BitVec.xor_zero
        rw [hxz] at hfoldZ
        -- hfoldZ : crossD = syn p.1 p.2
        by_cases hd0 : p.1 = 0
        · rw [hd0, syn_zero] at hfoldZ
          have htoNat : crossD.toNat < 32 := by
            rw [hfoldZ, BitVec.toNat_setWidth]
            have h := p.2.isLt
            omega
          have hD : crossD.toNat = 0x2bc830a2 := by decide
          omega
        · have hd1 : 1 ≤ p.1 := by omega
          have hd88 : p.1 ≤ 88 := by omega
          obtain ⟨i, j, hij_mem, hij_ne⟩ := exists_detD2 p.1 hd1 hd88
          obtain ⟨hb1, hb2, hb3, hb4⟩ := coordPairs_bounds hij_mem
          have e1 : gf32Mul p.2 (chunkW (syn p.1 1) i) = chunkW crossD i :=
            chunk_eq_of_syn_eq (by omega) hfoldZ.symm
          have e2 : gf32Mul p.2 (chunkW (syn p.1 1) j) = chunkW crossD j :=
            chunk_eq_of_syn_eq (by omega) hfoldZ.symm
          have hcram := cramer2 (syn p.1 1) crossD p.2 1 i j
            (by rw [gf32Mul_comm 1 (chunkW crossD i), gf32Mul_one, ← e1]; exact BitVec.xor_self)
            (by rw [gf32Mul_comm 1 (chunkW crossD j), gf32Mul_one, ← e2]; exact BitVec.xor_self)
          have hzero : det2W (syn p.1 1) crossD i j = 0 := by
            have h := gf32Mul_eq_zero hcram
            cases h with
            | inl h => exact absurd h hp_ne
            | inr h => exact h
          exact hij_ne hzero
      | cons q rest2 =>
        -- two terms; rest2 must be empty (weight ≤ 2)
        have hq_ne : q.2 ≠ 0 :=
          decomp_snd_ne (by rw [hdec]; exact List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have hq_lt : q.1 < (List.zipWith (· ^^^ ·) R₁ R₂).length :=
          decomp_fst_lt (by rw [hdec]; exact List.mem_cons.mpr (Or.inr List.mem_cons_self))
        have hrest2 : rest2 = [] := by
          cases rest2 with
          | nil => rfl
          | cons r rest3 =>
            rw [hdec] at hdeclen
            simp only [List.length_cons] at hdeclen
            exact (by omega : False).elim
        subst hrest2
        rw [hdec] at hfoldZ
        simp only [List.foldr_cons, List.foldr_nil] at hfoldZ
        have hxz : syn q.1 q.2 ^^^ (0 : BitVec 30) = syn q.1 q.2 :=
          BitVec.xor_zero
        rw [hxz] at hfoldZ
        -- hfoldZ : crossD = syn p.1 p.2 ^^^ syn q.1 q.2, with q.1 < p.1
        have hpq : q.1 < p.1 := by
          have hpair := decomp_pairwise (List.zipWith (· ^^^ ·) R₁ R₂)
          rw [hdec] at hpair
          have := List.pairwise_cons.mp hpair
          exact this.1 _ List.mem_cons_self
        by_cases hq0 : q.1 = 0
        · -- chunk equations at coordinates ≥ 1 against certD2 on p
          rw [hq0] at hfoldZ
          have hd1 : 1 ≤ p.1 := by omega
          have hd88 : p.1 ≤ 88 := by omega
          obtain ⟨i, j, hij_mem, hij_ne⟩ := exists_detD2 p.1 hd1 hd88
          obtain ⟨hb1, hb2, hb3, hb4⟩ := coordPairs_bounds hij_mem
          have e1 : gf32Mul p.2 (chunkW (syn p.1 1) i) = chunkW crossD i := by
            have hch : chunkW crossD i =
                chunkW (syn p.1 p.2 ^^^ syn 0 q.2) i :=
              congrArg (fun s => chunkW s i) hfoldZ
            rw [chunkW_xor] at hch
            have hsyn0 : chunkW (syn 0 q.2) i = 0 := by
              rw [syn_zero, chunkW_setWidth, if_neg (by omega : i ≠ 0)]
            rw [hsyn0] at hch
            have hxz : chunkW (syn p.1 p.2) i ^^^ (0 : Word) =
                chunkW (syn p.1 p.2) i := BitVec.xor_zero
            rw [hxz] at hch
            have h2 : syn p.1 p.2 = scaleState p.2 (syn p.1 1) := by
              have h3 := syn_scale p.2 p.1 1
              rwa [gf32Mul_one] at h3
            rw [h2, chunkW_scaleState _ _ _ (by omega)] at hch
            exact hch.symm
          have e2 : gf32Mul p.2 (chunkW (syn p.1 1) j) = chunkW crossD j := by
            have hch : chunkW crossD j =
                chunkW (syn p.1 p.2 ^^^ syn 0 q.2) j :=
              congrArg (fun s => chunkW s j) hfoldZ
            rw [chunkW_xor] at hch
            have hsyn0 : chunkW (syn 0 q.2) j = 0 := by
              rw [syn_zero, chunkW_setWidth, if_neg (by omega : j ≠ 0)]
            rw [hsyn0] at hch
            have hxz : chunkW (syn p.1 p.2) j ^^^ (0 : Word) =
                chunkW (syn p.1 p.2) j := BitVec.xor_zero
            rw [hxz] at hch
            have h2 : syn p.1 p.2 = scaleState p.2 (syn p.1 1) := by
              have h3 := syn_scale p.2 p.1 1
              rwa [gf32Mul_one] at h3
            rw [h2, chunkW_scaleState _ _ _ (by omega)] at hch
            exact hch.symm
          have hcram := cramer2 (syn p.1 1) crossD p.2 1 i j
            (by rw [gf32Mul_comm 1 (chunkW crossD i), gf32Mul_one, ← e1]; exact BitVec.xor_self)
            (by rw [gf32Mul_comm 1 (chunkW crossD j), gf32Mul_one, ← e2]; exact BitVec.xor_self)
          have hzero : det2W (syn p.1 1) crossD i j = 0 := by
            have h := gf32Mul_eq_zero hcram
            cases h with
            | inl h => exact absurd h hp_ne
            | inr h => exact h
          exact hij_ne hzero
        · -- full cramer3 against certD3
          have hd1 : 1 ≤ q.1 := by omega
          have hd88 : p.1 ≤ 88 := by omega
          obtain ⟨i, j, k, hijk_mem, hijk_ne⟩ := exists_detD3 p.1 q.1 hd1 hpq hd88
          obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := coordTriples_bounds hijk_mem
          have e1 : ∀ t : Nat, t < 6 →
              gf32Mul p.2 (chunkW (syn p.1 1) t) ^^^
                gf32Mul q.2 (chunkW (syn q.1 1) t) = chunkW crossD t := by
            intro t ht
            have hch : chunkW crossD t =
                chunkW (syn p.1 p.2 ^^^ syn q.1 q.2) t :=
              congrArg (fun s => chunkW s t) hfoldZ
            rw [chunkW_xor] at hch
            have h2 : syn p.1 p.2 = scaleState p.2 (syn p.1 1) := by
              have h3 := syn_scale p.2 p.1 1
              rwa [gf32Mul_one] at h3
            have h3' : syn q.1 q.2 = scaleState q.2 (syn q.1 1) := by
              have h4 := syn_scale q.2 q.1 1
              rwa [gf32Mul_one] at h4
            rw [h2, h3', chunkW_scaleState _ _ _ ht,
              chunkW_scaleState _ _ _ ht] at hch
            exact hch.symm
          have hcram := cramer3 (syn p.1 1) (syn q.1 1) crossD p.2 q.2 1 i j k
            (by rw [gf32Mul_comm 1 (chunkW crossD i), gf32Mul_one, ← e1 i (by omega)]; exact BitVec.xor_self)
            (by rw [gf32Mul_comm 1 (chunkW crossD j), gf32Mul_one, ← e1 j (by omega)]; exact BitVec.xor_self)
            (by rw [gf32Mul_comm 1 (chunkW crossD k), gf32Mul_one, ← e1 k (by omega)]; exact BitVec.xor_self)
          have hzero : det3W (syn p.1 1) (syn q.1 1) crossD i j k = 0 := by
            have h := gf32Mul_eq_zero hcram
            cases h with
            | inl h => exact absurd h hp_ne
            | inr h => exact h
          exact hijk_ne hzero

/-! ## Kernel-checked counterexamples (dossier §1.4, L5.7)

Every hypothesis of the refined guarantees is necessary: each
failure mechanism of the naive string-level claim is exhibited by
a pair of strings that both decode.  All are `by decide`. -/

set_option maxRecDepth 16384 in
theorem cex1_case_twins_bech32 :
    decode Variant.bech32 "A19267542334" ≠ none ∧
    decode Variant.bech32 "a19267542334" ≠ none ∧
    hammingDist "A19267542334".toList "a19267542334".toList = 1 := by decide

set_option maxRecDepth 16384 in
theorem cex1_case_twins_bech32m :
    decode Variant.bech32m "A18335205628" ≠ none ∧
    decode Variant.bech32m "a18335205628" ≠ none ∧
    hammingDist "A18335205628".toList "a18335205628".toList = 1 := by decide

set_option maxRecDepth 16384 in
theorem cex2a_separator_in_data_bech32 :
    decode Variant.bech32 "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqqqvqx2rt" ≠ none ∧
    decode Variant.bech32 "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqq1vqx2rt" ≠ none ∧
    hammingDist "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqqqvqx2rt".toList "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqq1vqx2rt".toList = 1 := by decide

set_option maxRecDepth 16384 in
theorem cex2a_separator_in_data_bech32m :
    decode Variant.bech32m "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqqqeukxxf" ≠ none ∧
    decode Variant.bech32m "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqq1eukxxf" ≠ none ∧
    hammingDist "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqqqeukxxf".toList "a1qppppppqqpqpqpqqpppqqppqqppqqqqqqqq1eukxxf".toList = 1 := by decide

set_option maxRecDepth 16384 in
theorem cex2b_separator_relocation_bech32 :
    decode Variant.bech32 "bc1pqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqqqy5zkgn" ≠ none ∧
    decode Variant.bech32 "bcapqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqq1y5zkgn" ≠ none ∧
    hammingDist "bc1pqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqqqy5zkgn".toList "bcapqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqq1y5zkgn".toList = 2 := by decide

set_option maxRecDepth 16384 in
theorem cex2b_separator_relocation_bech32m :
    decode Variant.bech32m "bc1pqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqqq3gj6d3" ≠ none ∧
    decode Variant.bech32m "bcapqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqq13gj6d3" ≠ none ∧
    hammingDist "bc1pqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqqq3gj6d3".toList "bcapqpqqqpqqqqqqqqpqpqqppppqqqpppqqqqq13gj6d3".toList = 2 := by decide

set_option maxRecDepth 16384 in
theorem cex3a_cross_block_hrp_bech32 :
    decode Variant.bech32 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@158j4f9" ≠ none ∧
    decode Variant.bech32 "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaataaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaam158j4f9" ≠ none ∧
    hammingDist "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@158j4f9".toList "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaataaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaam158j4f9".toList = 2 := by decide

set_option maxRecDepth 16384 in
theorem cex3a_cross_block_hrp_bech32m :
    decode Variant.bech32m "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@1pmzev8" ≠ none ∧
    decode Variant.bech32m "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaataaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaam1pmzev8" ≠ none ∧
    hammingDist "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa@1pmzev8".toList "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaataaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaam1pmzev8".toList = 2 := by decide

set_option maxRecDepth 16384 in
theorem cex3b_cross_block_hrp_bech32 :
    decode Variant.bech32 "9aaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqkklkx8" ≠ none ∧
    decode Variant.bech32 "vaaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqqkklkx5" ≠ none ∧
    hammingDist "9aaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqkklkx8".toList "vaaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqqkklkx5".toList = 3 := by decide

set_option maxRecDepth 16384 in
theorem cex3b_cross_block_hrp_bech32m :
    decode Variant.bech32m "9aaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqr206r9" ≠ none ∧
    decode Variant.bech32m "vaaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqqr206rk" ≠ none ∧
    hammingDist "9aaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqr206r9".toList "vaaaaaaaa1qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqqr206rk".toList = 3 := by decide

set_option maxRecDepth 16384 in
theorem cex3c_cross_block_hrp_bech32 :
    decode Variant.bech32 "21qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq0e9236" ≠ none ∧
    decode Variant.bech32 "r1qqqqqqq0qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqq0e923f" ≠ none ∧
    hammingDist "21qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq0e9236".toList "r1qqqqqqq0qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqq0e923f".toList = 4 := by decide

set_option maxRecDepth 16384 in
theorem cex3c_cross_block_hrp_bech32m :
    decode Variant.bech32m "21qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq694x5c" ≠ none ∧
    decode Variant.bech32m "r1qqqqqqq0qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqq694x5t" ≠ none ∧
    hammingDist "21qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq694x5c".toList "r1qqqqqqq0qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq7qqqqqqqq694x5t".toList = 4 := by decide

set_option maxRecDepth 16384 in
theorem cex_length_91_bech32 :
    verifyChecksum Variant.bech32 ['a'] (List.replicate 83 0 ++ [31, 15, 24, 24, 13, 4]) = true ∧
    verifyChecksum Variant.bech32 ['b'] (List.replicate 9 0 ++ [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 31, 15, 24, 24, 13, 10]) = true ∧
    hammingDist ['a'] ['b'] + hammingDist
      (List.replicate 83 0 ++ [31, 15, 24, 24, 13, 4]) (List.replicate 9 0 ++ [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 31, 15, 24, 24, 13, 10]) = 4 := by decide

set_option maxRecDepth 16384 in
theorem cex_length_91_bech32m :
    verifyChecksum Variant.bech32m ['a'] (List.replicate 83 0 ++ [10, 19, 8, 20, 8, 6]) = true ∧
    verifyChecksum Variant.bech32m ['b'] (List.replicate 9 0 ++ [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 10, 19, 8, 20, 8, 8]) = true ∧
    hammingDist ['a'] ['b'] + hammingDist
      (List.replicate 83 0 ++ [10, 19, 8, 20, 8, 6]) (List.replicate 9 0 ++ [28, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 10, 19, 8, 20, 8, 8]) = 4 := by decide

set_option maxRecDepth 16384 in
theorem cex_cross_variant_distance_three :
    verifyChecksum Variant.bech32 ['a'] (List.replicate 74 0 ++ [1, 27, 22, 17, 13, 12]) = true ∧
    verifyChecksum Variant.bech32m ['a'] ([20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 27, 22, 17, 13, 12]) = true ∧
    hammingDist (List.replicate 74 0 ++ [1, 27, 22, 17, 13, 12]) ([20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 27, 22, 17, 13, 12]) = 3 := by decide

end Bech32
