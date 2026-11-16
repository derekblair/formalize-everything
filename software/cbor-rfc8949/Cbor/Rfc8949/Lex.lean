/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Map-key byte orders (§4.2.1, §4.2.3, CTAP2) and stable insertion sort

RFC 8949 §4.2.1 sorts map keys in the bytewise lexicographic order of their
deterministic encodings (`lexLt`). §4.2.3 defines the length-first order
inherited from RFC 7049 §3.9 (`lengthFirstLt`: shorter encodings first, ties
broken by `lexLt`) and discusses FIDO CTAP2's canonical CBOR order (`ctap2Lt`:
major type first, then encoded byte length, then `lexLt`). All three are
strict total orders on `List UInt8`; `sortBy` is a stable insertion sort,
written with structural recursion so the kernel can run it directly. Item-level
profile comparison theorems (`order_core_eq_ctap2_atomic` and
`order_core_ne_ctap2_compound`) live in `Cbor.Rfc8949.Ordering`.
-/

namespace Cbor.Rfc8949

/-- Bytewise lexicographic order on byte strings. -/
def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if a = b then lexLt as bs else false

theorem lexLt_irrefl : ∀ l : List UInt8, lexLt l l = false
  | [] => rfl
  | a :: as => by simp [lexLt, lexLt_irrefl as]

theorem lexLt_cons_cons (a b : UInt8) (as bs : List UInt8) :
    lexLt (a :: as) (b :: bs) = true ↔ a.toNat < b.toNat ∨ (a = b ∧ lexLt as bs = true) := by
  simp only [lexLt]
  split
  · simp [*]
  · split
    · simp_all
    · rename_i h1 h2
      simp [h1, h2]

theorem lexLt_asymm : ∀ {a b : List UInt8}, lexLt a b = true → lexLt b a = false
  | [], [], h => by simp [lexLt] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [lexLt] at h
  | a :: as, b :: bs, h => by
    rw [lexLt_cons_cons] at h
    cases hba : lexLt (b :: bs) (a :: as)
    · rfl
    · rw [lexLt_cons_cons] at hba
      rcases h with h | ⟨rfl, h⟩
      · rcases hba with h' | ⟨rfl, _⟩ <;> omega
      · rcases hba with h' | ⟨_, h'⟩
        · omega
        · rw [lexLt_asymm h] at h'; exact h'.symm

theorem lexLt_trans : ∀ {a b c : List UInt8}, lexLt a b = true → lexLt b c = true →
    lexLt a c = true
  | [], [], _, h, _ => by simp [lexLt] at h
  | [], _ :: _, [], _, h => by simp [lexLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [lexLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexLt] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    rw [lexLt_cons_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (by omega)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans h1 h2⟩

theorem lexLt_total : ∀ {a b : List UInt8}, a ≠ b → lexLt a b = true ∨ lexLt b a = true
  | [], [], h => absurd rfl h
  | [], _ :: _, _ => Or.inl rfl
  | _ :: _, [], _ => Or.inr rfl
  | a :: as, b :: bs, h => by
    rw [lexLt_cons_cons, lexLt_cons_cons]
    by_cases hab : a = b
    · subst hab
      have : as ≠ bs := fun e => h (by rw [e])
      rcases lexLt_total this with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · have : a.toNat ≠ b.toNat := fun e => hab (UInt8.toNat_inj.mp e)
      by_cases hlt : a.toNat < b.toNat
      · exact Or.inl (Or.inl hlt)
      · exact Or.inr (Or.inl (by omega))

theorem lexLt_append_left : ∀ (p a b : List UInt8), lexLt (p ++ a) (p ++ b) = lexLt a b
  | [], _, _ => rfl
  | x :: p, a, b => by simp [lexLt, lexLt_append_left p a b]

theorem lexLt_neg_trans {a b c : List UInt8} (hab : lexLt a b = false)
    (hbc : lexLt b c = false) : lexLt a c = false := by
  cases hac : lexLt a c
  · rfl
  · exfalso
    by_cases heq : a = b
    · subst heq; rw [hac] at hbc; exact Bool.noConfusion hbc
    · rcases lexLt_total heq with h | h
      · rw [h] at hab; exact Bool.noConfusion hab
      · rw [lexLt_trans h hac] at hbc; exact Bool.noConfusion hbc

/-! ## Length-first byte order (RFC 8949 §4.2.3) -/

/-- Length-first map key order on byte strings (RFC 8949 §4.2.3, formerly
RFC 7049 §3.9): shorter byte strings sort earlier; equal-length byte strings
sort in bytewise lexicographic order. -/
def lengthFirstLt (a b : List UInt8) : Bool :=
  if a.length < b.length then true
  else if a.length = b.length then lexLt a b
  else false

theorem lengthFirstLt_iff (a b : List UInt8) :
    lengthFirstLt a b = true ↔ a.length < b.length ∨ (a.length = b.length ∧ lexLt a b = true) := by
  unfold lengthFirstLt
  split
  · rename_i h; simp [h]
  · split
    · rename_i h1 h2; simp [h2]
    · rename_i h1 h2; simp [h1, h2]

theorem lengthFirstLt_irrefl (a : List UInt8) : lengthFirstLt a a = false := by
  simp [lengthFirstLt, lexLt_irrefl]

theorem lengthFirstLt_asymm {a b : List UInt8} (h : lengthFirstLt a b = true) :
    lengthFirstLt b a = false := by
  rw [lengthFirstLt_iff] at h
  cases hba : lengthFirstLt b a
  · rfl
  · rw [lengthFirstLt_iff] at hba
    rcases h with h | ⟨hl, h⟩ <;> rcases hba with h' | ⟨hl', h'⟩
    · omega
    · omega
    · omega
    · rw [lexLt_asymm h] at h'; exact h'.symm

theorem lengthFirstLt_trans {a b c : List UInt8} (h1 : lengthFirstLt a b = true)
    (h2 : lengthFirstLt b c = true) : lengthFirstLt a c = true := by
  rw [lengthFirstLt_iff] at h1 h2 ⊢
  rcases h1 with h1 | ⟨hl1, h1⟩ <;> rcases h2 with h2 | ⟨hl2, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, lexLt_trans h1 h2⟩

theorem lengthFirstLt_total {a b : List UInt8} (h : a ≠ b) :
    lengthFirstLt a b = true ∨ lengthFirstLt b a = true := by
  rw [lengthFirstLt_iff, lengthFirstLt_iff]
  by_cases hl : a.length = b.length
  · rcases lexLt_total h with h' | h'
    · exact Or.inl (Or.inr ⟨hl, h'⟩)
    · exact Or.inr (Or.inr ⟨hl.symm, h'⟩)
  · by_cases hlt : a.length < b.length
    · exact Or.inl (Or.inl hlt)
    · exact Or.inr (Or.inl (by omega))

theorem lengthFirstLt_neg_trans {a b c : List UInt8} (hab : lengthFirstLt a b = false)
    (hbc : lengthFirstLt b c = false) : lengthFirstLt a c = false := by
  cases hac : lengthFirstLt a c
  · rfl
  · exfalso
    by_cases heq : a = b
    · subst heq; rw [hac] at hbc; exact Bool.noConfusion hbc
    · rcases lengthFirstLt_total heq with h | h
      · rw [h] at hab; exact Bool.noConfusion hab
      · rw [lengthFirstLt_trans h hac] at hbc; exact Bool.noConfusion hbc

/-! ## CTAP2 canonical CBOR byte order (FIDO CTAP2 §6; RFC 8949 §4.2.3) -/

/-- Major type of an encoded CBOR item from its initial byte (`b >>> 5`, §3). -/
def wireMajor : List UInt8 → Nat
  | [] => 0
  | b :: _ => b.toNat / 32

/-- CTAP2 canonical CBOR map key order (FIDO CTAP2 §6; RFC 8949 §4.2.3):
compare major type first, then encoded byte length, then bytewise lexical
order. -/
def ctap2Lt (a b : List UInt8) : Bool :=
  if wireMajor a < wireMajor b then true
  else if wireMajor a = wireMajor b then lengthFirstLt a b
  else false

theorem ctap2Lt_iff (a b : List UInt8) :
    ctap2Lt a b = true ↔
      wireMajor a < wireMajor b ∨ (wireMajor a = wireMajor b ∧ lengthFirstLt a b = true) := by
  unfold ctap2Lt
  split
  · rename_i h; simp [h]
  · split
    · rename_i h1 h2; simp [h2]
    · rename_i h1 h2; simp [h1, h2]

theorem ctap2Lt_irrefl (a : List UInt8) : ctap2Lt a a = false := by
  simp [ctap2Lt, lengthFirstLt_irrefl]

theorem ctap2Lt_asymm {a b : List UInt8} (h : ctap2Lt a b = true) : ctap2Lt b a = false := by
  rw [ctap2Lt_iff] at h
  cases hba : ctap2Lt b a
  · rfl
  · rw [ctap2Lt_iff] at hba
    rcases h with h | ⟨hm, h⟩ <;> rcases hba with h' | ⟨hm', h'⟩
    · omega
    · omega
    · omega
    · rw [lengthFirstLt_asymm h] at h'; exact h'.symm

theorem ctap2Lt_trans {a b c : List UInt8} (h1 : ctap2Lt a b = true) (h2 : ctap2Lt b c = true) :
    ctap2Lt a c = true := by
  rw [ctap2Lt_iff] at h1 h2 ⊢
  rcases h1 with h1 | ⟨hm1, h1⟩ <;> rcases h2 with h2 | ⟨hm2, h2⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, lengthFirstLt_trans h1 h2⟩

theorem ctap2Lt_total {a b : List UInt8} (h : a ≠ b) :
    ctap2Lt a b = true ∨ ctap2Lt b a = true := by
  rw [ctap2Lt_iff, ctap2Lt_iff]
  by_cases hm : wireMajor a = wireMajor b
  · rcases lengthFirstLt_total h with h' | h'
    · exact Or.inl (Or.inr ⟨hm, h'⟩)
    · exact Or.inr (Or.inr ⟨hm.symm, h'⟩)
  · by_cases hlt : wireMajor a < wireMajor b
    · exact Or.inl (Or.inl hlt)
    · exact Or.inr (Or.inl (by omega))

theorem ctap2Lt_neg_trans {a b c : List UInt8} (hab : ctap2Lt a b = false)
    (hbc : ctap2Lt b c = false) : ctap2Lt a c = false := by
  cases hac : ctap2Lt a c
  · rfl
  · exfalso
    by_cases heq : a = b
    · subst heq; rw [hac] at hbc; exact Bool.noConfusion hbc
    · rcases ctap2Lt_total heq with h | h
      · rw [h] at hab; exact Bool.noConfusion hab
      · rw [ctap2Lt_trans h hac] at hbc; exact Bool.noConfusion hbc

/-! ## Stable insertion sort -/

/-- Insert `x` before the first element that does not sort strictly before it. -/
def insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt y x then y :: insertBy lt x ys else x :: y :: ys

/-- Stable insertion sort. -/
def sortBy {α : Type} (lt : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => insertBy lt x (sortBy lt xs)

theorem insertBy_perm {α : Type} (lt : α → α → Bool) (x : α) :
    ∀ l : List α, (insertBy lt x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    simp only [insertBy]
    split
    · exact ((insertBy_perm lt x ys).cons y).trans (List.Perm.swap x y ys)
    · exact List.Perm.refl _

theorem sortBy_perm {α : Type} (lt : α → α → Bool) : ∀ l : List α, (sortBy lt l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertBy_perm lt x _).trans ((sortBy_perm lt xs).cons x)

theorem sortBy_length {α : Type} (lt : α → α → Bool) (l : List α) :
    (sortBy lt l).length = l.length :=
  (sortBy_perm lt l).length_eq

/-- A list is sorted for `lt` when no element sorts strictly before an
earlier one. -/
def SortedBy {α : Type} (lt : α → α → Bool) : List α → Prop
  | [] => True
  | x :: xs => (∀ y ∈ xs, lt y x = false) ∧ SortedBy lt xs

theorem insertBy_of_sorted {α : Type} (lt : α → α → Bool) (x : α) :
    ∀ l : List α, (∀ y ∈ l, lt y x = false) → insertBy lt x l = x :: l
  | [] => fun _ => rfl
  | y :: ys => fun h => by simp [insertBy, h y (by simp)]

theorem sortBy_of_sorted {α : Type} (lt : α → α → Bool) :
    ∀ l : List α, SortedBy lt l → sortBy lt l = l
  | [] => fun _ => rfl
  | x :: xs => fun ⟨hx, hxs⟩ => by
    simp only [sortBy, sortBy_of_sorted lt xs hxs]
    exact insertBy_of_sorted lt x xs hx

theorem sortBy_congr {α : Type} {lt₁ lt₂ : α → α → Bool} :
    ∀ l : List α, (∀ a ∈ l, ∀ b ∈ l, lt₁ a b = lt₂ a b) → sortBy lt₁ l = sortBy lt₂ l
  | [] => fun _ => rfl
  | x :: xs => fun h => by
    simp only [sortBy]
    rw [sortBy_congr xs (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))]
    have hp := (sortBy_perm lt₂ xs)
    generalize sortBy lt₂ xs = m at hp
    have hm : ∀ y ∈ m, lt₁ y x = lt₂ y x := fun y hy =>
      h y (by simp [hp.mem_iff.1 hy]) x (by simp)
    clear hp
    induction m with
    | nil => rfl
    | cons y ys ih =>
      simp only [insertBy, hm y (by simp)]
      split
      · rw [ih (fun z hz => hm z (by simp [hz]))]
      · rfl

theorem sortBy_map {α β : Type} (lt : β → β → Bool) (f : α → β) :
    ∀ l : List α, sortBy lt (l.map f) = (sortBy (fun a b => lt (f a) (f b)) l).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, sortBy, sortBy_map lt f xs]
    generalize sortBy (fun a b => lt (f a) (f b)) xs = m
    induction m with
    | nil => rfl
    | cons y ys ih => simp only [List.map_cons, insertBy]; split <;> simp [ih]

theorem sortedBy_insertBy {α : Type} (lt : α → α → Bool)
    (hasym : ∀ {a b}, lt a b = true → lt b a = false)
    (hneg : ∀ {a b c}, lt a b = false → lt b c = false → lt a c = false)
    (x : α) : ∀ {l : List α}, SortedBy lt l → SortedBy lt (insertBy lt x l)
  | [], _ => ⟨by simp, trivial⟩
  | y :: ys, ⟨hy, hys⟩ => by
    simp only [insertBy]
    split
    · rename_i hyx
      refine ⟨fun z hz => ?_, sortedBy_insertBy lt hasym hneg x hys⟩
      have hmem := (insertBy_perm lt x ys).mem_iff.1 hz
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hz'
      · exact hasym hyx
      · exact hy z hz'
    · rename_i hyx
      have hyx' : lt y x = false := Bool.eq_false_iff.2 hyx
      refine ⟨fun z hz => ?_, ⟨hy, hys⟩⟩
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz'
      · exact hyx'
      · exact hneg (hy z hz') hyx'

theorem sortedBy_sortBy {α : Type} (lt : α → α → Bool)
    (hasym : ∀ {a b}, lt a b = true → lt b a = false)
    (hneg : ∀ {a b c}, lt a b = false → lt b c = false → lt a c = false) :
    ∀ l : List α, SortedBy lt (sortBy lt l)
  | [] => trivial
  | x :: xs => sortedBy_insertBy lt hasym hneg x (sortedBy_sortBy lt hasym hneg xs)

theorem sortBy_idem {α : Type} (lt : α → α → Bool)
    (hasym : ∀ {a b}, lt a b = true → lt b a = false)
    (hneg : ∀ {a b c}, lt a b = false → lt b c = false → lt a c = false)
    (l : List α) : sortBy lt (sortBy lt l) = sortBy lt l :=
  sortBy_of_sorted lt _ (sortedBy_sortBy lt hasym hneg l)

end Cbor.Rfc8949
