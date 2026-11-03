/-
Copyright (c) 2026 Derek Blair. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/

/-!
# Bytewise lexicographic order and stable insertion sort

§4.2.1 sorts map keys "in the bytewise lexicographic order of their
deterministic encodings". `lexLt` is that order on byte strings (a proper
prefix sorts first, which never matters for well-formed encodings because
they are prefix-free). It is a strict total order; `sortBy` is a stable
insertion sort, written with structural recursion so the kernel can run it.
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

end Cbor.Rfc8949
