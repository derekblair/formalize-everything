import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Garling.Chapter01
import Garling.Chapter02
import Garling.Chapter03
import Garling.Chapter04
import Garling.Chapter05

/-!
# Chapter 6: Ruler-and-compass constructions

Formalization of Chapter 6 ("Ruler-and-compass constructions", printed pp. 54–58 / PDF pp. 62–66) of
D. J. H. Garling, *A Course in Galois Theory* (Cambridge University Press, 1986):

- **§6.1 Constructible points** (printed pp. 54–57, PDF pp. 62–65):
  coordinates/*coefficients* of a point relative to `P₀ = (0, 0)` and `P₁ = (1, 0)`, definition of
  *constructible* point via straight-line and circle intersections `(i)`–`(iii)`, associated field
  extension `ℚ(x, y) : ℚ`, `Theorem 6.1`, and `Exercises 6.1`–`6.4`.
- **§6.2 The angle `π/3` cannot be trisected** (printed p. 57, PDF p. 65):
  unnumbered main-text prose proof of the impossibility of trisecting `π/3`, and
  `Exercises 6.5`–`6.6`.
- **§6.3 Concluding remarks** (printed p. 58, PDF p. 66):
  `Exercise 6.7` (parts `(a)` and `(b)`).
-/

namespace Garling.Chapter06

open scoped Polynomial
open Garling.Chapter01 Garling.Chapter02 Garling.Chapter03 Garling.Chapter04 Garling.Chapter05

/-! ## §6.1 Constructible points (printed pp. 54–57, PDF pp. 62–65) -/

/-- Each point in the Euclidean plane is identified with `(x, y) ∈ ℝ × ℝ` relative to the fixed
origin `P₀ = (0, 0)` and unit first-axis point `P₁ = (1, 0)` (§6.1, printed p. 54 / PDF p. 62). -/
abbrev PlanePoint : Type := ℝ × ℝ

/-- Fixed origin `P₀ = (0, 0)` (§6.1, printed p. 54 / PDF p. 62). -/
def P₀ : PlanePoint := (0, 0)

/-- Fixed unit first-axis point `P₁ = (1, 0)` (§6.1, printed p. 54 / PDF p. 62). -/
def P₁ : PlanePoint := (1, 0)

/-- First *coefficient* `x` of a point `(x, y) ∈ ℝ × ℝ` (§6.1, printed p. 54 / PDF p. 62). -/
def firstCoeff (P : PlanePoint) : ℝ := P.1

/-- Second *coefficient* `y` of a point `(x, y) ∈ ℝ × ℝ` (§6.1, printed p. 54 / PDF p. 62). -/
def secondCoeff (P : PlanePoint) : ℝ := P.2

/-- Squared Euclidean distance `(a₁ - a₂)² + (b₁ - b₂)²` between two points in `ℝ × ℝ`
(§6.1, printed p. 55 / PDF p. 63). -/
def sqDist (A B : PlanePoint) : ℝ :=
  (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2

/-- Euclidean distance `√((a₁ - a₂)² + (b₁ - b₂)²)` in `ℝ × ℝ` (§6.1, pp. 54–55). -/
noncomputable def euclidDist (A B : PlanePoint) : ℝ :=
  Real.sqrt (sqDist A B)

theorem sqDist_nonneg (A B : PlanePoint) : 0 ≤ sqDist A B := by
  dsimp [sqDist]
  positivity

theorem sqDist_comm (A B : PlanePoint) : sqDist A B = sqDist B A := by
  dsimp [sqDist]
  ring

theorem sqDist_eq_zero_iff {A B : PlanePoint} : sqDist A B = 0 ↔ A = B := by
  constructor
  · intro h
    dsimp [sqDist] at h
    have h1 : A.1 - B.1 = 0 := by nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2)]
    have h2 : A.2 - B.2 = 0 := by nlinarith [sq_nonneg (A.1 - B.1), sq_nonneg (A.2 - B.2)]
    ext <;> linarith
  · rintro rfl
    dsimp [sqDist]
    ring

theorem sqDist_pos_iff {A B : PlanePoint} : 0 < sqDist A B ↔ A ≠ B := by
  constructor
  · intro hp hEq
    rw [sqDist_eq_zero_iff.mpr hEq] at hp
    linarith
  · intro hne
    have h0 : sqDist A B ≠ 0 := mt sqDist_eq_zero_iff.mp hne
    exact lt_of_le_of_ne (sqDist_nonneg A B) h0.symm

theorem euclidDist_nonneg (A B : PlanePoint) : 0 ≤ euclidDist A B :=
  Real.sqrt_nonneg _

theorem euclidDist_sq (A B : PlanePoint) : euclidDist A B ^ 2 = sqDist A B :=
  Real.sq_sqrt (sqDist_nonneg A B)

/-- Garling's straight line joining `A = (a₁, b₁)` and `B = (a₂, b₂)` (§6.1, printed p. 55 /
PDF p. 63): `{(x, y) | (x - a₂)(b₁ - b₂) = (a₁ - a₂)(y - b₂)}`. -/
def garlingLine (A B : PlanePoint) : Set PlanePoint :=
  {P : PlanePoint | (P.1 - B.1) * (A.2 - B.2) = (A.1 - B.1) * (P.2 - B.2)}

theorem mem_garlingLine_left (A B : PlanePoint) : A ∈ garlingLine A B := by
  simp [garlingLine]

theorem mem_garlingLine_right (A B : PlanePoint) : B ∈ garlingLine A B := by
  simp [garlingLine]

theorem garlingLine_comm (A B : PlanePoint) : garlingLine A B = garlingLine B A := by
  ext P
  dsimp [garlingLine]
  constructor <;> intro h <;> linear_combination -h

/-- Two distinct points `P ≠ Q` lying on `garlingLine A B` (with `A ≠ B`) determine the exact same
straight line `garlingLine P Q = garlingLine A B`. -/
theorem garlingLine_eq_of_mem {A B P Q : PlanePoint} (hAB : A ≠ B) (hPQ : P ≠ Q)
    (hP : P ∈ garlingLine A B) (hQ : Q ∈ garlingLine A B) :
    garlingLine P Q = garlingLine A B := by
  dsimp [garlingLine] at hP hQ
  have hAB_nz : sqDist A B ≠ 0 := mt sqDist_eq_zero_iff.mp hAB
  have hPQ_nz : sqDist P Q ≠ 0 := mt sqDist_eq_zero_iff.mp hPQ
  ext X
  dsimp [garlingLine]
  have hrel : (P.1 - Q.1) * (A.2 - B.2) = (A.1 - B.1) * (P.2 - Q.2) := by
    linear_combination hP - hQ
  constructor
  · intro hX
    have h1 : (P.1 - Q.1) * ((X.1 - Q.1) * (A.2 - B.2) - (A.1 - B.1) * (X.2 - Q.2)) = 0 := by
      linear_combination (X.1 - Q.1) * hrel + (A.1 - B.1) * hX
    have h2 : (P.2 - Q.2) * ((X.1 - Q.1) * (A.2 - B.2) - (A.1 - B.1) * (X.2 - Q.2)) = 0 := by
      linear_combination (X.2 - Q.2) * hrel + (A.2 - B.2) * hX
    have hsq : sqDist P Q * ((X.1 - Q.1) * (A.2 - B.2) - (A.1 - B.1) * (X.2 - Q.2)) = 0 := by
      dsimp [sqDist]
      linear_combination (P.1 - Q.1) * h1 + (P.2 - Q.2) * h2
    have h0 := (mul_eq_zero.mp hsq).resolve_left hPQ_nz
    linarith
  · intro hX
    have hX_Q : (X.1 - Q.1) * (A.2 - B.2) = (A.1 - B.1) * (X.2 - Q.2) := by
      linear_combination hX - hQ
    have h1 : (A.1 - B.1) * ((X.1 - Q.1) * (P.2 - Q.2) - (P.1 - Q.1) * (X.2 - Q.2)) = 0 := by
      linear_combination (P.1 - Q.1) * hX_Q - (X.1 - Q.1) * hrel
    have h2 : (A.2 - B.2) * ((X.1 - Q.1) * (P.2 - Q.2) - (P.1 - Q.1) * (X.2 - Q.2)) = 0 := by
      linear_combination (P.2 - Q.2) * hX_Q - (X.2 - Q.2) * hrel
    have hsq : sqDist A B * ((X.1 - Q.1) * (P.2 - Q.2) - (P.1 - Q.1) * (X.2 - Q.2)) = 0 := by
      dsimp [sqDist]
      linear_combination (A.1 - B.1) * h1 + (A.2 - B.2) * h2
    have h0 := (mul_eq_zero.mp hsq).resolve_left hAB_nz
    linarith

/-- A straight line joining two (distinct) points of `S` (§6.1, pp. 54–55). -/
def IsLineFrom (S : Set PlanePoint) (L : Set PlanePoint) : Prop :=
  ∃ A ∈ S, ∃ B ∈ S, A ≠ B ∧ L = garlingLine A B

/-- Any two distinct straight lines `L₁ ≠ L₂` meet in at most one point; hence if `P ∈ L₁ ∩ L₂`,
`P` is uniquely *"the intersection of two distinct straight lines"* (`L₁ ∩ L₂ = {P}`, §6.1(i)). -/
theorem inter_eq_singleton_of_distinct_lines {S₁ S₂ L₁ L₂ : Set PlanePoint} {P : PlanePoint}
    (hL₁ : IsLineFrom S₁ L₁) (hL₂ : IsLineFrom S₂ L₂) (hne : L₁ ≠ L₂)
    (hP₁ : P ∈ L₁) (hP₂ : P ∈ L₂) :
    L₁ ∩ L₂ = {P} := by
  rcases hL₁ with ⟨A₁, _, B₁, _, hAB₁, rfl⟩
  rcases hL₂ with ⟨A₂, _, B₂, _, hAB₂, rfl⟩
  ext Q
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hQ₁, hQ₂⟩
    by_contra hQP
    have heq1 := garlingLine_eq_of_mem hAB₁ hQP hQ₁ hP₁
    have heq2 := garlingLine_eq_of_mem hAB₂ hQP hQ₂ hP₂
    exact hne (heq1.symm.trans heq2)
  · rintro rfl
    exact ⟨hP₁, hP₂⟩

/-- Garling's circle with centre `C = (a₁, b₁)` and radius the distance between `R₁ = (a₂, b₂)` and
`R₂ = (a₃, b₃)` (§6.1, printed p. 55 bottom / PDF p. 63):
`{(x, y) | (x - a₁)² + (y - b₁)² = (a₂ - a₃)² + (b₂ - b₃)²}`. -/
def garlingCircle (C R₁ R₂ : PlanePoint) : Set PlanePoint :=
  {P : PlanePoint | (P.1 - C.1) ^ 2 + (P.2 - C.2) ^ 2 = (R₁.1 - R₂.1) ^ 2 + (R₁.2 - R₂.2) ^ 2}

theorem mem_garlingCircle_iff_sqDist {P C R₁ R₂ : PlanePoint} :
    P ∈ garlingCircle C R₁ R₂ ↔ sqDist P C = sqDist R₁ R₂ :=
  Iff.rfl

theorem mem_garlingCircle_iff_euclidDist {P C R₁ R₂ : PlanePoint} :
    P ∈ garlingCircle C R₁ R₂ ↔ euclidDist P C = euclidDist R₁ R₂ := by
  rw [mem_garlingCircle_iff_sqDist]
  constructor
  · intro h
    dsimp [euclidDist]
    rw [h]
  · intro h
    rw [← euclidDist_sq P C, ← euclidDist_sq R₁ R₂, h]

/-- A circle with centre a point of `S` and positive radius the distance between two distinct
points of `S` (§6.1, p. 55). (See `isConstructible_iff_relaxed` below proving that allowing
zero-radius circles `R₁ = R₂` yields the exact same set of constructible points.) -/
def IsCircleFrom (S : Set PlanePoint) (Cir : Set PlanePoint) : Prop :=
  ∃ C ∈ S, ∃ R₁ ∈ S, ∃ R₂ ∈ S, R₁ ≠ R₂ ∧ Cir = garlingCircle C R₁ R₂

/-- Garling's remark on Case `(iii)` (§6.1, printed p. 55 / PDF p. 63):
*"In case (iii), the centres must be different if the circles are to intersect: the radii may or
may not be different."* -/
theorem distinct_centres_of_distinct_intersecting_circles
    {C₁ R₁ R₂ C₂ T₁ T₂ P : PlanePoint}
    (hne : garlingCircle C₁ R₁ R₂ ≠ garlingCircle C₂ T₁ T₂)
    (hP₁ : P ∈ garlingCircle C₁ R₁ R₂)
    (hP₂ : P ∈ garlingCircle C₂ T₁ T₂) :
    C₁ ≠ C₂ := by
  rintro rfl
  apply hne
  ext Q
  dsimp [garlingCircle] at hP₁ hP₂ ⊢
  rw [← hP₁, ← hP₂]

/-- Single-step ruler-and-compass generation from `S` via clauses `(i)`, `(ii)`, or `(iii)`
(§6.1, printed p. 55 / PDF p. 63). -/
def IsOneStepFrom (S : Set PlanePoint) (P : PlanePoint) : Prop :=
  (∃ L₁ L₂, IsLineFrom S L₁ ∧ IsLineFrom S L₂ ∧ L₁ ≠ L₂ ∧ P ∈ L₁ ∧ P ∈ L₂) ∨
  (∃ L Cir, IsLineFrom S L ∧ IsCircleFrom S Cir ∧ P ∈ L ∧ P ∈ Cir) ∨
  (∃ Cir₁ Cir₂, IsCircleFrom S Cir₁ ∧ IsCircleFrom S Cir₂ ∧ Cir₁ ≠ Cir₂ ∧ P ∈ Cir₁ ∧ P ∈ Cir₂)

theorem isLineFrom_mono {S₁ S₂ : Set PlanePoint} (h : S₁ ⊆ S₂) {L : Set PlanePoint}
    (hL : IsLineFrom S₁ L) : IsLineFrom S₂ L := by
  rcases hL with ⟨A, hA, B, hB, hAB, rfl⟩
  exact ⟨A, h hA, B, h hB, hAB, rfl⟩

theorem isCircleFrom_mono {S₁ S₂ : Set PlanePoint} (h : S₁ ⊆ S₂) {Cir : Set PlanePoint}
    (hC : IsCircleFrom S₁ Cir) : IsCircleFrom S₂ Cir := by
  rcases hC with ⟨C, hCs, R₁, hR₁, R₂, hR₂, hne, rfl⟩
  exact ⟨C, h hCs, R₁, h hR₁, R₂, h hR₂, hne, rfl⟩

theorem isOneStepFrom_mono {S₁ S₂ : Set PlanePoint} (h : S₁ ⊆ S₂) {P : PlanePoint}
    (hP : IsOneStepFrom S₁ P) : IsOneStepFrom S₂ P := by
  rcases hP with ⟨L₁, L₂, h1, h2, hne, hp1, hp2⟩ |
      ⟨L, Cir, hL, hC, hp1, hp2⟩ |
      ⟨C₁, C₂, h1, h2, hne, hp1, hp2⟩
  · exact Or.inl ⟨L₁, L₂, isLineFrom_mono h h1, isLineFrom_mono h h2, hne, hp1, hp2⟩
  · exact Or.inr (Or.inl ⟨L, Cir, isLineFrom_mono h hL, isCircleFrom_mono h hC, hp1, hp2⟩)
  · exact Or.inr (Or.inr ⟨C₁, C₂, isCircleFrom_mono h h1, isCircleFrom_mono h h2, hne, hp1, hp2⟩)

/-- Prefix set `S_j = {P_0, P_1, ..., P_j}` of a finite point sequence `P_0, ..., P_n`
(§6.1, printed p. 55 / PDF p. 63). -/
def prefixPointSet {n : ℕ} (seq : Fin (n + 1) → PlanePoint) (j : ℕ) : Set PlanePoint :=
  {Q : PlanePoint | ∃ i : Fin (n + 1), (i : ℕ) ≤ j ∧ seq i = Q}

/-- A valid ruler-and-compass construction sequence `P_0, P_1, ..., P_n` (`1 ≤ n`) starting at the
fixed base points `P₀ = (0, 0)` and `P₁ = (1, 0)` (§6.1, printed pp. 54–55 / PDF pp. 62–63). -/
def IsConstructionSeq {n : ℕ} (hn : 1 ≤ n) (seq : Fin (n + 1) → PlanePoint) : Prop :=
  seq 0 = P₀ ∧
  seq ⟨1, Nat.lt_succ_of_le hn⟩ = P₁ ∧
  ∀ j : Fin (n + 1), 2 ≤ (j : ℕ) → IsOneStepFrom (prefixPointSet seq ((j : ℕ) - 1)) (seq j)

/-- Garling's definition of a *constructible* point `P ∈ ℝ × ℝ` (§6.1, printed pp. 54–55 /
PDF pp. 62–63): there exists a finite sequence `P_0, P_1, ..., P_n = P` (`1 ≤ n`) satisfying
`IsConstructionSeq`. -/
def IsConstructible (P : PlanePoint) : Prop :=
  ∃ (n : ℕ) (hn : 1 ≤ n) (seq : Fin (n + 1) → PlanePoint),
    IsConstructionSeq hn seq ∧ seq (Fin.last n) = P

/-! ### Sequence concatenation & elementary ruler-and-compass combinators -/

theorem P₀_ne_P₁ : P₀ ≠ P₁ := by
  intro h
  have := congrArg Prod.fst h
  norm_num [P₀, P₁] at this

/-- `P₁ = (1, 0)` is constructible (`n = 1`). -/
theorem isConstructible_P₁ : IsConstructible P₁ := by
  refine ⟨1, le_rfl, ![P₀, P₁], ⟨rfl, rfl, ?_⟩, rfl⟩
  intro j hj
  omega

/-- Append one step `Q` onto a construction sequence `seq` of length `n + 1`. -/
theorem isConstructionSeq_snoc {n : ℕ} (hn : 1 ≤ n) {seq : Fin (n + 1) → PlanePoint}
    (hseq : IsConstructionSeq hn seq) {Q : PlanePoint}
    (hQ : IsOneStepFrom (prefixPointSet seq n) Q) :
    let seq' : Fin (n + 2) → PlanePoint :=
      fun j => if hj : (j : ℕ) < n + 1 then seq ⟨j, hj⟩ else Q
    IsConstructionSeq (by omega : 1 ≤ n + 1) seq' ∧
    seq' (Fin.last (n + 1)) = Q ∧
    prefixPointSet seq n ⊆ prefixPointSet seq' (n + 1) := by
  intro seq'
  have h0 : seq' 0 = P₀ := by
    dsimp [seq']
    exact hseq.1
  have h1 : seq' ⟨1, by omega⟩ = P₁ := by
    change (if hj : (1 : ℕ) < n + 1 then seq ⟨1, hj⟩ else Q) = P₁
    split_ifs with hj
    · exact hseq.2.1
    · omega
  have hpref : ∀ k : ℕ, k ≤ n → prefixPointSet seq k ⊆ prefixPointSet seq' k := by
    rintro k _ X ⟨i, hi, rfl⟩
    refine ⟨⟨i, by omega⟩, hi, ?_⟩
    change (if hj : (i : ℕ) < n + 1 then seq ⟨i, hj⟩ else Q) = seq i
    split_ifs with hj
    · rfl
    · exact absurd i.isLt hj
  refine ⟨⟨h0, h1, ?_⟩, ?_, ?_⟩
  · intro j hj2
    by_cases hj : (j : ℕ) < n + 1
    · change IsOneStepFrom _ (if hj' : (j : ℕ) < n + 1 then seq ⟨j, hj'⟩ else Q)
      split_ifs
      have hstep := hseq.2.2 ⟨j, hj⟩ hj2
      have hle : ((j : ℕ) - 1) ≤ n := by omega
      exact isOneStepFrom_mono (hpref ((j : ℕ) - 1) hle) hstep
    · change IsOneStepFrom _ (if hj' : (j : ℕ) < n + 1 then seq ⟨j, hj'⟩ else Q)
      split_ifs
      have hsub : (j : ℕ) - 1 = n := by omega
      rw [hsub]
      exact isOneStepFrom_mono (hpref n le_rfl) hQ
  · change (if hj : n + 1 < n + 1 then seq ⟨n + 1, hj⟩ else Q) = Q
    split_ifs with hj
    · omega
    · rfl
  · rintro X ⟨i, hi, rfl⟩
    refine ⟨⟨i, by omega⟩, by omega, ?_⟩
    change (if hj : (i : ℕ) < n + 1 then seq ⟨i, hj⟩ else Q) = seq i
    split_ifs with hj
    · rfl
    · exact absurd i.isLt hj

/-- Concatenate two construction sequences so the combined sequence covers both prefixes. -/
theorem exists_constructionSeq_covering_list :
    ∀ (pts : List PlanePoint), (∀ Q ∈ pts, IsConstructible Q) →
      ∃ (n : ℕ) (hn : 1 ≤ n) (seq : Fin (n + 1) → PlanePoint),
        IsConstructionSeq hn seq ∧
        P₀ ∈ prefixPointSet seq n ∧
        P₁ ∈ prefixPointSet seq n ∧
        ∀ Q ∈ pts, Q ∈ prefixPointSet seq n
  | [], _ => by
    refine ⟨1, le_rfl, ![P₀, P₁], ⟨rfl, rfl, fun j hj => by omega⟩, ?_, ?_, ?_⟩
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
    · intro _ h; cases h
  | Q :: rest, hall => by
    obtain ⟨n₁, hn₁, seq₁, hseq₁, hP0, hP1, hrest⟩ :=
      exists_constructionSeq_covering_list rest (fun X hX => hall X (List.mem_cons_of_mem Q hX))
    obtain ⟨m, hm, seqQ, hseqQ, hlastQ⟩ := hall Q (List.mem_cons_self)
    -- Inductively append `seqQ k` for `2 ≤ k ≤ m` onto `seq₁`
    have happend : ∀ k : ℕ, (hk : 1 ≤ k) → k ≤ m →
        ∃ (n' : ℕ) (hn' : 1 ≤ n') (seq' : Fin (n' + 1) → PlanePoint),
          IsConstructionSeq hn' seq' ∧
          prefixPointSet seq₁ n₁ ⊆ prefixPointSet seq' n' ∧
          prefixPointSet seqQ k ⊆ prefixPointSet seq' n' := by
      intro k hk hkm
      induction k with
      | zero => omega
      | succ k' ih =>
        by_cases hk0 : k' = 0
        · subst hk0
          refine ⟨n₁, hn₁, seq₁, hseq₁, Set.Subset.rfl, ?_⟩
          rintro X ⟨i, hi, rfl⟩
          have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
          rcases hi01 with hi0 | hi1
          · have hiz : i = 0 := Fin.ext hi0
            rw [hiz, hseqQ.1]
            exact hP0
          · have hi1' : i = ⟨1, Nat.lt_succ_of_le hm⟩ := Fin.ext hi1
            rw [hi1', hseqQ.2.1]
            exact hP1
        · obtain ⟨n', hn', seq', hseq', hsub1, hsubQ⟩ := ih (by omega) (by omega)
          let idx : Fin (m + 1) := ⟨k' + 1, by omega⟩
          have hstepQ : IsOneStepFrom (prefixPointSet seqQ k') (seqQ idx) :=
            hseqQ.2.2 idx (by change 2 ≤ k' + 1; omega)
          have hstep' : IsOneStepFrom (prefixPointSet seq' n') (seqQ idx) :=
            isOneStepFrom_mono hsubQ hstepQ
          obtain ⟨hsnoc, hlast, hpref'⟩ := isConstructionSeq_snoc hn' hseq' hstep'
          refine ⟨n' + 1, by omega, Fin.snoc seq' (seqQ idx), hsnoc, hsub1.trans hpref', ?_⟩
          rintro X ⟨i, hi, rfl⟩
          by_cases hik : (i : ℕ) ≤ k'
          · exact hpref' (hsubQ ⟨i, hik, rfl⟩)
          · have hieq : i = idx := by ext; dsimp [idx]; omega
            rw [hieq]
            exact ⟨Fin.last (n' + 1), le_rfl, hlast⟩
    obtain ⟨n', hn', seq', hseq', hsub1, hsubQ⟩ := happend m hm le_rfl
    refine ⟨n', hn', seq', hseq', hsub1 hP0, hsub1 hP1, ?_⟩
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hXr
    · rw [← hlastQ]
      exact hsubQ ⟨Fin.last m, le_rfl, rfl⟩
    · exact hsub1 (hrest X hXr)

/-- Fundamental closure rule: if every point in `pts` is constructible and `P` is obtained in one
step from `{P₀, P₁} ∪ pts`, then `P` is constructible. -/
theorem isConstructible_of_oneStep (pts : List PlanePoint)
    (hpts : ∀ Q ∈ pts, IsConstructible Q) {P : PlanePoint}
    (hstep : IsOneStepFrom ({P₀, P₁} ∪ {Q | Q ∈ pts}) P) :
    IsConstructible P := by
  obtain ⟨n, hn, seq, hseq, hP0, hP1, hcov⟩ := exists_constructionSeq_covering_list pts hpts
  have hsub : ({P₀, P₁} ∪ {Q | Q ∈ pts}) ⊆ prefixPointSet seq n := by
    rintro X (h01 | hmem)
    · rcases h01 with rfl | rfl
      · exact hP0
      · exact hP1
    · exact hcov X hmem
  obtain ⟨hsnoc, hlast, _⟩ := isConstructionSeq_snoc hn hseq (isOneStepFrom_mono hsub hstep)
  exact ⟨n + 1, by omega, Fin.snoc seq P, hsnoc, hlast⟩

/-- Rule `(i)` closure: intersection of two distinct lines through constructible point pairs. -/
theorem isConstructible_of_line_line {A₁ B₁ A₂ B₂ P : PlanePoint}
    (hA₁ : IsConstructible A₁) (hB₁ : IsConstructible B₁)
    (hA₂ : IsConstructible A₂) (hB₂ : IsConstructible B₂)
    (hAB₁ : A₁ ≠ B₁) (hAB₂ : A₂ ≠ B₂)
    (hne : garlingLine A₁ B₁ ≠ garlingLine A₂ B₂)
    (hP₁ : P ∈ garlingLine A₁ B₁) (hP₂ : P ∈ garlingLine A₂ B₂) :
    IsConstructible P := by
  refine isConstructible_of_oneStep [A₁, B₁, A₂, B₂] ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl) <;> assumption
  · refine Or.inl ⟨garlingLine A₁ B₁, garlingLine A₂ B₂, ?_, ?_, hne, hP₁, hP₂⟩
    · exact ⟨A₁, by simp, B₁, by simp, hAB₁, rfl⟩
    · exact ⟨A₂, by simp, B₂, by simp, hAB₂, rfl⟩

/-- Rule `(ii)` closure: intersection of a line and a circle determined by constructible points. -/
theorem isConstructible_of_line_circle {A B C R₁ R₂ P : PlanePoint}
    (hA : IsConstructible A) (hB : IsConstructible B)
    (hC : IsConstructible C) (hR₁ : IsConstructible R₁) (hR₂ : IsConstructible R₂)
    (hAB : A ≠ B) (hR : R₁ ≠ R₂)
    (hPL : P ∈ garlingLine A B) (hPC : P ∈ garlingCircle C R₁ R₂) :
    IsConstructible P := by
  refine isConstructible_of_oneStep [A, B, C, R₁, R₂] ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> assumption
  · refine Or.inr (Or.inl ⟨garlingLine A B, garlingCircle C R₁ R₂, ?_, ?_, hPL, hPC⟩)
    · exact ⟨A, by simp, B, by simp, hAB, rfl⟩
    · exact ⟨C, by simp, R₁, by simp, R₂, by simp, hR, rfl⟩

/-- Rule `(iii)` closure: intersection of two distinct circles determined by constructible points. -/
theorem isConstructible_of_circle_circle {C₁ R₁ R₂ C₂ T₁ T₂ P : PlanePoint}
    (hC₁ : IsConstructible C₁) (hR₁ : IsConstructible R₁) (hR₂ : IsConstructible R₂)
    (hC₂ : IsConstructible C₂) (hT₁ : IsConstructible T₁) (hT₂ : IsConstructible T₂)
    (hR : R₁ ≠ R₂) (hT : T₁ ≠ T₂)
    (hne : garlingCircle C₁ R₁ R₂ ≠ garlingCircle C₂ T₁ T₂)
    (hP₁ : P ∈ garlingCircle C₁ R₁ R₂) (hP₂ : P ∈ garlingCircle C₂ T₁ T₂) :
    IsConstructible P := by
  refine isConstructible_of_oneStep [C₁, R₁, R₂, C₂, T₁, T₂] ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption
  · refine Or.inr (Or.inr ⟨garlingCircle C₁ R₁ R₂, garlingCircle C₂ T₁ T₂, ?_, ?_, hne, hP₁, hP₂⟩)
    · exact ⟨C₁, by simp, R₁, by simp, R₂, by simp, hR, rfl⟩
    · exact ⟨C₂, by simp, T₁, by simp, T₂, by simp, hT, rfl⟩

/-- Equilateral apex `(1/2, √3/2)` constructed in 1 circle-circle step from `{P₀, P₁}`. -/
theorem isConstructible_equilateral_apex :
    IsConstructible (1 / 2, Real.sqrt 3 / 2) := by
  refine isConstructible_of_oneStep [] (by simp) ?_
  refine Or.inr (Or.inr ⟨garlingCircle P₀ P₀ P₁, garlingCircle P₁ P₀ P₁, ?_, ?_, ?_, ?_, ?_⟩)
  · exact ⟨P₀, by simp, P₀, by simp, P₁, by simp, P₀_ne_P₁, rfl⟩
  · exact ⟨P₁, by simp, P₀, by simp, P₁, by simp, P₀_ne_P₁, rfl⟩
  · intro heq
    have hmem : ((2 : ℝ), (0 : ℝ)) ∈ garlingCircle P₁ P₀ P₁ := by
      dsimp [garlingCircle, P₀, P₁]
      norm_num
    rw [← heq] at hmem
    dsimp [garlingCircle, P₀, P₁] at hmem
    norm_num at hmem
  · dsimp [garlingCircle, P₀, P₁]
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  · dsimp [garlingCircle, P₀, P₁]
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith

/-- `P₀ = (0, 0)` is constructible (at `n = 3`: unit circles around `P₀` and `P₁` give
`Q = (1/2, √3/2)`, and intersecting `P₀P₁` with the circle around `Q` of radius `|QP₀| = 1` gives
`P₀`). -/
theorem isConstructible_P₀ : IsConstructible P₀ := by
  let Q : PlanePoint := (1 / 2, Real.sqrt 3 / 2)
  have hQ : IsConstructible Q := isConstructible_equilateral_apex
  refine isConstructible_of_oneStep [Q] ?_ ?_
  · simp only [List.mem_singleton]
    rintro _ rfl
    exact hQ
  · have hQP₀ : Q ≠ P₀ := by
      intro h
      have := congrArg Prod.fst h
      norm_num [Q, P₀] at this
    refine Or.inr (Or.inl ⟨garlingLine P₀ P₁, garlingCircle Q Q P₀, ?_, ?_, ?_, ?_⟩)
    · exact ⟨P₀, by simp, P₁, by simp, P₀_ne_P₁, rfl⟩
    · exact ⟨Q, by simp, Q, by simp, P₀, by simp, hQP₀, rfl⟩
    · exact mem_garlingLine_left P₀ P₁
    · dsimp [garlingCircle]
      ring

/-- Every point appearing anywhere in a valid construction sequence is constructible. -/
theorem isConstructible_of_mem_prefixPointSet {n : ℕ} {hn : 1 ≤ n}
    {seq : Fin (n + 1) → PlanePoint} (hseq : IsConstructionSeq hn seq)
    {P : PlanePoint} {j : ℕ} (hP : P ∈ prefixPointSet seq j) :
    IsConstructible P := by
  rcases hP with ⟨i, _, rfl⟩
  by_cases hi0 : (i : ℕ) = 0
  · have hiz : i = 0 := Fin.ext hi0
    rw [hiz, hseq.1]
    exact isConstructible_P₀
  · have hi1 : 1 ≤ (i : ℕ) := by omega
    let seq' : Fin ((i : ℕ) + 1) → PlanePoint := fun k => seq ⟨k.1, by omega⟩
    refine ⟨(i : ℕ), hi1, seq', ⟨?_, ?_, ?_⟩, ?_⟩
    · change seq 0 = P₀
      exact hseq.1
    · change seq ⟨1, _⟩ = P₁
      exact hseq.2.1
    · intro k hk2
      have hstep := hseq.2.2 ⟨k.1, by omega⟩ hk2
      refine isOneStepFrom_mono ?_ hstep
      rintro X ⟨m, hm, rfl⟩
      have hm_le : (m : ℕ) ≤ k.1 - 1 := hm
      exact ⟨⟨m.1, by omega⟩, hm_le, rfl⟩
    · dsimp [seq', Fin.last]

/-- Relaxed ruler-and-compass variant allowing `n = 0` (`P_0` in `0` steps) and possibly-zero
circle radii (`R₁ = R₂`). -/
def IsConstructibleRelaxed (P : PlanePoint) : Prop :=
  P = P₀ ∨
  ∃ (n : ℕ) (hn : 1 ≤ n) (seq : Fin (n + 1) → PlanePoint),
    seq 0 = P₀ ∧
    seq ⟨1, Nat.lt_succ_of_le hn⟩ = P₁ ∧
    (∀ j : Fin (n + 1), 2 ≤ (j : ℕ) →
      let S := prefixPointSet seq ((j : ℕ) - 1)
      let IsCirAny (Cir : Set PlanePoint) : Prop :=
        ∃ C ∈ S, ∃ R₁ ∈ S, ∃ R₂ ∈ S, Cir = garlingCircle C R₁ R₂
      (∃ L₁ L₂, IsLineFrom S L₁ ∧ IsLineFrom S L₂ ∧ L₁ ≠ L₂ ∧ seq j ∈ L₁ ∧ seq j ∈ L₂) ∨
      (∃ L Cir, IsLineFrom S L ∧ IsCirAny Cir ∧ seq j ∈ L ∧ seq j ∈ Cir) ∨
      (∃ Cir₁ Cir₂, IsCirAny Cir₁ ∧ IsCirAny Cir₂ ∧ Cir₁ ≠ Cir₂ ∧ seq j ∈ Cir₁ ∧ seq j ∈ Cir₂)) ∧
    seq (Fin.last n) = P

/-- Equivalence confirming that `n ≥ 1` vs `n ≥ 0` and positive-radius vs possibly-zero-radius
circles determine the **exact same** set of constructible points in `ℝ × ℝ`. -/
theorem isConstructible_iff_relaxed (P : PlanePoint) :
    IsConstructible P ↔ IsConstructibleRelaxed P := by
  constructor
  · rintro ⟨n, hn, seq, hseq, rfl⟩
    refine Or.inr ⟨n, hn, seq, hseq.1, hseq.2.1, ?_, rfl⟩
    intro j hj
    rcases hseq.2.2 j hj with ⟨L₁, L₂, h1, h2, hne, hp1, hp2⟩ |
        ⟨L, Cir, hL, ⟨C, hC, R₁, hR₁, R₂, hR₂, _, rfl⟩, hp1, hp2⟩ |
        ⟨Cir₁, Cir₂, ⟨C₁, hC₁, R₁, hR₁, R₂, hR₂, _, rfl⟩,
          ⟨C₂, hC₂, T₁, hT₁, T₂, hT₂, _, rfl⟩, hne, hp1, hp2⟩
    · exact Or.inl ⟨L₁, L₂, h1, h2, hne, hp1, hp2⟩
    · exact Or.inr (Or.inl ⟨L, _, hL, ⟨C, hC, R₁, hR₁, R₂, hR₂, rfl⟩, hp1, hp2⟩)
    · exact Or.inr (Or.inr ⟨_, _, ⟨C₁, hC₁, R₁, hR₁, R₂, hR₂, rfl⟩,
        ⟨C₂, hC₂, T₁, hT₁, T₂, hT₂, rfl⟩, hne, hp1, hp2⟩)
  · rintro (rfl | ⟨n, hn, seq, h0, h1, hsteps, rfl⟩)
    · exact isConstructible_P₀
    · suffices h : ∀ k : ℕ, k ≤ n → ∀ Q ∈ prefixPointSet seq k, IsConstructible Q by
        exact h n le_rfl (seq (Fin.last n)) ⟨Fin.last n, le_rfl, rfl⟩
      intro k hk
      induction k with
      | zero =>
        rintro Q ⟨i, hi, rfl⟩
        have hi0 : (i : ℕ) = 0 := by omega
        have hiz : i = 0 := Fin.ext hi0
        rw [hiz, h0]
        exact isConstructible_P₀
      | succ k' ih =>
        rintro Q ⟨i, hi, rfl⟩
        by_cases hik : (i : ℕ) ≤ k'
        · exact ih (by omega) (seq i) ⟨i, hik, rfl⟩
        · have hieq : (i : ℕ) = k' + 1 := by omega
          by_cases hk0 : k' = 0
          · have hi1_val : (i : ℕ) = 1 := by omega
            have hi1 : i = ⟨1, Nat.lt_succ_of_le hn⟩ := Fin.ext hi1_val
            rw [hi1, h1]
            exact isConstructible_P₁
          · have hi2 : 2 ≤ (i : ℕ) := by omega
            have hprev : ∀ X ∈ prefixPointSet seq ((i : ℕ) - 1), IsConstructible X := by
              have hsub : (i : ℕ) - 1 = k' := by omega
              rw [hsub]
              exact ih (by omega)
            rcases hsteps i hi2 with
                ⟨L₁, L₂, ⟨A₁, hA₁, B₁, hB₁, hAB₁, rfl⟩,
                  ⟨A₂, hA₂, B₂, hB₂, hAB₂, rfl⟩, hne, hp1, hp2⟩ |
                ⟨L, Cir, ⟨A, hA, B, hB, hAB, rfl⟩,
                  ⟨C, hC, R₁, hR₁, R₂, hR₂, rfl⟩, hp1, hp2⟩ |
                ⟨Cir₁, Cir₂, ⟨C₁, hC₁, R₁, hR₁, R₂, hR₂, rfl⟩,
                  ⟨C₂, hC₂, T₁, hT₁, T₂, hT₂, rfl⟩, hne, hp1, hp2⟩
            · exact isConstructible_of_line_line (hprev A₁ hA₁) (hprev B₁ hB₁)
                (hprev A₂ hA₂) (hprev B₂ hB₂) hAB₁ hAB₂ hne hp1 hp2
            · by_cases hR : R₁ = R₂
              · subst hR
                have hPC : seq i = C := by
                  rw [mem_garlingCircle_iff_sqDist, sqDist_eq_zero_iff.mpr rfl,
                    sqDist_eq_zero_iff] at hp2
                  exact hp2
                rw [hPC]
                exact hprev C hC
              · exact isConstructible_of_line_circle (hprev A hA) (hprev B hB)
                  (hprev C hC) (hprev R₁ hR₁) (hprev R₂ hR₂) hAB hR hp1 hp2
            · by_cases hR : R₁ = R₂
              · subst hR
                have hPC : seq i = C₁ := by
                  rw [mem_garlingCircle_iff_sqDist, sqDist_eq_zero_iff.mpr rfl,
                    sqDist_eq_zero_iff] at hp1
                  exact hp1
                rw [hPC]
                exact hprev C₁ hC₁
              · by_cases hT : T₁ = T₂
                · subst hT
                  have hPC : seq i = C₂ := by
                    rw [mem_garlingCircle_iff_sqDist, sqDist_eq_zero_iff.mpr rfl,
                      sqDist_eq_zero_iff] at hp2
                    exact hp2
                  rw [hPC]
                  exact hprev C₂ hC₂
                · exact isConstructible_of_circle_circle
                    (hprev C₁ hC₁) (hprev R₁ hR₁) (hprev R₂ hR₂)
                    (hprev C₂ hC₂) (hprev T₁ hT₁) (hprev T₂ hT₂)
                    hR hT hne hp1 hp2

/-! ### Associated field extension `ℚ(x, y) : ℚ` and **Theorem 6.1** (pp. 55–56) -/

/-- Associated intermediate field `ℚ(x, y)` inside `ℝ : ℚ` generated by the coefficients `x` and `y`
of `P = (x, y)` (§6.1, printed p. 55 / PDF p. 63). -/
noncomputable def ratPointField (x y : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ ({x, y} : Set ℝ)

theorem ratPointField_toSubfield_eq_garlingFieldGenSubfield (x y : ℝ) :
    (ratPointField x y).toSubfield = garlingFieldGenSubfield ℚ ({x, y} : Set ℝ) :=
  (garlingFieldGenSubfield_eq_adjoin ℚ ({x, y} : Set ℝ)).symm

/-- Helper for Case `(ii)` of `Theorem 6.1` (printed p. 56 / PDF p. 64): if `(x, y) ∈ ℝ × ℝ`
satisfies a non-trivial linear equation `λ x + μ y + ν = 0` (`(λ, μ) ≠ (0, 0)`) and a circle
equation `x² + y² + 2gx + 2fy + c = 0` with all coefficients in `F : IntermediateField ℚ ℝ`, then
`F(x, y)` is finite over `F` with `finrank F F(x, y) = 1 ∨ finrank F F(x, y) = 2`. -/
private theorem finrank_adjoin_pair_line_circle (F : IntermediateField ℚ ℝ) {x y : ℝ}
    {lam mu nu g f c : F} (hlin_nz : lam ≠ 0 ∨ mu ≠ 0)
    (hlin : (lam : ℝ) * x + (mu : ℝ) * y + (nu : ℝ) = 0)
    (hcir : x ^ 2 + y ^ 2 + 2 * (g : ℝ) * x + 2 * (f : ℝ) * y + (c : ℝ) = 0) :
    let F' : IntermediateField ℚ ℝ := F ⊔ IntermediateField.adjoin ℚ ({x, y} : Set ℝ)
    let _ : Algebra F F' := (IntermediateField.inclusion le_sup_left).toAlgebra
    Module.Finite F F' ∧ (Module.finrank F F' = 1 ∨ Module.finrank F F' = 2) := by
  -- Core elimination helper: if `u, v ∈ ℝ` satisfy `u = a * v + b` (`a, b ∈ F`) and a quadratic
  -- `(a² + 1) v² + ... = 0` over `F`, then `[F(u, v) : F] ∈ {1, 2}`.
  have helim : ∀ (u v : ℝ) (a b p₁ p₀ : F),
      u = (a : ℝ) * v + (b : ℝ) →
      ((a : ℝ) ^ 2 + 1) * v ^ 2 + (p₁ : ℝ) * v + (p₀ : ℝ) = 0 →
      let E : IntermediateField ℚ ℝ := F ⊔ IntermediateField.adjoin ℚ ({u, v} : Set ℝ)
      let _ : Algebra F E := (IntermediateField.inclusion le_sup_left).toAlgebra
      Module.Finite F E ∧ (Module.finrank F E = 1 ∨ Module.finrank F E = 2) := by
    intro u v a b p₁ p₀ huv hquad E _
    let a₂ : F := a ^ 2 + 1
    have ha₂_pos : (0 : ℝ) < (a₂ : ℝ) := by
      change (0 : ℝ) < (a : ℝ) ^ 2 + 1
      positivity
    let Q : F[X] :=
      Polynomial.X ^ 2 + Polynomial.C (a₂⁻¹ * p₁) * Polynomial.X + Polynomial.C (a₂⁻¹ * p₀)
    have hQ_deg : Q.natDegree = 2 := by
      dsimp [Q]
      compute_degree!
    have hQ_monic : Q.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hQ_deg]
      dsimp [Q]
      simp
    have hQ_aeval : Polynomial.aeval v Q = 0 := by
      have hval : v ^ 2 + (a₂ : ℝ)⁻¹ * (p₁ : ℝ) * v + (a₂ : ℝ)⁻¹ * (p₀ : ℝ) = 0 := by
        have ha₂R : (a₂ : ℝ) ≠ 0 := ne_of_gt ha₂_pos
        have hmul : (a₂ : ℝ) * v ^ 2 + (p₁ : ℝ) * v + (p₀ : ℝ) = 0 := hquad
        field_simp [ha₂R]
        linarith
      dsimp [Q]
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      exact hval
    have hv_int : IsIntegral F v := ⟨Q, hQ_monic, hQ_aeval⟩
    have hdvd : minpoly F v ∣ Q := minpoly.dvd F v hQ_aeval
    have hdeg_le : (minpoly F v).natDegree ≤ 2 :=
      (Polynomial.natDegree_le_of_dvd hdvd hQ_monic.ne_zero).trans (le_of_eq hQ_deg)
    have hdeg_pos : 0 < (minpoly F v).natDegree := minpoly.natDegree_pos hv_int
    let Fv : IntermediateField F ℝ := IntermediateField.adjoin F ({v} : Set ℝ)
    have hFv_fin : Module.Finite F Fv := IntermediateField.adjoin.finiteDimensional hv_int
    have hFv_rank : Module.finrank F Fv = (minpoly F v).natDegree :=
      IntermediateField.adjoin.finrank hv_int
    -- Show `E.toSubfield = Fv.toSubfield`
    have hSub : E.toSubfield = Fv.toSubfield := by
      apply le_antisymm
      · change (F ⊔ IntermediateField.adjoin ℚ ({u, v} : Set ℝ)).toSubfield ≤ Fv.toSubfield
        rw [IntermediateField.sup_toSubfield]
        refine sup_le ?_ ?_
        · intro z hz
          exact Fv.algebraMap_mem ⟨z, hz⟩
        · rw [← garlingFieldGenSubfield_eq_adjoin, garlingFieldGenSubfield]
          refine sInf_le ⟨?_, ?_⟩
          · rintro _ ⟨q, rfl⟩
            change (q : ℝ) ∈ Fv.toSubfield
            exact SubfieldClass.ratCast_mem Fv.toSubfield q
          · intro w hw
            rcases Set.mem_insert_iff.mp hw with rfl | hw'
            · rw [huv]
              exact Fv.toSubfield.add_mem
                (Fv.toSubfield.mul_mem (Fv.algebraMap_mem a)
                  (IntermediateField.subset_adjoin F _ (by simp)))
                (Fv.algebraMap_mem b)
            · rw [Set.mem_singleton_iff.mp hw']
              exact IntermediateField.subset_adjoin F _ (by simp)
      · intro z hz
        have hF_le : F.toSubfield ≤ E.toSubfield :=
          show F ≤ E from le_sup_left
        have hv_mem : v ∈ E := by
          have : v ∈ IntermediateField.adjoin ℚ ({u, v} : Set ℝ) :=
            IntermediateField.subset_adjoin ℚ ({u, v} : Set ℝ) (by simp)
          exact (le_sup_right : IntermediateField.adjoin ℚ ({u, v} : Set ℝ) ≤ E) this
        have hFv_le : Fv ≤
            { E.toSubfield with
              algebraMap_mem' := fun k => hF_le k.2 } := by
          rw [IntermediateField.adjoin_le_iff]
          rintro _ rfl
          exact hv_mem
        exact hFv_le hz
    have hmem_iff : ∀ w : ℝ, w ∈ Fv ↔ w ∈ E := fun w =>
      (SetLike.ext_iff.mp hSub w).symm
    let _ : Algebra F E := (IntermediateField.inclusion le_sup_left).toAlgebra
    let eAlg : Fv ≃ₐ[F] E :=
      { toFun := fun z => ⟨z.1, (hmem_iff z.1).mp z.2⟩
        invFun := fun z => ⟨z.1, (hmem_iff z.1).mpr z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    have hE_fin : Module.Finite F E := Module.Finite.equiv eAlg.toLinearEquiv
    have hE_rank : Module.finrank F E = Module.finrank F Fv :=
      (LinearEquiv.finrank_eq eAlg.toLinearEquiv).symm
    refine ⟨hE_fin, ?_⟩
    rw [hE_rank, hFv_rank]
    omega
  rcases hlin_nz with hlam | hmu
  · -- Case `λ ≠ 0`: eliminate `x = (-λ⁻¹ μ) y + (-λ⁻¹ ν)`
    let a : F := -lam⁻¹ * mu
    let b : F := -lam⁻¹ * nu
    have hx : x = (a : ℝ) * y + (b : ℝ) := by
      have hlamR : (lam : ℝ) ≠ 0 := fun hz => hlam (Subtype.ext hz)
      dsimp [a, b]
      field_simp [hlamR]
      linarith
    let p₁ : F := (1 + 1) * a * b + (1 + 1) * g * a + (1 + 1) * f
    let p₀ : F := b ^ 2 + (1 + 1) * g * b + c
    have hquad : ((a : ℝ) ^ 2 + 1) * y ^ 2 + (p₁ : ℝ) * y + (p₀ : ℝ) = 0 := by
      dsimp [p₁, p₀]
      linear_combination (hx ▸ hcir : ((a : ℝ) * y + (b : ℝ)) ^ 2 + y ^ 2 +
        2 * (g : ℝ) * ((a : ℝ) * y + (b : ℝ)) + 2 * (f : ℝ) * y + (c : ℝ) = 0)
    exact helim x y a b p₁ p₀ hx hquad
  · -- Case `μ ≠ 0`: eliminate `y = (-μ⁻¹ λ) x + (-μ⁻¹ ν)`
    let a : F := -mu⁻¹ * lam
    let b : F := -mu⁻¹ * nu
    have hy : y = (a : ℝ) * x + (b : ℝ) := by
      have hmuR : (mu : ℝ) ≠ 0 := fun hz => hmu (Subtype.ext hz)
      dsimp [a, b]
      field_simp [hmuR]
      linarith
    let p₁ : F := (1 + 1) * a * b + (1 + 1) * f * a + (1 + 1) * g
    let p₀ : F := b ^ 2 + (1 + 1) * f * b + c
    have hquad : ((a : ℝ) ^ 2 + 1) * x ^ 2 + (p₁ : ℝ) * x + (p₀ : ℝ) = 0 := by
      dsimp [p₁, p₀]
      linear_combination (hy ▸ hcir : x ^ 2 + ((a : ℝ) * x + (b : ℝ)) ^ 2 +
        2 * (g : ℝ) * x + 2 * (f : ℝ) * ((a : ℝ) * x + (b : ℝ)) + (c : ℝ) = 0)
    have hpair : ({y, x} : Set ℝ) = {x, y} := Set.pair_comm y x
    have hres := helim y x a b p₁ p₀ hy hquad
    dsimp only at hres ⊢
    rwa [hpair] at hres

/-- Single-step degree bound from the proof of `Theorem 6.1` (printed pp. 55–56 / PDF pp. 63–64):
if every point in `S` has coordinates in `F : IntermediateField ℚ ℝ` and `IsOneStepFrom S P`, then
`[F(P.1, P.2) : F] = 1` or `2`. -/
private theorem finrank_step_one_or_two (F : IntermediateField ℚ ℝ) {S : Set PlanePoint}
    (hS : ∀ Q ∈ S, Q.1 ∈ F ∧ Q.2 ∈ F) {P : PlanePoint} (hstep : IsOneStepFrom S P) :
    let F' : IntermediateField ℚ ℝ := F ⊔ IntermediateField.adjoin ℚ ({P.1, P.2} : Set ℝ)
    let _ : Algebra F F' := (IntermediateField.inclusion le_sup_left).toAlgebra
    Module.Finite F F' ∧ (Module.finrank F F' = 1 ∨ Module.finrank F F' = 2) := by
  have hline_eq : ∀ {L : Set PlanePoint}, IsLineFrom S L →
      ∃ (lam mu nu : F), (lam ≠ 0 ∨ mu ≠ 0) ∧
        L = {Q : PlanePoint | (lam : ℝ) * Q.1 + (mu : ℝ) * Q.2 + (nu : ℝ) = 0} := by
    rintro L ⟨A, hA, B, hB, hAB, rfl⟩
    obtain ⟨hA1, hA2⟩ := hS A hA
    obtain ⟨hB1, hB2⟩ := hS B hB
    let lam : F := ⟨A.2 - B.2, F.sub_mem hA2 hB2⟩
    let mu : F := ⟨-(A.1 - B.1), F.neg_mem (F.sub_mem hA1 hB1)⟩
    let nu : F := ⟨-B.1 * (A.2 - B.2) + (A.1 - B.1) * B.2,
      F.add_mem (F.mul_mem (F.neg_mem hB1) (F.sub_mem hA2 hB2))
        (F.mul_mem (F.sub_mem hA1 hB1) hB2)⟩
    refine ⟨lam, mu, nu, ?_, ?_⟩
    · by_contra hboth
      push Not at hboth
      have h1 : A.2 - B.2 = 0 := congrArg Subtype.val hboth.1
      have h2 : -(A.1 - B.1) = 0 := congrArg Subtype.val hboth.2
      apply hAB
      ext <;> linarith
    · ext Q
      dsimp [garlingLine, lam, mu, nu]
      constructor <;> intro h <;> linarith
  have hcir_eq : ∀ {Cir : Set PlanePoint}, IsCircleFrom S Cir →
      ∃ (g f c : F),
        Cir = {Q : PlanePoint |
          Q.1 ^ 2 + Q.2 ^ 2 + 2 * (g : ℝ) * Q.1 + 2 * (f : ℝ) * Q.2 + (c : ℝ) = 0} := by
    rintro Cir ⟨C, hC, R₁, hR₁, R₂, hR₂, _, rfl⟩
    obtain ⟨hC1, hC2⟩ := hS C hC
    obtain ⟨hR11, hR12⟩ := hS R₁ hR₁
    obtain ⟨hR21, hR22⟩ := hS R₂ hR₂
    let g : F := ⟨-C.1, F.neg_mem hC1⟩
    let f : F := ⟨-C.2, F.neg_mem hC2⟩
    let cval : ℝ :=
      C.1 * C.1 + C.2 * C.2 - ((R₁.1 - R₂.1) * (R₁.1 - R₂.1) + (R₁.2 - R₂.2) * (R₁.2 - R₂.2))
    let c : F := ⟨cval,
      F.sub_mem (F.add_mem (F.mul_mem hC1 hC1) (F.mul_mem hC2 hC2))
        (F.add_mem
          (F.mul_mem (F.sub_mem hR11 hR21) (F.sub_mem hR11 hR21))
          (F.mul_mem (F.sub_mem hR12 hR22) (F.sub_mem hR12 hR22)))⟩
    refine ⟨g, f, c, ?_⟩
    ext Q
    change (Q.1 - C.1) ^ 2 + (Q.2 - C.2) ^ 2 = (R₁.1 - R₂.1) ^ 2 + (R₁.2 - R₂.2) ^ 2 ↔
      Q.1 ^ 2 + Q.2 ^ 2 + 2 * (-C.1) * Q.1 + 2 * (-C.2) * Q.2 + cval = 0
    dsimp [cval]
    constructor <;> intro h <;> linear_combination h
  rcases hstep with ⟨L₁, L₂, hL₁, hL₂, hne, hP₁, hP₂⟩ |
      ⟨L, Cir, hL, hC, hPL, hPC⟩ |
      ⟨Cir₁, Cir₂, hC₁, hC₂, hne, hP₁, hP₂⟩
  · -- Case (i): intersection of two distinct straight lines
    obtain ⟨lam₁, mu₁, nu₁, hnz₁, rfl⟩ := hline_eq hL₁
    obtain ⟨lam₂, mu₂, nu₂, hnz₂, rfl⟩ := hline_eq hL₂
    dsimp at hP₁ hP₂
    let det : F := lam₁ * mu₂ - lam₂ * mu₁
    have hdet : (det : ℝ) ≠ 0 := by
      intro hdet0
      apply hne
      dsimp [det] at hdet0
      ext Q
      dsimp
      rcases hnz₁ with hlam₁ | hmu₁
      · have hlam₁R : (lam₁ : ℝ) ≠ 0 := fun hz => hlam₁ (Subtype.ext hz)
        have hmu₂ : (mu₂ : ℝ) = (lam₂ : ℝ) * (mu₁ : ℝ) / (lam₁ : ℝ) := by
          field_simp [hlam₁R]; linarith
        have hnz₂R : (lam₂ : ℝ) ≠ 0 ∨ (mu₂ : ℝ) ≠ 0 :=
          hnz₂.imp (fun h hz => h (Subtype.ext hz)) (fun h hz => h (Subtype.ext hz))
        have hlam₂R : (lam₂ : ℝ) ≠ 0 := by
          rcases hnz₂R with h | h
          · exact h
          · intro hz; rw [hz, zero_mul, zero_div] at hmu₂; exact h hmu₂
        have hnu₂ : (nu₂ : ℝ) = (lam₂ : ℝ) * (nu₁ : ℝ) / (lam₁ : ℝ) := by
          field_simp [hlam₁R]
          linear_combination (lam₁ : ℝ) * hP₂ - (lam₂ : ℝ) * hP₁ - P.2 * hdet0
        constructor <;> intro hQ
        · rw [hmu₂, hnu₂]; field_simp [hlam₁R]; linear_combination (lam₂ : ℝ) * hQ
        · rw [hmu₂, hnu₂] at hQ
          have hmul : (lam₂ : ℝ) * ((lam₁ : ℝ) * Q.1 + (mu₁ : ℝ) * Q.2 + (nu₁ : ℝ)) = 0 := by
            field_simp [hlam₁R] at hQ; linarith
          exact (mul_eq_zero.mp hmul).resolve_left hlam₂R
      · have hmu₁R : (mu₁ : ℝ) ≠ 0 := fun hz => hmu₁ (Subtype.ext hz)
        have hlam₂ : (lam₂ : ℝ) = (mu₂ : ℝ) * (lam₁ : ℝ) / (mu₁ : ℝ) := by
          field_simp [hmu₁R]; linarith
        have hnz₂R : (lam₂ : ℝ) ≠ 0 ∨ (mu₂ : ℝ) ≠ 0 :=
          hnz₂.imp (fun h hz => h (Subtype.ext hz)) (fun h hz => h (Subtype.ext hz))
        have hmu₂R : (mu₂ : ℝ) ≠ 0 := by
          rcases hnz₂R with h | h
          · intro hz; rw [hz, zero_mul, zero_div] at hlam₂; exact h hlam₂
          · exact h
        have hnu₂ : (nu₂ : ℝ) = (mu₂ : ℝ) * (nu₁ : ℝ) / (mu₁ : ℝ) := by
          field_simp [hmu₁R]
          linear_combination (mu₁ : ℝ) * hP₂ - (mu₂ : ℝ) * hP₁ + P.1 * hdet0
        constructor <;> intro hQ
        · rw [hlam₂, hnu₂]; field_simp [hmu₁R]; linear_combination (mu₂ : ℝ) * hQ
        · rw [hlam₂, hnu₂] at hQ
          have hmul : (mu₂ : ℝ) * ((lam₁ : ℝ) * Q.1 + (mu₁ : ℝ) * Q.2 + (nu₁ : ℝ)) = 0 := by
            field_simp [hmu₁R] at hQ; linarith
          exact (mul_eq_zero.mp hmul).resolve_left hmu₂R
    have hP1_eq : P.1 = (((mu₁ * nu₂ - mu₂ * nu₁) * det⁻¹ : F) : ℝ) := by
      change P.1 = ((mu₁ : ℝ) * (nu₂ : ℝ) - (mu₂ : ℝ) * (nu₁ : ℝ)) * (det : ℝ)⁻¹
      field_simp [hdet]
      dsimp [det]
      linear_combination (mu₂ : ℝ) * hP₁ - (mu₁ : ℝ) * hP₂
    have hP2_eq : P.2 = (((nu₁ * lam₂ - nu₂ * lam₁) * det⁻¹ : F) : ℝ) := by
      change P.2 = ((nu₁ : ℝ) * (lam₂ : ℝ) - (nu₂ : ℝ) * (lam₁ : ℝ)) * (det : ℝ)⁻¹
      field_simp [hdet]
      dsimp [det]
      linear_combination -(lam₂ : ℝ) * hP₁ + (lam₁ : ℝ) * hP₂
    have hP1F : P.1 ∈ F := hP1_eq ▸ ((mu₁ * nu₂ - mu₂ * nu₁) * det⁻¹).2
    have hP2F : P.2 ∈ F := hP2_eq ▸ ((nu₁ * lam₂ - nu₂ * lam₁) * det⁻¹).2
    have hle : IntermediateField.adjoin ℚ ({P.1, P.2} : Set ℝ) ≤ F := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      · exact hP1F
      · exact hP2F
    let F' : IntermediateField ℚ ℝ := F ⊔ IntermediateField.adjoin ℚ ({P.1, P.2} : Set ℝ)
    let _ : Algebra F F' := (IntermediateField.inclusion le_sup_left).toAlgebra
    have hFF' : F' = F := sup_eq_left.mpr hle
    have hmem_iff : ∀ w : ℝ, w ∈ F ↔ w ∈ F' := fun w =>
      (SetLike.ext_iff.mp hFF' w).symm
    let eAlg : F ≃ₐ[F] F' :=
      { toFun := fun z => ⟨z.1, (hmem_iff z.1).mp z.2⟩
        invFun := fun z => ⟨z.1, (hmem_iff z.1).mpr z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    refine ⟨Module.Finite.equiv eAlg.toLinearEquiv, Or.inl ?_⟩
    rw [← LinearEquiv.finrank_eq eAlg.toLinearEquiv, Module.finrank_self]
  · -- Case (ii): intersection of a straight line and a circle
    obtain ⟨lam, mu, nu, hnz, rfl⟩ := hline_eq hL
    obtain ⟨g, f, c, rfl⟩ := hcir_eq hC
    exact finrank_adjoin_pair_line_circle F hnz hPL hPC
  · -- Case (iii): intersection of two distinct circles reduces to Case (ii)
    obtain ⟨g₁, f₁, c₁, rfl⟩ := hcir_eq hC₁
    obtain ⟨g₂, f₂, c₂, rfl⟩ := hcir_eq hC₂
    dsimp at hP₁ hP₂
    let lam : F := (1 + 1) * (g₁ - g₂)
    let mu : F := (1 + 1) * (f₁ - f₂)
    let nu : F := c₁ - c₂
    have hlin : (lam : ℝ) * P.1 + (mu : ℝ) * P.2 + (nu : ℝ) = 0 := by
      dsimp [lam, mu, nu]
      linarith
    have hnz : lam ≠ 0 ∨ mu ≠ 0 := by
      by_contra hboth
      push Not at hboth
      have hg : (g₁ : ℝ) = (g₂ : ℝ) := by
        have := congrArg Subtype.val hboth.1
        dsimp [lam] at this; linarith
      have hf : (f₁ : ℝ) = (f₂ : ℝ) := by
        have := congrArg Subtype.val hboth.2
        dsimp [mu] at this; linarith
      have hc : (c₁ : ℝ) = (c₂ : ℝ) := by
        rw [hg, hf] at hP₁
        linarith
      apply hne
      ext Q
      simp [hg, hf, hc]
    exact finrank_adjoin_pair_line_circle F hnz hlin hP₁

/-- **Theorem 6.1** (§6.1, printed p. 55 / PDF p. 63; proof pp. 55–56 / PDF pp. 63–64):
*"If `P = (x, y)` is a constructible point, the extension `ℚ(x, y) : ℚ` is finite, and
`[ℚ(x, y) : ℚ] = 2^r`, for some non-negative integer `r`."* -/
theorem theorem_6_1 {x y : ℝ} (hP : IsConstructible (x, y)) :
    IsFiniteExtension ℚ (ratPointField x y) ∧
    ∃ r : ℕ, extDegree ℚ (ratPointField x y) = (2 : ℕ∞) ^ r ∧
      Module.finrank ℚ (ratPointField x y) = 2 ^ r := by
  obtain ⟨n, hn, seq, hseq, hlast⟩ := hP
  -- Define the cumulative coordinate field `F_k = ℚ(x_0, y_0, ..., x_k, y_k)` for `k ≤ n`
  let F : ℕ → IntermediateField ℚ ℝ := fun k =>
    IntermediateField.adjoin ℚ {z : ℝ | ∃ i : Fin (n + 1), (i : ℕ) ≤ k ∧ (z = (seq i).1 ∨ z = (seq i).2)}
  have hF_pow : ∀ k : ℕ, k ≤ n →
      Module.Finite ℚ (F k) ∧ ∃ s : ℕ, Module.finrank ℚ (F k) = 2 ^ s := by
    intro k hk
    induction k with
    | zero =>
      have hF0 : F 0 = ⊥ := by
        rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
        rintro z ⟨i, hi, hz⟩
        have hi0 : (i : ℕ) = 0 := by omega
        have hiz : i = 0 := Fin.ext hi0
        rw [hiz, hseq.1] at hz
        rcases hz with rfl | rfl <;> exact (⊥ : IntermediateField ℚ ℝ).zero_mem
      rw [hF0]
      refine ⟨inferInstance, 0, ?_⟩
      simp
    | succ k' ih =>
      by_cases hk0 : k' = 0
      · subst hk0
        have hF1 : F 1 = ⊥ := by
          rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
          rintro z ⟨i, hi, hz⟩
          have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
          rcases hi01 with hi0 | hi1
          · have hiz : i = 0 := Fin.ext hi0
            rw [hiz, hseq.1] at hz
            rcases hz with rfl | rfl <;> exact (⊥ : IntermediateField ℚ ℝ).zero_mem
          · have hi1' : i = ⟨1, Nat.lt_succ_of_le hn⟩ := Fin.ext hi1
            rw [hi1', hseq.2.1] at hz
            rcases hz with rfl | rfl
            · exact (⊥ : IntermediateField ℚ ℝ).one_mem
            · exact (⊥ : IntermediateField ℚ ℝ).zero_mem
        rw [hF1]
        refine ⟨inferInstance, 0, ?_⟩
        simp
      · obtain ⟨hfin_prev, s, hs⟩ := ih (by omega)
        let idx : Fin (n + 1) := ⟨k' + 1, by omega⟩
        have hS_in : ∀ Q ∈ prefixPointSet seq k', Q.1 ∈ F k' ∧ Q.2 ∈ F k' := by
          rintro Q ⟨i, hi, rfl⟩
          exact ⟨IntermediateField.subset_adjoin ℚ _ ⟨i, hi, Or.inl rfl⟩,
            IntermediateField.subset_adjoin ℚ _ ⟨i, hi, Or.inr rfl⟩⟩
        have hstep : IsOneStepFrom (prefixPointSet seq k') (seq idx) :=
          hseq.2.2 idx (by change 2 ≤ k' + 1; omega)
        have hF_sup : F (k' + 1) =
            F k' ⊔ IntermediateField.adjoin ℚ ({(seq idx).1, (seq idx).2} : Set ℝ) := by
          apply le_antisymm
          · rw [IntermediateField.adjoin_le_iff]
            rintro z ⟨i, hi, hz⟩
            by_cases hik : (i : ℕ) ≤ k'
            · exact (le_sup_left : F k' ≤ _)
                (IntermediateField.subset_adjoin ℚ _ ⟨i, hik, hz⟩)
            · have hieq : i = idx := by ext; dsimp [idx]; omega
              rw [hieq] at hz
              exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _)
                (IntermediateField.subset_adjoin ℚ _ hz)
          · refine sup_le ?_ ?_
            · rw [IntermediateField.adjoin_le_iff]
              rintro z ⟨i, hi, hz⟩
              exact IntermediateField.subset_adjoin ℚ _ ⟨i, by omega, hz⟩
            · rw [IntermediateField.adjoin_le_iff]
              rintro z hz
              exact IntermediateField.subset_adjoin ℚ _ ⟨idx, le_rfl, hz⟩
        let F' := F k' ⊔ IntermediateField.adjoin ℚ ({(seq idx).1, (seq idx).2} : Set ℝ)
        let _ : Algebra (F k') F' := (IntermediateField.inclusion le_sup_left).toAlgebra
        have _ : IsScalarTower ℚ (F k') F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
        obtain ⟨hfin_step, hrank_step⟩ := finrank_step_one_or_two (F k') hS_in hstep
        have _ : Module.Finite ℚ (F k') := hfin_prev
        have _ : Module.Finite (F k') F' := hfin_step
        have hfin_F' : Module.Finite ℚ F' := Module.Finite.trans (F k') F'
        have hmul := Module.finrank_mul_finrank ℚ (F k') F'
        rw [hF_sup]
        refine ⟨hfin_F', ?_⟩
        rcases hrank_step with h1 | h2
        · exact ⟨s, by rw [← hmul, hs, h1, mul_one]⟩
        · exact ⟨s + 1, by rw [← hmul, hs, h2, pow_succ]⟩
  obtain ⟨hFn_fin, s, hs⟩ := hF_pow n le_rfl
  have hle : ratPointField x y ≤ F n := by
    rw [ratPointField, IntermediateField.adjoin_le_iff]
    have hx : x = (seq (Fin.last n)).1 := congrArg Prod.fst hlast.symm
    have hy : y = (seq (Fin.last n)).2 := congrArg Prod.snd hlast.symm
    rintro z (rfl | rfl)
    · exact IntermediateField.subset_adjoin ℚ _ ⟨Fin.last n, le_rfl, Or.inl hx⟩
    · exact IntermediateField.subset_adjoin ℚ _ ⟨Fin.last n, le_rfl, Or.inr hy⟩
  let _ : Module.Finite ℚ (F n) := hFn_fin
  let _ : Algebra (ratPointField x y) (F n) := (IntermediateField.inclusion hle).toAlgebra
  have _ : IsScalarTower ℚ (ratPointField x y) (F n) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfin_xy : Module.Finite ℚ (ratPointField x y) :=
    Module.Finite.left ℚ (ratPointField x y) (F n)
  have hdvd : Module.finrank ℚ (ratPointField x y) ∣ 2 ^ s :=
    ⟨Module.finrank (ratPointField x y) (F n),
      (Module.finrank_mul_finrank ℚ (ratPointField x y) (F n)).trans hs |>.symm⟩
  obtain ⟨r, _, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  refine ⟨(isFiniteExtension_iff_moduleFinite ℚ (ratPointField x y)).mpr hfin_xy, r, ?_, hr⟩
  rw [extDegree_eq_finrank ℚ (ratPointField x y), hr, Nat.cast_pow, Nat.cast_ofNat]

/-- **Theorem 6.1 (Garling subfield form)** (§6.1, printed p. 55 / PDF p. 63):
Version of `Theorem 6.1` phrased directly on Chapter 4's `garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)`. -/
theorem theorem_6_1_subfield {x y : ℝ} (hP : IsConstructible (x, y)) :
    IsFiniteExtension ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) ∧
    ∃ r : ℕ, extDegree ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) = (2 : ℕ∞) ^ r := by
  obtain ⟨hfin, r, hr, _⟩ := theorem_6_1 hP
  have hsub := ratPointField_toSubfield_eq_garlingFieldGenSubfield x y
  have hmem_iff : ∀ w : ℝ, w ∈ ratPointField x y ↔
      w ∈ garlingFieldGenSubfield ℚ ({x, y} : Set ℝ) := fun w =>
    SetLike.ext_iff.mp hsub w
  let e : ratPointField x y ≃ₐ[ℚ] garlingFieldGenSubfield ℚ ({x, y} : Set ℝ) :=
    { toFun := fun z => ⟨z.1, (hmem_iff z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (hmem_iff z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have _ : Module.Finite ℚ (ratPointField x y) :=
    (isFiniteExtension_iff_moduleFinite ℚ (ratPointField x y)).mp hfin
  have hfin' : Module.Finite ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) :=
    Module.Finite.equiv e.toLinearEquiv
  refine ⟨(isFiniteExtension_iff_moduleFinite ℚ _).mpr hfin', r, ?_⟩
  rw [extDegree_eq_finrank, ← LinearEquiv.finrank_eq e.toLinearEquiv,
    ← extDegree_eq_finrank ℚ (ratPointField x y), hr]

/-! ### Coordinate closure, subfield of constructible reals, and Exercises 6.1, 6.2, 6.4 (p. 57) -/

/-- `(-1, 0)` is constructible by intersecting the first axis `P₀P₁` with the unit circle centred
at `P₀`. -/
theorem isConstructible_neg_one_zero : IsConstructible (-1, 0) := by
  refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_P₁
    isConstructible_P₀ isConstructible_P₀ isConstructible_P₁ P₀_ne_P₁ P₀_ne_P₁ ?_ ?_
  · dsimp [garlingLine, P₀, P₁]; ring
  · dsimp [garlingCircle, P₀, P₁]; ring

/-- Addition and subtraction along the first axis: if `(a, 0)` and `(b, 0)` are constructible,
then `(a + b, 0)` and `(a - b, 0)` are constructible. -/
theorem isConstructible_xaxis_add_sub {a b : ℝ}
    (ha : IsConstructible (a, 0)) (hb : IsConstructible (b, 0)) :
    IsConstructible (a + b, 0) ∧ IsConstructible (a - b, 0) := by
  by_cases hb0 : b = 0
  · subst hb0
    exact ⟨by simpa using ha, by simpa using ha⟩
  · have hP0b : P₀ ≠ (b, 0) := by
      intro h
      exact hb0 (congrArg Prod.fst h).symm
    refine ⟨?_, ?_⟩
    · refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_P₁
        ha isConstructible_P₀ hb P₀_ne_P₁ hP0b ?_ ?_
      · dsimp [garlingLine, P₀, P₁]; ring
      · dsimp [garlingCircle, P₀]; ring
    · refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_P₁
        ha isConstructible_P₀ hb P₀_ne_P₁ hP0b ?_ ?_
      · dsimp [garlingLine, P₀, P₁]; ring
      · dsimp [garlingCircle, P₀]; ring

theorem isConstructible_xaxis_neg {a : ℝ} (ha : IsConstructible (a, 0)) :
    IsConstructible (-a, 0) := by
  simpa using (isConstructible_xaxis_add_sub isConstructible_P₀ ha).2

/-- Vertical auxiliary point `(x, √3)` above any constructible `(x, 0)`, obtained by intersecting
circles of radius `2 = dist (-1, 0) (1, 0)` centred at `(x - 1, 0)` and `(x + 1, 0)`. -/
private theorem isConstructible_vertical_sqrt3 {x : ℝ} (hx : IsConstructible (x, 0)) :
    IsConstructible (x, Real.sqrt 3) := by
  have hxm1 : IsConstructible (x - 1, 0) :=
    (isConstructible_xaxis_add_sub hx isConstructible_P₁).2
  have hxp1 : IsConstructible (x + 1, 0) :=
    (isConstructible_xaxis_add_sub hx isConstructible_P₁).1
  have hne_pm1 : ((-1, 0) : PlanePoint) ≠ P₁ := by
    intro h; have := congrArg Prod.fst h; norm_num [P₁] at this
  have hcir_ne :
      garlingCircle (x - 1, 0) (-1, 0) P₁ ≠ garlingCircle (x + 1, 0) (-1, 0) P₁ := by
    intro hEq
    have hmem : (x + 3, (0 : ℝ)) ∈ garlingCircle (x + 1, 0) (-1, 0) P₁ := by
      dsimp [garlingCircle, P₁]; ring
    rw [← hEq] at hmem
    dsimp [garlingCircle, P₁] at hmem
    linarith
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine isConstructible_of_circle_circle
    hxm1 isConstructible_neg_one_zero isConstructible_P₁
    hxp1 isConstructible_neg_one_zero isConstructible_P₁
    hne_pm1 hne_pm1 hcir_ne ?_ ?_
  · dsimp [garlingCircle, P₁]; linear_combination hsq3
  · dsimp [garlingCircle, P₁]; linear_combination hsq3

/-- `(0, 1)` is constructible by intersecting the second axis `garlingLine P₀ (0, √3)` with the
unit circle centred at `P₀`. -/
theorem isConstructible_zero_one : IsConstructible (0, 1) := by
  have hv := isConstructible_vertical_sqrt3 isConstructible_P₀
  have hne : P₀ ≠ (0, Real.sqrt 3) := by
    intro h
    have h0 : (0 : ℝ) = Real.sqrt 3 := congrArg Prod.snd h
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  refine isConstructible_of_line_circle isConstructible_P₀ hv
    isConstructible_P₀ isConstructible_P₀ isConstructible_P₁ hne P₀_ne_P₁ ?_ ?_
  · dsimp [garlingLine, P₀]; ring
  · dsimp [garlingCircle, P₀, P₁]; ring

/-- Compass transfer between the first and second axes: `(0, t)` is constructible iff `(t, 0)` is. -/
theorem isConstructible_zero_y_iff {t : ℝ} :
    IsConstructible (0, t) ↔ IsConstructible (t, 0) := by
  have hP0_01 : P₀ ≠ ((0, 1) : PlanePoint) := by
    intro h; have := congrArg Prod.snd h; norm_num [P₀] at this
  constructor
  · intro ht
    by_cases ht0 : t = 0
    · subst ht0; exact isConstructible_P₀
    · have hne : P₀ ≠ (0, t) := fun h => ht0 (congrArg Prod.snd h).symm
      refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_P₁
        isConstructible_P₀ isConstructible_P₀ ht P₀_ne_P₁ hne ?_ ?_
      · dsimp [garlingLine, P₀, P₁]; ring
      · dsimp [garlingCircle, P₀]; ring
  · intro ht
    by_cases ht0 : t = 0
    · subst ht0; exact isConstructible_P₀
    · have hne : P₀ ≠ (t, 0) := fun h => ht0 (congrArg Prod.fst h).symm
      refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_zero_one
        isConstructible_P₀ isConstructible_P₀ ht hP0_01 hne ?_ ?_
      · dsimp [garlingLine, P₀]; ring
      · dsimp [garlingCircle, P₀]; ring

/-- Horizontal auxiliary point `(√3, y)` beside any constructible `(0, y)`. -/
private theorem isConstructible_horizontal_sqrt3 {y : ℝ} (hy : IsConstructible (y, 0)) :
    IsConstructible (Real.sqrt 3, y) := by
  have hym1 : IsConstructible (0, y - 1) :=
    isConstructible_zero_y_iff.mpr (isConstructible_xaxis_add_sub hy isConstructible_P₁).2
  have hyp1 : IsConstructible (0, y + 1) :=
    isConstructible_zero_y_iff.mpr (isConstructible_xaxis_add_sub hy isConstructible_P₁).1
  have hne_pm1 : ((-1, 0) : PlanePoint) ≠ P₁ := by
    intro h; have := congrArg Prod.fst h; norm_num [P₁] at this
  have hcir_ne :
      garlingCircle (0, y - 1) (-1, 0) P₁ ≠ garlingCircle (0, y + 1) (-1, 0) P₁ := by
    intro hEq
    have hmem : ((0 : ℝ), y + 3) ∈ garlingCircle (0, y + 1) (-1, 0) P₁ := by
      dsimp [garlingCircle, P₁]; ring
    rw [← hEq] at hmem
    dsimp [garlingCircle, P₁] at hmem
    linarith
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine isConstructible_of_circle_circle
    hym1 isConstructible_neg_one_zero isConstructible_P₁
    hyp1 isConstructible_neg_one_zero isConstructible_P₁
    hne_pm1 hne_pm1 hcir_ne ?_ ?_
  · dsimp [garlingCircle, P₁]; linear_combination hsq3
  · dsimp [garlingCircle, P₁]; linear_combination hsq3

/-- Assembling `(x, y)` from constructible coordinates `(x, 0)` and `(y, 0)` as the intersection
of the vertical line `X = x` and horizontal line `Y = y`. -/
theorem isConstructible_of_coords {x y : ℝ}
    (hx : IsConstructible (x, 0)) (hy : IsConstructible (y, 0)) :
    IsConstructible (x, y) := by
  have hs3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hv : IsConstructible (x, Real.sqrt 3) := isConstructible_vertical_sqrt3 hx
  have h0y : IsConstructible (0, y) := isConstructible_zero_y_iff.mpr hy
  have hh : IsConstructible (Real.sqrt 3, y) := isConstructible_horizontal_sqrt3 hy
  have hne_v : ((x, 0) : PlanePoint) ≠ (x, Real.sqrt 3) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; linarith
  have hne_h : ((0, y) : PlanePoint) ≠ (Real.sqrt 3, y) := by
    intro h; have := congrArg Prod.fst h; dsimp at this; linarith
  have hlines_ne : garlingLine (x, 0) (x, Real.sqrt 3) ≠ garlingLine (0, y) (Real.sqrt 3, y) := by
    intro hEq
    have hmem : (x + 1, y) ∈ garlingLine (0, y) (Real.sqrt 3, y) := by
      dsimp [garlingLine]; ring
    rw [← hEq] at hmem
    dsimp [garlingLine] at hmem
    linarith
  refine isConstructible_of_line_line hx hv h0y hh hne_v hne_h hlines_ne ?_ ?_
  · dsimp [garlingLine]; ring
  · dsimp [garlingLine]; ring

/-- Projecting the first coordinate: if `(x, y)` is constructible, then `(x, 0)` is constructible
(by reflecting `(x, y)` across the first axis using circles centred at `P₀` and `P₁`). -/
theorem isConstructible_fst {x y : ℝ} (hP : IsConstructible (x, y)) :
    IsConstructible (x, 0) := by
  by_cases hy0 : y = 0
  · subst hy0; exact hP
  · have hne0 : P₀ ≠ (x, y) := fun h => hy0 (congrArg Prod.snd h).symm
    have hne1 : P₁ ≠ (x, y) := fun h => hy0 (congrArg Prod.snd h).symm
    have hcir_ne : garlingCircle P₀ P₀ (x, y) ≠ garlingCircle P₁ P₁ (x, y) := by
      intro hEq
      have hm1 : (-x, -y) ∈ garlingCircle P₀ P₀ (x, y) := by
        dsimp [garlingCircle, P₀]; ring
      rw [hEq] at hm1
      have hm2 : (2 - x, -y) ∈ garlingCircle P₁ P₁ (x, y) := by
        dsimp [garlingCircle, P₁]; ring
      rw [← hEq] at hm2
      dsimp [garlingCircle, P₀, P₁] at hm1 hm2
      linarith
    have hrefl : IsConstructible (x, -y) := by
      refine isConstructible_of_circle_circle
        isConstructible_P₀ isConstructible_P₀ hP
        isConstructible_P₁ isConstructible_P₁ hP
        hne0 hne1 hcir_ne ?_ ?_
      · dsimp [garlingCircle, P₀]; ring
      · dsimp [garlingCircle, P₁]; ring
    have hne_refl : ((x, y) : PlanePoint) ≠ (x, -y) := by
      intro h; have := congrArg Prod.snd h; dsimp at this; exact hy0 (by linarith)
    have hline_ne : garlingLine (x, y) (x, -y) ≠ garlingLine P₀ P₁ := by
      intro hEq
      have hmem : (x, y) ∈ garlingLine (x, y) (x, -y) := mem_garlingLine_left _ _
      rw [hEq] at hmem
      dsimp [garlingLine, P₀, P₁] at hmem
      exact hy0 (by linarith)
    refine isConstructible_of_line_line hP hrefl isConstructible_P₀ isConstructible_P₁
      hne_refl P₀_ne_P₁ hline_ne ?_ ?_
    · dsimp [garlingLine]; ring
    · dsimp [garlingLine, P₀, P₁]; ring

/-- Coordinate swap `(x, y) ↦ (y, x)` by reflecting across the diagonal through `P₀ = (0, 0)` and
`(1, 1)`. -/
theorem isConstructible_swap {x y : ℝ} (hP : IsConstructible (x, y)) :
    IsConstructible (y, x) := by
  by_cases hxy : y = x
  · subst hxy; exact hP
  · have h11 : IsConstructible (1, 1) :=
      isConstructible_of_coords isConstructible_P₁ isConstructible_P₁
    have hne0 : P₀ ≠ (x, y) := by
      intro h
      have hx0 : 0 = x := congrArg Prod.fst h
      have hy0 : 0 = y := congrArg Prod.snd h
      exact hxy (hy0.symm.trans hx0)
    have hne11 : ((1, 1) : PlanePoint) ≠ (x, y) := by
      intro h
      have hx1 : 1 = x := congrArg Prod.fst h
      have hy1 : 1 = y := congrArg Prod.snd h
      exact hxy (hy1.symm.trans hx1)
    have hcir_ne : garlingCircle P₀ P₀ (x, y) ≠ garlingCircle (1, 1) (1, 1) (x, y) := by
      intro hEq
      have hm1 : (-x, -y) ∈ garlingCircle P₀ P₀ (x, y) := by
        dsimp [garlingCircle, P₀]; ring
      rw [hEq] at hm1
      have hm2 : (2 - x, 2 - y) ∈ garlingCircle (1, 1) (1, 1) (x, y) := by
        dsimp [garlingCircle]; ring
      rw [← hEq] at hm2
      dsimp [garlingCircle, P₀] at hm1 hm2
      linarith
    refine isConstructible_of_circle_circle
      isConstructible_P₀ isConstructible_P₀ hP
      h11 h11 hP
      hne0 hne11 hcir_ne ?_ ?_
    · dsimp [garlingCircle, P₀]; ring
    · dsimp [garlingCircle]; ring

/-- Projecting the second coordinate: if `(x, y)` is constructible, then `(y, 0)` is constructible. -/
theorem isConstructible_snd {x y : ℝ} (hP : IsConstructible (x, y)) :
    IsConstructible (y, 0) :=
  isConstructible_fst (isConstructible_swap hP)

/-- Exact coordinate characterization: `(x, y)` is constructible iff both `(x, 0)` and `(y, 0)` are
constructible. -/
theorem isConstructible_iff_coords (x y : ℝ) :
    IsConstructible (x, y) ↔ IsConstructible (x, 0) ∧ IsConstructible (y, 0) :=
  ⟨fun h => ⟨isConstructible_fst h, isConstructible_snd h⟩,
   fun ⟨hx, hy⟩ => isConstructible_of_coords hx hy⟩

/-- Multiplication along the first axis: if `(a, 0)` and `(b, 0)` are constructible, then
`(a * b, 0)` is constructible (intersecting `garlingLine (0, b) (a, b - 1)` with `P₀P₁`). -/
theorem isConstructible_xaxis_mul {a b : ℝ}
    (ha : IsConstructible (a, 0)) (hb : IsConstructible (b, 0)) :
    IsConstructible (a * b, 0) := by
  have h0b : IsConstructible (0, b) := isConstructible_of_coords isConstructible_P₀ hb
  have habm1 : IsConstructible (a, b - 1) :=
    isConstructible_of_coords ha (isConstructible_xaxis_add_sub hb isConstructible_P₁).2
  have hAB : ((0, b) : PlanePoint) ≠ (a, b - 1) := by
    intro h; have := congrArg Prod.snd h; dsimp at this; linarith
  have hline_ne : garlingLine (0, b) (a, b - 1) ≠ garlingLine P₀ P₁ := by
    intro hEq
    have hm1 : ((0, b) : PlanePoint) ∈ garlingLine (0, b) (a, b - 1) := mem_garlingLine_left _ _
    have hm2 : ((a, b - 1) : PlanePoint) ∈ garlingLine (0, b) (a, b - 1) :=
      mem_garlingLine_right _ _
    rw [hEq] at hm1 hm2
    dsimp [garlingLine, P₀, P₁] at hm1 hm2
    linarith
  refine isConstructible_of_line_line h0b habm1 isConstructible_P₀ isConstructible_P₁
    hAB P₀_ne_P₁ hline_ne ?_ ?_
  · dsimp [garlingLine]; ring
  · dsimp [garlingLine, P₀, P₁]; ring

/-- Multiplicative inverse along the first axis: if `(a, 0)` is constructible, then `(a⁻¹, 0)` is
constructible (intersecting `garlingLine P₀ (1, a)` with `garlingLine (0, 1) (1, 1)`). -/
theorem isConstructible_xaxis_inv {a : ℝ} (ha : IsConstructible (a, 0)) :
    IsConstructible (a⁻¹, 0) := by
  by_cases ha0 : a = 0
  · subst ha0; simpa [P₀] using isConstructible_P₀
  · have h1a : IsConstructible (1, a) := isConstructible_of_coords isConstructible_P₁ ha
    have h11 : IsConstructible (1, 1) :=
      isConstructible_of_coords isConstructible_P₁ isConstructible_P₁
    have hP0_1a : P₀ ≠ ((1, a) : PlanePoint) := by
      intro h; have := congrArg Prod.fst h; norm_num [P₀] at this
    have h01_11 : ((0, 1) : PlanePoint) ≠ (1, 1) := by
      intro h; have := congrArg Prod.fst h; norm_num at this
    have hline_ne : garlingLine P₀ (1, a) ≠ garlingLine (0, 1) (1, 1) := by
      intro hEq
      have hm : P₀ ∈ garlingLine P₀ (1, a) := mem_garlingLine_left _ _
      rw [hEq] at hm
      dsimp [garlingLine, P₀] at hm
      linarith
    have hpt : IsConstructible (a⁻¹, 1) := by
      refine isConstructible_of_line_line isConstructible_P₀ h1a
        isConstructible_zero_one h11 hP0_1a h01_11 hline_ne ?_ ?_
      · dsimp [garlingLine, P₀]
        field_simp [ha0]
        ring
      · dsimp [garlingLine]; ring
    exact isConstructible_fst hpt

/-- The subfield of `ℝ` consisting of all real numbers `x` such that `(x, 0)` is constructible. -/
def constructibleSubfield : Subfield ℝ where
  carrier := {x : ℝ | IsConstructible (x, 0)}
  mul_mem' ha hb := isConstructible_xaxis_mul ha hb
  one_mem' := isConstructible_P₁
  add_mem' ha hb := (isConstructible_xaxis_add_sub ha hb).1
  zero_mem' := isConstructible_P₀
  neg_mem' ha := isConstructible_xaxis_neg ha
  inv_mem' _ ha := isConstructible_xaxis_inv ha

@[simp]
theorem mem_constructibleSubfield_iff (x : ℝ) :
    x ∈ constructibleSubfield ↔ IsConstructible (x, 0) :=
  Iff.rfl

theorem isConstructible_iff_mem_constructibleSubfield (x y : ℝ) :
    IsConstructible (x, y) ↔ x ∈ constructibleSubfield ∧ y ∈ constructibleSubfield :=
  isConstructible_iff_coords x y

/-- **Exercise 6.4** (§6.1, printed p. 57 / PDF p. 65):
*"Suppose that `P = (x, y)` is a constructible point. Let `α` and `β` be elements of `ℚ(x, y)`. Show
that `(α, β)` is a constructible point."* -/
theorem exercise_6_4 {x y x' y' : ℝ} (hP : IsConstructible (x, y))
    (hx' : x' ∈ ratPointField x y) (hy' : y' ∈ ratPointField x y) :
    IsConstructible (x', y') := by
  obtain ⟨hx, hy⟩ := (isConstructible_iff_mem_constructibleSubfield x y).mp hP
  let K_int : IntermediateField ℚ ℝ :=
    constructibleSubfield.toIntermediateField (fun q => SubfieldClass.ratCast_mem _ q)
  have hle : ratPointField x y ≤ K_int := by
    unfold ratPointField
    rw [IntermediateField.adjoin_le_iff]
    rintro z (rfl | rfl)
    · exact hx
    · exact hy
  exact (isConstructible_iff_mem_constructibleSubfield x' y').mpr ⟨hle hx', hle hy'⟩

/-- **Exercise 6.4 (Garling subfield form)** (§6.1, printed p. 57 / PDF p. 65):
Version phrased directly on Chapter 4's `garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)`. -/
theorem exercise_6_4_subfield {x y x' y' : ℝ} (hP : IsConstructible (x, y))
    (hx' : x' ∈ garlingFieldGenSubfield ℚ ({x, y} : Set ℝ))
    (hy' : y' ∈ garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) :
    IsConstructible (x', y') := by
  rw [← ratPointField_toSubfield_eq_garlingFieldGenSubfield] at hx' hy'
  exact exercise_6_4 hP hx' hy'

/-- **Exercise 6.2** (§6.1, printed p. 57 / PDF p. 65):
*"Suppose that the point `(l, 0)` is constructible (where `l > 0`). Show how to construct the
points `(√l, 0)` and `(l², 0)`."* -/
theorem exercise_6_2 {l : ℝ} (hl : IsConstructible (l, 0)) (hl_pos : 0 < l) :
    IsConstructible (Real.sqrt l, 0) ∧ IsConstructible (l ^ 2, 0) := by
  have hl_mem : l ∈ constructibleSubfield := hl
  have htwo : (2 : ℝ) ∈ constructibleSubfield := SubfieldClass.ratCast_mem constructibleSubfield 2
  have hm_mem : (l - 1) / 2 ∈ constructibleSubfield :=
    constructibleSubfield.div_mem
      (constructibleSubfield.sub_mem hl_mem constructibleSubfield.one_mem) htwo
  have hM : IsConstructible ((l - 1) / 2, 0) := hm_mem
  have hP0_01 : P₀ ≠ ((0, 1) : PlanePoint) := by
    intro h; have := congrArg Prod.snd h; norm_num [P₀] at this
  have hM_ne : (((l - 1) / 2, 0) : PlanePoint) ≠ (l, 0) := by
    intro h; have := congrArg Prod.fst h; dsimp at this; linarith
  have hsql : Real.sqrt l ^ 2 = l := Real.sq_sqrt (le_of_lt hl_pos)
  have h0_sqrt : IsConstructible (0, Real.sqrt l) := by
    refine isConstructible_of_line_circle isConstructible_P₀ isConstructible_zero_one
      hM hM hl hP0_01 hM_ne ?_ ?_
    · dsimp [garlingLine, P₀]; ring
    · dsimp [garlingCircle]; linear_combination hsql
  exact ⟨isConstructible_zero_y_iff.mp h0_sqrt, constructibleSubfield.pow_mem hl_mem 2⟩

/-- `constructibleSubfield` is closed under real square roots of non-negative elements. -/
theorem sqrt_mem_constructibleSubfield {x : ℝ}
    (hx : x ∈ constructibleSubfield) (hx0 : 0 ≤ x) :
    Real.sqrt x ∈ constructibleSubfield := by
  rcases eq_or_lt_of_le hx0 with rfl | hpos
  · rw [Real.sqrt_zero]; exact constructibleSubfield.zero_mem
  · exact (exercise_6_2 hx hpos).1

/-! #### Exercise 6.1: Constructions from the first paragraph of §6.1 (printed pp. 54, 57) -/

/-- Degeneracy witness for `Exercise 6.1` when two points coincide (`A = B`): `garlingLine A A` is
the entire plane `Set.univ`, so a distinctness hypothesis `A ≠ B` is genuinely required whenever a
construction refers to "a given line" or "two rays" via point pairs. -/
theorem exercise_6_1_degenerate_line_counterexample (A : PlanePoint) :
    garlingLine A A = Set.univ := by
  ext P
  simp [garlingLine]

/-- **Exercise 6.1(a) — Equilateral triangle, square, and regular hexagon** (§6.1, pp. 54, 57):
Given constructible distinct points `A ≠ B`:
1. there is a constructible apex `C` forming an equilateral triangle with `A, B`;
2. the rotated vertices `D, C` forming a Euclidean square `A, B, C, D` of side `euclidDist A B` are
   constructible; and
3. all six vertices `(cos(2πk/6), sin(2πk/6))` (`0 ≤ k < 6`) of the unit regular hexagon are
   constructible. -/
theorem exercise_6_1_polygons :
    (∀ {A B : PlanePoint}, IsConstructible A → IsConstructible B → A ≠ B →
      (∃ C : PlanePoint, IsConstructible C ∧
        sqDist C A = sqDist A B ∧ sqDist C B = sqDist A B) ∧
      (let D : PlanePoint := (A.1 - (B.2 - A.2), A.2 + (B.1 - A.1))
       let C : PlanePoint := (B.1 - (B.2 - A.2), B.2 + (B.1 - A.1))
       IsConstructible D ∧ IsConstructible C ∧
       sqDist A B = sqDist B C ∧ sqDist B C = sqDist C D ∧ sqDist C D = sqDist D A ∧
       (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0)) ∧
    (∀ k : Fin 6,
      IsConstructible (Real.cos (2 * Real.pi * (k : ℝ) / 6),
        Real.sin (2 * Real.pi * (k : ℝ) / 6))) := by
  let K := constructibleSubfield
  have htwo : (2 : ℝ) ∈ K := by exact_mod_cast SubfieldClass.ratCast_mem K (2 : ℚ)
  have hhalf : (1 / 2 : ℝ) ∈ K := K.div_mem K.one_mem htwo
  have hs3 : Real.sqrt 3 ∈ K :=
    sqrt_mem_constructibleSubfield
      (by exact_mod_cast SubfieldClass.ratCast_mem K (3 : ℚ)) (by norm_num)
  have hs3_half : Real.sqrt 3 / 2 ∈ K := K.div_mem hs3 htwo
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨fun {A B} hA hB _ => ?_, ?_⟩
  · obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
    obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
    refine ⟨?_, ?_⟩
    · let E : PlanePoint :=
        ((A.1 + B.1) / 2 - Real.sqrt 3 / 2 * (B.2 - A.2),
         (A.2 + B.2) / 2 + Real.sqrt 3 / 2 * (B.1 - A.1))
      have hE : IsConstructible E :=
        (isConstructible_iff_mem_constructibleSubfield _ _).mpr
          ⟨K.sub_mem (K.div_mem (K.add_mem hA1 hB1) htwo)
            (K.mul_mem hs3_half (K.sub_mem hB2 hA2)),
           K.add_mem (K.div_mem (K.add_mem hA2 hB2) htwo)
            (K.mul_mem hs3_half (K.sub_mem hB1 hA1))⟩
      refine ⟨E, hE, ?_, ?_⟩
      · dsimp [sqDist, E]
        linear_combination ((B.2 - A.2) ^ 2 + (B.1 - A.1) ^ 2) / 4 * hsq3
      · dsimp [sqDist, E]
        linear_combination ((B.2 - A.2) ^ 2 + (B.1 - A.1) ^ 2) / 4 * hsq3
    · have hD : IsConstructible (A.1 - (B.2 - A.2), A.2 + (B.1 - A.1)) :=
        (isConstructible_iff_mem_constructibleSubfield _ _).mpr
          ⟨K.sub_mem hA1 (K.sub_mem hB2 hA2), K.add_mem hA2 (K.sub_mem hB1 hA1)⟩
      have hC : IsConstructible (B.1 - (B.2 - A.2), B.2 + (B.1 - A.1)) :=
        (isConstructible_iff_mem_constructibleSubfield _ _).mpr
          ⟨K.sub_mem hB1 (K.sub_mem hB2 hA2), K.add_mem hB2 (K.sub_mem hB1 hA1)⟩
      refine ⟨hD, hC, ?_, ?_, ?_, ?_⟩ <;> (dsimp [sqDist]; ring)
  · intro k
    fin_cases k
    · simpa [P₁] using isConstructible_P₁
    · have hc : Real.cos (2 * Real.pi * (1 : ℝ) / 6) = 1 / 2 := by
        have : 2 * Real.pi * (1 : ℝ) / 6 = Real.pi / 3 := by ring
        rw [this, Real.cos_pi_div_three]
      have hs : Real.sin (2 * Real.pi * (1 : ℝ) / 6) = Real.sqrt 3 / 2 := by
        have : 2 * Real.pi * (1 : ℝ) / 6 = Real.pi / 3 := by ring
        rw [this, Real.sin_pi_div_three]
      dsimp; push_cast; rw [hc, hs]
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr ⟨hhalf, hs3_half⟩
    · have hc : Real.cos (2 * Real.pi * (2 : ℝ) / 6) = -(1 / 2) := by
        have : 2 * Real.pi * (2 : ℝ) / 6 = Real.pi - Real.pi / 3 := by ring
        rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
      have hs : Real.sin (2 * Real.pi * (2 : ℝ) / 6) = Real.sqrt 3 / 2 := by
        have : 2 * Real.pi * (2 : ℝ) / 6 = Real.pi - Real.pi / 3 := by ring
        rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
      dsimp; rw [hc, hs]
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr ⟨K.neg_mem hhalf, hs3_half⟩
    · have hc : Real.cos (2 * Real.pi * (3 : ℝ) / 6) = -1 := by
        have : 2 * Real.pi * (3 : ℝ) / 6 = Real.pi := by ring
        rw [this, Real.cos_pi]
      have hs : Real.sin (2 * Real.pi * (3 : ℝ) / 6) = 0 := by
        have : 2 * Real.pi * (3 : ℝ) / 6 = Real.pi := by ring
        rw [this, Real.sin_pi]
      dsimp; rw [hc, hs]
      exact isConstructible_neg_one_zero
    · have hc : Real.cos (2 * Real.pi * (4 : ℝ) / 6) = -(1 / 2) := by
        have : 2 * Real.pi * (4 : ℝ) / 6 = Real.pi / 3 + Real.pi := by ring
        rw [this, Real.cos_add_pi, Real.cos_pi_div_three]
      have hs : Real.sin (2 * Real.pi * (4 : ℝ) / 6) = -(Real.sqrt 3 / 2) := by
        have : 2 * Real.pi * (4 : ℝ) / 6 = Real.pi / 3 + Real.pi := by ring
        rw [this, Real.sin_add_pi, Real.sin_pi_div_three]
      dsimp; rw [hc, hs]
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr
        ⟨K.neg_mem hhalf, K.neg_mem hs3_half⟩
    · have hc : Real.cos (2 * Real.pi * (5 : ℝ) / 6) = 1 / 2 := by
        have : 2 * Real.pi * (5 : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 := by ring
        rw [this, Real.cos_two_pi_sub, Real.cos_pi_div_three]
      have hs : Real.sin (2 * Real.pi * (5 : ℝ) / 6) = -(Real.sqrt 3 / 2) := by
        have : 2 * Real.pi * (5 : ℝ) / 6 = -(Real.pi / 3) + 2 * Real.pi := by ring
        rw [this, Real.sin_add_two_pi, Real.sin_neg, Real.sin_pi_div_three]
      dsimp; rw [hc, hs]
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr ⟨hhalf, K.neg_mem hs3_half⟩

/-- **Exercise 6.1(b) — Bisecting an angle** (§6.1, pp. 54, 57):
Given a constructible vertex `O` and constructible points `A ≠ O`, `B ≠ O` defining two rays from
`O`, there exists a constructible point `C ≠ O` whose ray from `O` makes equal non-negative cosine
(normalized inner product) with both rays `OA` and `OB`. -/
theorem exercise_6_1_bisect_angle {O A B : PlanePoint}
    (hO : IsConstructible O) (hA : IsConstructible A) (hB : IsConstructible B)
    (hAO : A ≠ O) (hBO : B ≠ O) :
    let dA := euclidDist A O
    let dB := euclidDist B O
    ∃ C : PlanePoint, IsConstructible C ∧ C ≠ O ∧
      ((C.1 - O.1) * ((A.1 - O.1) / dA) + (C.2 - O.2) * ((A.2 - O.2) / dA) =
       (C.1 - O.1) * ((B.1 - O.1) / dB) + (C.2 - O.2) * ((B.2 - O.2) / dB)) ∧
      0 ≤ (C.1 - O.1) * ((A.1 - O.1) / dA) + (C.2 - O.2) * ((A.2 - O.2) / dA) := by
  intro dA dB
  let K := constructibleSubfield
  obtain ⟨hO1, hO2⟩ := (isConstructible_iff_mem_constructibleSubfield O.1 O.2).mp hO
  obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
  obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
  have hdA_pos : 0 < dA := Real.sqrt_pos.mpr (sqDist_pos_iff.mpr hAO)
  have hdB_pos : 0 < dB := Real.sqrt_pos.mpr (sqDist_pos_iff.mpr hBO)
  have hdA_K : dA ∈ K := sqrt_mem_constructibleSubfield
    (K.add_mem (K.pow_mem (K.sub_mem hA1 hO1) 2) (K.pow_mem (K.sub_mem hA2 hO2) 2))
    (sqDist_nonneg A O)
  have hdB_K : dB ∈ K := sqrt_mem_constructibleSubfield
    (K.add_mem (K.pow_mem (K.sub_mem hB1 hO1) 2) (K.pow_mem (K.sub_mem hB2 hO2) 2))
    (sqDist_nonneg B O)
  let uA1 := (A.1 - O.1) / dA
  let uA2 := (A.2 - O.2) / dA
  let uB1 := (B.1 - O.1) / dB
  let uB2 := (B.2 - O.2) / dB
  have huA1 : uA1 ∈ K := K.div_mem (K.sub_mem hA1 hO1) hdA_K
  have huA2 : uA2 ∈ K := K.div_mem (K.sub_mem hA2 hO2) hdA_K
  have huB1 : uB1 ∈ K := K.div_mem (K.sub_mem hB1 hO1) hdB_K
  have huB2 : uB2 ∈ K := K.div_mem (K.sub_mem hB2 hO2) hdB_K
  have huA_norm : uA1 ^ 2 + uA2 ^ 2 = 1 := by
    dsimp [uA1, uA2]
    have hdA2 : dA ^ 2 = (A.1 - O.1) ^ 2 + (A.2 - O.2) ^ 2 := euclidDist_sq A O
    have hdA_ne : dA ≠ 0 := ne_of_gt hdA_pos
    field_simp [hdA_ne]
    linarith
  have huB_norm : uB1 ^ 2 + uB2 ^ 2 = 1 := by
    dsimp [uB1, uB2]
    have hdB2 : dB ^ 2 = (B.1 - O.1) ^ 2 + (B.2 - O.2) ^ 2 := euclidDist_sq B O
    have hdB_ne : dB ≠ 0 := ne_of_gt hdB_pos
    field_simp [hdB_ne]
    linarith
  by_cases hsum : uA1 + uB1 = 0 ∧ uA2 + uB2 = 0
  · -- Straight angle `π`: take perpendicular unit vector `(-uA2, uA1)` attached at `O`
    let C : PlanePoint := (O.1 - uA2, O.2 + uA1)
    have hC : IsConstructible C :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mpr
        ⟨K.sub_mem hO1 huA2, K.add_mem hO2 huA1⟩
    have hCO : C ≠ O := by
      intro hEq
      have h1 : O.1 - uA2 = O.1 := congrArg Prod.fst hEq
      have h2 : O.2 + uA1 = O.2 := congrArg Prod.snd hEq
      have z1 : uA1 = 0 := by linarith
      have z2 : uA2 = 0 := by linarith
      rw [z1, z2] at huA_norm
      norm_num at huA_norm
    refine ⟨C, hC, hCO, ?_, ?_⟩
    · dsimp [C]
      have hb1 : uB1 = -uA1 := by linarith [hsum.1]
      have hb2 : uB2 = -uA2 := by linarith [hsum.2]
      change (O.1 - uA2 - O.1) * uA1 + (O.2 + uA1 - O.2) * uA2 =
        (O.1 - uA2 - O.1) * uB1 + (O.2 + uA1 - O.2) * uB2
      rw [hb1, hb2]; ring
    · change 0 ≤ (O.1 - uA2 - O.1) * uA1 + (O.2 + uA1 - O.2) * uA2
      linarith [show (O.1 - uA2 - O.1) * uA1 + (O.2 + uA1 - O.2) * uA2 = 0 by ring]
  · -- Non-opposite rays: take sum of unit vectors `O + (uA + uB)`
    let C : PlanePoint := (O.1 + uA1 + uB1, O.2 + uA2 + uB2)
    have hC : IsConstructible C :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mpr
        ⟨K.add_mem (K.add_mem hO1 huA1) huB1, K.add_mem (K.add_mem hO2 huA2) huB2⟩
    have hCO : C ≠ O := by
      intro hEq
      have h1 : O.1 + uA1 + uB1 = O.1 := congrArg Prod.fst hEq
      have h2 : O.2 + uA2 + uB2 = O.2 := congrArg Prod.snd hEq
      exact hsum ⟨by linarith, by linarith⟩
    refine ⟨C, hC, hCO, ?_, ?_⟩
    · change (O.1 + uA1 + uB1 - O.1) * uA1 + (O.2 + uA2 + uB2 - O.2) * uA2 =
        (O.1 + uA1 + uB1 - O.1) * uB1 + (O.2 + uA2 + uB2 - O.2) * uB2
      linear_combination huA_norm - huB_norm
    · change 0 ≤ (O.1 + uA1 + uB1 - O.1) * uA1 + (O.2 + uA2 + uB2 - O.2) * uA2
      have hsq : 0 ≤ (uA1 + uB1) ^ 2 + (uA2 + uB2) ^ 2 := by positivity
      linarith [show (O.1 + uA1 + uB1 - O.1) * uA1 + (O.2 + uA2 + uB2 - O.2) * uA2 =
        ((uA1 + uB1) ^ 2 + (uA2 + uB2) ^ 2 + (uA1 ^ 2 + uA2 ^ 2 - (uB1 ^ 2 + uB2 ^ 2))) / 2
        by ring, huA_norm, huB_norm]

/-- **Exercise 6.1(c) — Dropping a perpendicular from a point onto a line** (§6.1, pp. 54, 57):
Given constructible `A ≠ B` and any constructible point `P`, both the orthogonal foot `F` on
`garlingLine A B` and an auxiliary constructible point `Q ≠ P` defining the perpendicular line
`garlingLine P Q` through `P` and `F` are constructible. -/
theorem exercise_6_1_drop_perpendicular {A B P : PlanePoint}
    (hA : IsConstructible A) (hB : IsConstructible B) (hP : IsConstructible P) (hAB : A ≠ B) :
    ∃ F Q : PlanePoint, IsConstructible F ∧ IsConstructible Q ∧ Q ≠ P ∧
      F ∈ garlingLine A B ∧ F ∈ garlingLine P Q ∧
      (P.1 - F.1) * (B.1 - A.1) + (P.2 - F.2) * (B.2 - A.2) = 0 ∧
      (Q.1 - P.1) * (B.1 - A.1) + (Q.2 - P.2) * (B.2 - A.2) = 0 := by
  let K := constructibleSubfield
  obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
  obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
  obtain ⟨hP1, hP2⟩ := (isConstructible_iff_mem_constructibleSubfield P.1 P.2).mp hP
  let dx := B.1 - A.1
  let dy := B.2 - A.2
  let d2 := dx ^ 2 + dy ^ 2
  have hd2_nz : d2 ≠ 0 := by
    have : d2 = sqDist B A := rfl
    rw [this]
    exact mt sqDist_eq_zero_iff.mp hAB.symm
  have hdx : dx ∈ K := K.sub_mem hB1 hA1
  have hdy : dy ∈ K := K.sub_mem hB2 hA2
  have hd2 : d2 ∈ K := K.add_mem (K.pow_mem hdx 2) (K.pow_mem hdy 2)
  let t := ((P.1 - A.1) * dx + (P.2 - A.2) * dy) / d2
  have ht : t ∈ K := K.div_mem
    (K.add_mem (K.mul_mem (K.sub_mem hP1 hA1) hdx) (K.mul_mem (K.sub_mem hP2 hA2) hdy)) hd2
  let F : PlanePoint := (A.1 + t * dx, A.2 + t * dy)
  let Q : PlanePoint := (P.1 - dy, P.2 + dx)
  have hF : IsConstructible F :=
    (isConstructible_iff_mem_constructibleSubfield _ _).mpr
      ⟨K.add_mem hA1 (K.mul_mem ht hdx), K.add_mem hA2 (K.mul_mem ht hdy)⟩
  have hQ : IsConstructible Q :=
    (isConstructible_iff_mem_constructibleSubfield _ _).mpr
      ⟨K.sub_mem hP1 hdy, K.add_mem hP2 hdx⟩
  have hQP : Q ≠ P := by
    intro hEq
    have h1 : P.1 - dy = P.1 := congrArg Prod.fst hEq
    have h2 : P.2 + dx = P.2 := congrArg Prod.snd hEq
    apply hAB
    ext <;> dsimp [dx, dy] at h1 h2 <;> linarith
  refine ⟨F, Q, hF, hQ, hQP, ?_, ?_, ?_, ?_⟩
  · dsimp [garlingLine, F, dx, dy]; ring
  · dsimp [garlingLine, F, Q, t]
    field_simp [hd2_nz]
    dsimp [d2, dx, dy]; ring
  · dsimp [F, t]
    field_simp [hd2_nz]
    dsimp [d2, dx, dy]; ring
  · dsimp [Q, dx, dy]; ring

/-- **Exercise 6.1(d) — Line through a point parallel to a given line** (§6.1, pp. 54, 57):
Given constructible `A ≠ B` and a constructible point `P`, `Q = P + (B - A)` is constructible with
`Q ≠ P`, `P ∈ garlingLine P Q`, and `garlingLine P Q` is parallel to `garlingLine A B` (disjoint
from `garlingLine A B` whenever `P ∉ garlingLine A B`, and equal to `garlingLine A B` otherwise). -/
theorem exercise_6_1_parallel_line {A B P : PlanePoint}
    (hA : IsConstructible A) (hB : IsConstructible B) (hP : IsConstructible P) (hAB : A ≠ B) :
    ∃ Q : PlanePoint, IsConstructible Q ∧ Q ≠ P ∧ P ∈ garlingLine P Q ∧
      (Q.1 - P.1 = B.1 - A.1 ∧ Q.2 - P.2 = B.2 - A.2) ∧
      (P ∉ garlingLine A B → garlingLine P Q ∩ garlingLine A B = ∅) ∧
      (P ∈ garlingLine A B → garlingLine P Q = garlingLine A B) := by
  let K := constructibleSubfield
  obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
  obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
  obtain ⟨hP1, hP2⟩ := (isConstructible_iff_mem_constructibleSubfield P.1 P.2).mp hP
  let Q : PlanePoint := (P.1 + (B.1 - A.1), P.2 + (B.2 - A.2))
  have hQ : IsConstructible Q :=
    (isConstructible_iff_mem_constructibleSubfield _ _).mpr
      ⟨K.add_mem hP1 (K.sub_mem hB1 hA1), K.add_mem hP2 (K.sub_mem hB2 hA2)⟩
  have hQP : Q ≠ P := by
    intro hEq
    have h1 := congrArg Prod.fst hEq
    have h2 := congrArg Prod.snd hEq
    apply hAB
    ext <;> dsimp [Q] at h1 h2 <;> linarith
  refine ⟨Q, hQ, hQP, mem_garlingLine_left P Q, ⟨by dsimp [Q]; ring, by dsimp [Q]; ring⟩, ?_, ?_⟩
  · intro hPnot
    ext X
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hX1, hX2⟩
    apply hPnot
    dsimp [garlingLine, Q] at hX1 hX2 ⊢
    linear_combination hX2 - hX1
  · intro hPin
    have hQin : Q ∈ garlingLine A B := by
      dsimp [garlingLine, Q] at hPin ⊢
      linear_combination hPin
    exact garlingLine_eq_of_mem hAB hQP.symm hPin hQin

/-- **Exercise 6.1(e) — Dividing a given interval in a rational ratio** (§6.1, pp. 54, 57):
Given constructible endpoints `A, B` and rational numbers `p, q : ℚ` with `p + q ≠ 0` (as well as
any affine rational parameter `r : ℚ`), the division point `(q/(p+q)) • A + (p/(p+q)) • B` is
constructible and lies on `garlingLine A B`. -/
theorem exercise_6_1_divide_interval_rat :
    (∀ {A B : PlanePoint} (r : ℚ), IsConstructible A → IsConstructible B →
      let R := ((1 - (r : ℝ)) * A.1 + (r : ℝ) * B.1, (1 - (r : ℝ)) * A.2 + (r : ℝ) * B.2)
      IsConstructible R ∧ R ∈ garlingLine A B) ∧
    (∀ {A B : PlanePoint} (p q : ℚ), p + q ≠ 0 → IsConstructible A → IsConstructible B →
      let r : ℚ := p / (p + q)
      let R := ((1 - (r : ℝ)) * A.1 + (r : ℝ) * B.1, (1 - (r : ℝ)) * A.2 + (r : ℝ) * B.2)
      IsConstructible R ∧ R ∈ garlingLine A B ∧
        ((q : ℝ) * (R.1 - A.1) = (p : ℝ) * (B.1 - R.1) ∧
         (q : ℝ) * (R.2 - A.2) = (p : ℝ) * (B.2 - R.2))) := by
  have haff : ∀ {A B : PlanePoint} (r : ℚ), IsConstructible A → IsConstructible B →
      let R := ((1 - (r : ℝ)) * A.1 + (r : ℝ) * B.1, (1 - (r : ℝ)) * A.2 + (r : ℝ) * B.2)
      IsConstructible R ∧ R ∈ garlingLine A B := by
    intro A B r hA hB R
    let K := constructibleSubfield
    obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
    obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
    have hr : (r : ℝ) ∈ K := SubfieldClass.ratCast_mem K r
    have h1mr : 1 - (r : ℝ) ∈ K := K.sub_mem K.one_mem hr
    refine ⟨(isConstructible_iff_mem_constructibleSubfield _ _).mpr
      ⟨K.add_mem (K.mul_mem h1mr hA1) (K.mul_mem hr hB1),
       K.add_mem (K.mul_mem h1mr hA2) (K.mul_mem hr hB2)⟩, ?_⟩
    dsimp [garlingLine, R]; ring
  refine ⟨haff, fun {A B} p q hpq hA hB => ?_⟩
  obtain ⟨hc, hl⟩ := haff (p / (p + q)) hA hB
  have hpqR : (p : ℝ) + (q : ℝ) ≠ 0 := by exact_mod_cast hpq
  refine ⟨hc, hl, ?_, ?_⟩
  · push_cast; field_simp [hpqR]; ring
  · push_cast; field_simp [hpqR]; ring

/-- **Exercise 6.1(f) — Constructing any point with rational coordinates** (§6.1, pp. 54, 57):
Every point `(q₁, q₂) ∈ ℚ × ℚ` in `ℝ × ℝ` is constructible. -/
theorem exercise_6_1_rational_point (q₁ q₂ : ℚ) :
    IsConstructible ((q₁ : ℝ), (q₂ : ℝ)) :=
  (isConstructible_iff_mem_constructibleSubfield _ _).mpr
    ⟨SubfieldClass.ratCast_mem constructibleSubfield q₁,
     SubfieldClass.ratCast_mem constructibleSubfield q₂⟩

/-- **Exercise 6.1 (Bundled §6.1 first-paragraph constructions)** (§6.1, printed pp. 54, 57 /
PDF pp. 62, 65): combines all six ruler-and-compass construction families mentioned in the opening
paragraph of §6.1 (equilateral triangle, square, regular hexagon, angle bisection, perpendicular
from a point onto a line, parallel line through a point, rational-ratio interval division, and
points with rational coordinates). Note: the printed exercise is a non-propositional prompt
(*"Describe how the constructions mentioned in the first paragraph of Section 6.1 are made"*) and
its geometric line/ray formulations require non-degeneracy hypotheses (`A ≠ B` — see
`exercise_6_1_degenerate_line_counterexample`); it is accordingly also recorded in `QUEUE.md`. -/
theorem exercise_6_1 :
    (∀ q₁ q₂ : ℚ, IsConstructible ((q₁ : ℝ), (q₂ : ℝ))) ∧
    (∀ k : Fin 6,
      IsConstructible (Real.cos (2 * Real.pi * (k : ℝ) / 6),
        Real.sin (2 * Real.pi * (k : ℝ) / 6))) ∧
    (∀ {A B P : PlanePoint}, IsConstructible A → IsConstructible B → IsConstructible P → A ≠ B →
      (∃ C : PlanePoint, IsConstructible C ∧
        sqDist C A = sqDist A B ∧ sqDist C B = sqDist A B) ∧
      (∃ F Q : PlanePoint, IsConstructible F ∧ IsConstructible Q ∧ Q ≠ P ∧
        F ∈ garlingLine A B ∧ F ∈ garlingLine P Q ∧
        (P.1 - F.1) * (B.1 - A.1) + (P.2 - F.2) * (B.2 - A.2) = 0) ∧
      (∃ Q : PlanePoint, IsConstructible Q ∧ Q ≠ P ∧ P ∈ garlingLine P Q ∧
        (Q.1 - P.1 = B.1 - A.1 ∧ Q.2 - P.2 = B.2 - A.2))) ∧
    (∀ {O A B : PlanePoint},
      IsConstructible O → IsConstructible A → IsConstructible B → A ≠ O → B ≠ O →
      let dA := euclidDist A O
      let dB := euclidDist B O
      ∃ C : PlanePoint, IsConstructible C ∧ C ≠ O ∧
        ((C.1 - O.1) * ((A.1 - O.1) / dA) + (C.2 - O.2) * ((A.2 - O.2) / dA) =
         (C.1 - O.1) * ((B.1 - O.1) / dB) + (C.2 - O.2) * ((B.2 - O.2) / dB)) ∧
        0 ≤ (C.1 - O.1) * ((A.1 - O.1) / dA) + (C.2 - O.2) * ((A.2 - O.2) / dA)) ∧
    (∀ {A B : PlanePoint} (p q : ℚ), p + q ≠ 0 → IsConstructible A → IsConstructible B →
      let r : ℚ := p / (p + q)
      let R := ((1 - (r : ℝ)) * A.1 + (r : ℝ) * B.1, (1 - (r : ℝ)) * A.2 + (r : ℝ) * B.2)
      IsConstructible R ∧ R ∈ garlingLine A B) := by
  refine ⟨exercise_6_1_rational_point, exercise_6_1_polygons.2, ?_, ?_, ?_⟩
  · intro A B P hA hB hP hAB
    obtain ⟨heq, _⟩ := exercise_6_1_polygons.1 hA hB hAB
    obtain ⟨F, Q, hF, hQ, hQP, hFL, hFPQ, horth, _⟩ := exercise_6_1_drop_perpendicular hA hB hP hAB
    obtain ⟨Qp, hQp, hQpP, hPin, hdir, _, _⟩ := exercise_6_1_parallel_line hA hB hP hAB
    exact ⟨heq, ⟨F, Q, hF, hQ, hQP, hFL, hFPQ, horth⟩, ⟨Qp, hQp, hQpP, hPin, hdir⟩⟩
  · intro O A B hO hA hB hAO hBO
    exact exercise_6_1_bisect_angle hO hA hB hAO hBO
  · intro A B p q hpq hA hB
    obtain ⟨hc, hl, _⟩ := exercise_6_1_divide_interval_rat.2 p q hpq hA hB
    exact ⟨hc, hl⟩

/-! ### Regular `n`-gon constructibility formulations & Exercise 6.3 (printed p. 57; cf. §19.3 p. 152) -/

/-- **(Formulation A — Garling §19.3 unit-circle generator, p. 152):**
Constructing `(cos(2π/n), sin(2π/n))`. -/
def IsGarlingUnitCircleGeneratorConstructible (n : ℕ) : Prop :=
  IsConstructible (Real.cos (2 * Real.pi / (n : ℝ)), Real.sin (2 * Real.pi / (n : ℝ)))

/-- **(Formulation B — All `n` vertices on the unit circle):**
Every vertex `(cos(2πk/n), sin(2πk/n))` (`k : Fin n`) of the unit-circle regular `n`-gon is
constructible. -/
def IsUnitCircleRegularPolygonConstructible (n : ℕ) : Prop :=
  ∀ k : Fin n, IsConstructible
    (Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)), Real.sin (2 * Real.pi * (k : ℝ) / (n : ℝ)))

/-- Vertex `V_k` (`0 ≤ k < n`) of the unit-side regular `n`-gon built on the unit segment
`P₀ = (0, 0)`, `P₁ = (1, 0)` (Garling §19.3, printed p. 152: *"By constructing a regular n-gon
(n > 2), we mean constructing a regular n-gon of side length 1"*). -/
noncomputable def unitSideRegularPolygonVertex (n : ℕ) (k : Fin n) : PlanePoint :=
  (∑ j ∈ Finset.range (k : ℕ), Real.cos (2 * Real.pi * (j : ℝ) / (n : ℝ)),
   ∑ j ∈ Finset.range (k : ℕ), Real.sin (2 * Real.pi * (j : ℝ) / (n : ℝ)))

/-- **(Formulation C — All `n` vertices of the unit-side regular `n`-gon on `P₀P₁`, §19.3 p. 152):** -/
def IsUnitSideRegularPolygonConstructible (n : ℕ) : Prop :=
  ∀ k : Fin n, IsConstructible (unitSideRegularPolygonVertex n k)

/-- **(Formulation D — Any non-degenerate Euclidean regular `n`-gon in the plane):**
There exist a centre `O ∈ ℝ × ℝ`, circumradius `R > 0`, phase angle `φ ∈ ℝ`, and orientation
`orient : Bool` (`+1` counterclockwise or `-1` clockwise) such that all `n` vertices are
constructible. -/
def IsAnyRegularPolygonConstructible (n : ℕ) : Prop :=
  ∃ (O : PlanePoint) (R φ : ℝ) (orient : Bool), 0 < R ∧
    ∀ k : Fin n, IsConstructible
      (O.1 + R * Real.cos (φ + (if orient then 1 else -1) * (2 * Real.pi * (k : ℝ) / (n : ℝ))),
       O.2 + R * Real.sin (φ + (if orient then 1 else -1) * (2 * Real.pi * (k : ℝ) / (n : ℝ))))

/-- Basic sanity properties of `unitSideRegularPolygonVertex`: for `3 ≤ n`, `V_0 = P₀`, `V_1 = P₁`,
and every consecutive step `V_{k+1} - V_k` has unit length `sqDist = 1`. -/
theorem unitSideRegularPolygonVertex_props {n : ℕ} (hn : 3 ≤ n) :
    unitSideRegularPolygonVertex n ⟨0, by omega⟩ = P₀ ∧
    unitSideRegularPolygonVertex n ⟨1, by omega⟩ = P₁ ∧
    ∀ (k : ℕ) (hk : k + 1 < n),
      sqDist (unitSideRegularPolygonVertex n ⟨k + 1, hk⟩)
             (unitSideRegularPolygonVertex n ⟨k, by omega⟩) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [unitSideRegularPolygonVertex, P₀]
  · ext <;> simp [unitSideRegularPolygonVertex, P₁]
  · intro k hk
    dsimp [sqDist, unitSideRegularPolygonVertex]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_sub_cancel_left, add_sub_cancel_left]
    exact Real.cos_sq_add_sin_sq _

/-- Equivalence of all four regular `n`-gon constructibility formulations + `cos(2π/n) ∈ K` for
every `n ≥ 3`. -/
theorem regularPolygon_constructible_iff {n : ℕ} (hn : 3 ≤ n) :
    (Real.cos (2 * Real.pi / (n : ℝ)) ∈ constructibleSubfield ↔
      IsGarlingUnitCircleGeneratorConstructible n) ∧
    (IsGarlingUnitCircleGeneratorConstructible n ↔
      IsUnitCircleRegularPolygonConstructible n) ∧
    (IsUnitCircleRegularPolygonConstructible n ↔
      IsUnitSideRegularPolygonConstructible n) ∧
    (IsUnitSideRegularPolygonConstructible n ↔
      IsAnyRegularPolygonConstructible n) := by
  let K := constructibleSubfield
  let θ : ℝ := 2 * Real.pi / (n : ℝ)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn_ge3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hθ_pos : 0 < θ := by dsimp [θ]; positivity
  have hθ_lt_pi : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hn_pos]
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
  -- (0) ↔ (A)
  have h0A : Real.cos θ ∈ K ↔ IsGarlingUnitCircleGeneratorConstructible n := by
    constructor
    · intro hc
      have h1mc2 : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
        linear_combination -(Real.sin_sq_add_cos_sq θ)
      have hsin_eq : Real.sin θ = Real.sqrt (1 - Real.cos θ ^ 2) := by
        rw [h1mc2, Real.sqrt_sq (le_of_lt hsin_pos)]
      have hs : Real.sin θ ∈ K := by
        rw [hsin_eq]
        exact sqrt_mem_constructibleSubfield
          (K.sub_mem K.one_mem (K.pow_mem hc 2))
          (by rw [h1mc2]; positivity)
      exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr ⟨hc, hs⟩
    · intro hgen
      exact ((isConstructible_iff_mem_constructibleSubfield _ _).mp hgen).1
  -- (A) → (B)
  have hAB : IsGarlingUnitCircleGeneratorConstructible n →
      IsUnitCircleRegularPolygonConstructible n := by
    intro hgen
    obtain ⟨hc1, hs1⟩ := (isConstructible_iff_mem_constructibleSubfield _ _).mp hgen
    have hmul : ∀ m : ℕ, Real.cos ((m : ℝ) * θ) ∈ K ∧ Real.sin ((m : ℝ) * θ) ∈ K := by
      intro m
      induction m with
      | zero =>
        simp [K.one_mem, K.zero_mem]
      | succ m ih =>
        have hadd : ((m + 1 : ℕ) : ℝ) * θ = (m : ℝ) * θ + θ := by push_cast; ring
        rw [hadd, Real.cos_add, Real.sin_add]
        exact ⟨K.sub_mem (K.mul_mem ih.1 hc1) (K.mul_mem ih.2 hs1),
               K.add_mem (K.mul_mem ih.2 hc1) (K.mul_mem ih.1 hs1)⟩
    intro k
    have harg : 2 * Real.pi * (k : ℝ) / (n : ℝ) = ((k : ℕ) : ℝ) * θ := by
      dsimp [θ]; ring
    rw [harg]
    exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr (hmul k)
  -- (B) → (C)
  have hBC : IsUnitCircleRegularPolygonConstructible n →
      IsUnitSideRegularPolygonConstructible n := by
    intro hB k
    have hsum : ∀ m : ℕ, m ≤ n →
        (∑ j ∈ Finset.range m, Real.cos (2 * Real.pi * (j : ℝ) / (n : ℝ))) ∈ K ∧
        (∑ j ∈ Finset.range m, Real.sin (2 * Real.pi * (j : ℝ) / (n : ℝ))) ∈ K := by
      intro m hm
      induction m with
      | zero =>
        simp [K.zero_mem]
      | succ m ih =>
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨hm1, hm2⟩ :=
          (isConstructible_iff_mem_constructibleSubfield _ _).mp (hB ⟨m, hm⟩)
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        exact ⟨K.add_mem ih1 hm1, K.add_mem ih2 hm2⟩
    exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr (hsum k (le_of_lt k.isLt))
  -- (C) → (A)
  have hCA : IsUnitSideRegularPolygonConstructible n →
      IsGarlingUnitCircleGeneratorConstructible n := by
    intro hC
    obtain ⟨v2x, v2y⟩ :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mp (hC ⟨2, by omega⟩)
    dsimp [unitSideRegularPolygonVertex] at v2x v2y
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at v2x v2y
    simp only [Nat.cast_zero, mul_zero, zero_div, Real.cos_zero, Real.sin_zero, zero_add,
      Nat.cast_one, mul_one] at v2x v2y
    have hcx : Real.cos θ ∈ K := by
      have := K.sub_mem v2x K.one_mem
      convert this using 1; dsimp [θ]; ring
    have hcy : Real.sin θ ∈ K := v2y
    exact (isConstructible_iff_mem_constructibleSubfield _ _).mpr ⟨hcx, hcy⟩
  -- (B) → (D)
  have hBD : IsUnitCircleRegularPolygonConstructible n →
      IsAnyRegularPolygonConstructible n := by
    intro hB
    refine ⟨(0, 0), 1, 0, true, zero_lt_one, fun k => ?_⟩
    simpa using hB k
  -- (D) → (0)
  have hD0 : IsAnyRegularPolygonConstructible n → Real.cos θ ∈ K := by
    rintro ⟨O, R, φ, orient, hR_pos, hverts⟩
    let sgn : ℝ := if orient then 1 else -1
    let δ : ℝ := sgn * θ
    have hcos_δ : Real.cos δ = Real.cos θ := by
      dsimp [δ, sgn]
      split_ifs <;> simp [Real.cos_neg]
    obtain ⟨w0x, w0y⟩ :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mp (hverts ⟨0, by omega⟩)
    obtain ⟨w1x, w1y⟩ :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mp (hverts ⟨1, by omega⟩)
    obtain ⟨w2x, w2y⟩ :=
      (isConstructible_iff_mem_constructibleSubfield _ _).mp (hverts ⟨2, by omega⟩)
    let u1 := (O.1 + R * Real.cos (φ + sgn * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ)))) -
              (O.1 + R * Real.cos (φ + sgn * (2 * Real.pi * ((0 : ℕ) : ℝ) / (n : ℝ))))
    let u2 := (O.2 + R * Real.sin (φ + sgn * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ)))) -
              (O.2 + R * Real.sin (φ + sgn * (2 * Real.pi * ((0 : ℕ) : ℝ) / (n : ℝ))))
    let v1 := (O.1 + R * Real.cos (φ + sgn * (2 * Real.pi * ((2 : ℕ) : ℝ) / (n : ℝ)))) -
              (O.1 + R * Real.cos (φ + sgn * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ))))
    let v2 := (O.2 + R * Real.sin (φ + sgn * (2 * Real.pi * ((2 : ℕ) : ℝ) / (n : ℝ)))) -
              (O.2 + R * Real.sin (φ + sgn * (2 * Real.pi * ((1 : ℕ) : ℝ) / (n : ℝ))))
    have hu1_K : u1 ∈ K := K.sub_mem w1x w0x
    have hu2_K : u2 ∈ K := K.sub_mem w1y w0y
    have hv1_K : v1 ∈ K := K.sub_mem w2x w1x
    have hv2_K : v2 ∈ K := K.sub_mem w2y w1y
    have hu1_eq : u1 = R * (Real.cos (φ + δ) - Real.cos φ) := by
      dsimp [u1, δ, θ]; push_cast
      have h0 : φ + sgn * (2 * Real.pi * 0 / (n : ℝ)) = φ := by ring
      have h1 : φ + sgn * (2 * Real.pi * 1 / (n : ℝ)) = φ + sgn * (2 * Real.pi / (n : ℝ)) := by
        ring
      rw [h0, h1]; ring
    have hu2_eq : u2 = R * (Real.sin (φ + δ) - Real.sin φ) := by
      dsimp [u2, δ, θ]; push_cast
      have h0 : φ + sgn * (2 * Real.pi * 0 / (n : ℝ)) = φ := by ring
      have h1 : φ + sgn * (2 * Real.pi * 1 / (n : ℝ)) = φ + sgn * (2 * Real.pi / (n : ℝ)) := by
        ring
      rw [h0, h1]; ring
    have hv1_eq : v1 = R * (Real.cos ((φ + δ) + δ) - Real.cos (φ + δ)) := by
      dsimp [v1, δ, θ]; push_cast
      have h1 : φ + sgn * (2 * Real.pi * 1 / (n : ℝ)) = φ + sgn * (2 * Real.pi / (n : ℝ)) := by
        ring
      have h2 : φ + sgn * (2 * Real.pi * 2 / (n : ℝ)) =
          (φ + sgn * (2 * Real.pi / (n : ℝ))) + sgn * (2 * Real.pi / (n : ℝ)) := by ring
      rw [h1, h2]; ring
    have hv2_eq : v2 = R * (Real.sin ((φ + δ) + δ) - Real.sin (φ + δ)) := by
      dsimp [v2, δ, θ]; push_cast
      have h1 : φ + sgn * (2 * Real.pi * 1 / (n : ℝ)) = φ + sgn * (2 * Real.pi / (n : ℝ)) := by
        ring
      have h2 : φ + sgn * (2 * Real.pi * 2 / (n : ℝ)) =
          (φ + sgn * (2 * Real.pi / (n : ℝ))) + sgn * (2 * Real.pi / (n : ℝ)) := by ring
      rw [h1, h2]; ring
    have hscφ : Real.sin φ ^ 2 + Real.cos φ ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
    have hscδ : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
    have hnorm : u1 ^ 2 + u2 ^ 2 = 2 * R ^ 2 * (1 - Real.cos δ) := by
      rw [hu1_eq, hu2_eq, Real.cos_add, Real.sin_add]
      linear_combination
        R ^ 2 * (1 - 2 * Real.cos δ + Real.sin δ ^ 2 + Real.cos δ ^ 2) * hscφ +
        R ^ 2 * hscδ
    have hdot : u1 * v1 + u2 * v2 = (u1 ^ 2 + u2 ^ 2) * Real.cos δ := by
      rw [hnorm, hv1_eq, hv2_eq, hu1_eq, hu2_eq]
      rw [Real.cos_add (φ + δ) δ, Real.sin_add (φ + δ) δ, Real.cos_add φ δ, Real.sin_add φ δ]
      linear_combination
        R ^ 2 *
          ((Real.cos δ - 1) * (Real.cos δ ^ 2 - Real.sin δ ^ 2 - Real.cos δ) +
            Real.sin δ * (2 * Real.sin δ * Real.cos δ - Real.sin δ)) * hscφ +
        R ^ 2 * Real.cos δ * hscδ
    have hcos_lt1 : Real.cos θ < 1 := by
      have hsc := Real.sin_sq_add_cos_sq θ
      have hs2_pos : 0 < Real.sin θ ^ 2 := sq_pos_of_pos hsin_pos
      nlinarith
    have hnorm_pos : 0 < u1 ^ 2 + u2 ^ 2 := by
      rw [hnorm, hcos_δ]
      have : 0 < 1 - Real.cos θ := by linarith
      positivity
    have hcos_eq : Real.cos θ = (u1 * v1 + u2 * v2) / (u1 ^ 2 + u2 ^ 2) := by
      rw [← hcos_δ, hdot, mul_div_cancel_left₀ _ (ne_of_gt hnorm_pos)]
    rw [hcos_eq]
    exact K.div_mem
      (K.add_mem (K.mul_mem hu1_K hv1_K) (K.mul_mem hu2_K hv2_K))
      (K.add_mem (K.pow_mem hu1_K 2) (K.pow_mem hu2_K 2))
  refine ⟨h0A, ⟨hAB, fun hB => hCA (hBC hB)⟩, ⟨hBC, fun hC => hAB (hCA hC)⟩, ?_⟩
  exact ⟨fun hC => hBD (hAB (hCA hC)), fun hD => hBC (hAB (h0A.mp (hD0 hD)))⟩

/-- Exact radical value `cos(2π/5) = (√5 - 1) / 4`. -/
theorem cos_two_pi_div_five :
    Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  let θ : ℝ := 2 * Real.pi / 5
  let c : ℝ := Real.cos θ
  have h32 : Real.cos (3 * θ) = Real.cos (2 * θ) := by
    have h5 : 3 * θ = 2 * Real.pi - 2 * θ := by dsimp [θ]; ring
    rw [h5, Real.cos_two_pi_sub]
  rw [Real.cos_three_mul, Real.cos_two_mul] at h32
  have hfac : (c - 1) * (4 * c ^ 2 + 2 * c - 1) = 0 := by
    dsimp [c]; linear_combination h32
  have hc_pos : 0 < c := by
    dsimp [c]
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · dsimp [θ]; linarith [Real.pi_pos]
    · dsimp [θ]; linarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin θ := by
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · dsimp [θ]; linarith [Real.pi_pos]
    · dsimp [θ]; linarith [Real.pi_pos]
  have hc_ne1 : c - 1 ≠ 0 := by
    intro h1
    have hc1 : c = 1 := by linarith
    have hsc := Real.sin_sq_add_cos_sq θ
    have hs2 : 0 < Real.sin θ ^ 2 := sq_pos_of_pos hsin_pos
    change Real.sin θ ^ 2 + c ^ 2 = 1 at hsc
    rw [hc1] at hsc
    linarith
  have hquad : 4 * c ^ 2 + 2 * c - 1 = 0 := (mul_eq_zero.mp hfac).resolve_left hc_ne1
  have hsq5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hprod : (4 * c + 1 - Real.sqrt 5) * (4 * c + 1 + Real.sqrt 5) = 0 := by
    linear_combination 4 * hquad - hsq5
  have hsum_pos : 4 * c + 1 + Real.sqrt 5 ≠ 0 := by
    have hs5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  have hlin : 4 * c + 1 - Real.sqrt 5 = 0 := (mul_eq_zero.mp hprod).resolve_right hsum_pos
  change c = (Real.sqrt 5 - 1) / 4
  linarith

/-- **Exercise 6.3** (§6.1, printed p. 57 / PDF p. 65; cf. §19.3 p. 152):
*"Construct a regular pentagon."*
Proves constructibility of the regular pentagon simultaneously across all four natural formulations:
1. Garling's §19.3 unit-circle generator `(cos(2π/5), sin(2π/5))`;
2. all `5` vertices `(cos(2πk/5), sin(2πk/5))` on the unit circle;
3. all `5` vertices of the unit-side regular pentagon built on `P₀P₁` (§19.3 p. 152); and
4. existence of a non-degenerate constructible regular pentagon in the plane. -/
theorem exercise_6_3 :
    IsGarlingUnitCircleGeneratorConstructible 5 ∧
    IsUnitCircleRegularPolygonConstructible 5 ∧
    IsUnitSideRegularPolygonConstructible 5 ∧
    IsAnyRegularPolygonConstructible 5 := by
  obtain ⟨h0A, hAB, hBC, hCD⟩ := regularPolygon_constructible_iff (n := 5) (by omega)
  have hcos : Real.cos (2 * Real.pi / (5 : ℝ)) ∈ constructibleSubfield := by
    rw [cos_two_pi_div_five]
    let K := constructibleSubfield
    have hs5 : Real.sqrt 5 ∈ K :=
      sqrt_mem_constructibleSubfield
        (by exact_mod_cast SubfieldClass.ratCast_mem K (5 : ℚ)) (by norm_num)
    exact K.div_mem (K.sub_mem hs5 K.one_mem)
      (by exact_mod_cast SubfieldClass.ratCast_mem K (4 : ℚ))
  have hA := h0A.mp hcos
  have hB := hAB.mp hA
  have hC := hBC.mp hB
  have hD := hCD.mp hC
  exact ⟨hA, hB, hC, hD⟩

/-! ## §6.2 The angle `π/3` cannot be trisected & Exercises 6.5–6.6 (printed p. 57, PDF p. 65) -/

/-- Field-theoretic impossibility mechanism of §6.2 (printed p. 57 / PDF p. 65):
if `α ∈ ℚ(x, y)` is algebraic over `ℚ` with minimal polynomial of degree `3`, then `P = (x, y)` is
not constructible (combining `Theorem 4.4`, `Theorem 4.2`, and `Theorem 6.1`). -/
theorem not_isConstructible_of_minpoly_deg_three {x y α : ℝ}
    (hα_mem : α ∈ ratPointField x y)
    (hα_alg : IsGarlingAlgebraic ℚ α)
    (hdeg : (minpoly ℚ α).natDegree = 3) :
    ¬ IsConstructible (x, y) := by
  intro hP
  obtain ⟨hfin, r, hr_enat, hr_nat⟩ := theorem_6_1 hP
  have hdeg_Qα : extDegree ℚ (IntermediateField.adjoin ℚ ({α} : Set ℝ)) = (3 : ℕ∞) := by
    rw [((theorem_4_4 (K := ℚ) (L := ℝ) α).2 hα_alg).2, hdeg]
    rfl
  have hle : IntermediateField.adjoin ℚ ({α} : Set ℝ) ≤ ratPointField x y := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact hα_mem
  let E := IntermediateField.adjoin ℚ ({α} : Set ℝ)
  let M := ratPointField x y
  let _ : Algebra E M := (IntermediateField.inclusion hle).toAlgebra
  have _ : IsScalarTower ℚ E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Explicit invocation of Garling's `Theorem 4.2` (`[M : ℚ] = [M : E] [E : ℚ]`) as on p. 57:
  have htower := theorem_4_2 ℚ E M
  have _ : Module.Finite ℚ M := (isFiniteExtension_iff_moduleFinite ℚ M).mp hfin
  have _ : Module.Finite ℚ E := Module.Finite.left ℚ E M
  have _ : Module.Finite E M := Module.Finite.right ℚ E M
  rw [hr_enat, extDegree_eq_finrank E M, hdeg_Qα] at htower
  have hmul : Module.finrank E M * 3 = 2 ^ r := by
    have hcast : ((Module.finrank E M * 3 : ℕ) : ℕ∞) = ((2 ^ r : ℕ) : ℕ∞) := by
      push_cast
      exact htower.symm
    exact Nat.cast_injective hcast
  have hdvd3 : 3 ∣ 2 ^ r := ⟨Module.finrank E M, by omega⟩
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hdvd3
  omega

/-- Convenience corollary of `not_isConstructible_of_minpoly_deg_three` for a monic irreducible
cubic `p : ℚ[X]`. -/
theorem not_isConstructible_of_irr_monic_cubic {x y α : ℝ} {p : ℚ[X]}
    (hα_mem : α ∈ ratPointField x y)
    (hp_monic : p.Monic) (hp_irr : Irreducible p) (hp_deg : p.natDegree = 3)
    (hp_eval : Polynomial.aeval α p = 0) :
    ¬ IsConstructible (x, y) := by
  have hmin : minpoly ℚ α = p :=
    (minpoly.eq_of_irreducible_of_monic hp_irr hp_eval hp_monic).symm
  refine not_isConstructible_of_minpoly_deg_three hα_mem ⟨p, hp_monic.ne_zero, hp_eval⟩ ?_
  rw [hmin, hp_deg]

/-- **§6.2 Main-text prose theorem — Point form** (§6.2, printed p. 57 / PDF p. 65):
The point `(cos(π/9), sin(π/9))` is not constructible by ruler and compasses (since `2 cos(π/9)` is
a root of `x³ - 3x - 1`, which is irreducible over `ℚ` by §5.1 `example_5_1_cubic_irreducible`). -/
theorem not_isConstructible_cos_sin_pi_div_nine :
    ¬ IsConstructible (Real.cos (Real.pi / 9), Real.sin (Real.pi / 9)) := by
  let x := Real.cos (Real.pi / 9)
  let y := Real.sin (Real.pi / 9)
  let α := 2 * x
  have hx_mem : x ∈ ratPointField x y :=
    IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inl rfl)
  have hα_mem : α ∈ ratPointField x y :=
    (ratPointField x y).mul_mem ((ratPointField x y).algebraMap_mem 2) hx_mem
  let p : ℚ[X] := Polynomial.X ^ 3 - 3 * Polynomial.X - 1
  have hp_deg : p.natDegree = 3 := by dsimp [p]; compute_degree!
  have hp_monic : p.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hp_deg]
    dsimp [p]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
  have hp_irr : Irreducible p := example_5_1_cubic_irreducible.2.2.2
  have hcos3 : Real.cos (3 * (Real.pi / 9)) = 1 / 2 := by
    have : 3 * (Real.pi / 9) = Real.pi / 3 := by ring
    rw [this, Real.cos_pi_div_three]
  rw [Real.cos_three_mul] at hcos3
  have hp_eval : Polynomial.aeval α p = 0 := by
    dsimp [p, α, x]
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one, Polynomial.aeval_X]
    linear_combination 2 * hcos3
  exact not_isConstructible_of_irr_monic_cubic hα_mem hp_monic hp_irr hp_deg hp_eval

/-- **§6.2 Main-text prose theorem — Geometric trisection of `π/3`** (§6.2, printed p. 57 /
PDF p. 65):
1. The angle `π/3` itself is constructible: `(cos(π/3), sin(π/3)) = (1/2, √3/2)` is constructible.
2. `(cos(π/9), sin(π/9))` is not constructible.
3. No non-origin point `Q ≠ P₀` lying on the trisecting line through `P₀` at angle `π/9`
   (`Q.1 * sin(π/9) = Q.2 * cos(π/9)`) is constructible. -/
theorem angle_pi_div_three_cannot_be_trisected :
    IsConstructible (Real.cos (Real.pi / 3), Real.sin (Real.pi / 3)) ∧
    ¬ IsConstructible (Real.cos (Real.pi / 9), Real.sin (Real.pi / 9)) ∧
    ¬ ∃ Q : PlanePoint, Q ≠ P₀ ∧ IsConstructible Q ∧
        Q.1 * Real.sin (Real.pi / 9) = Q.2 * Real.cos (Real.pi / 9) := by
  refine ⟨?_, not_isConstructible_cos_sin_pi_div_nine, ?_⟩
  · rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
    exact isConstructible_equilateral_apex
  · rintro ⟨Q, hQ0, hQ, hray⟩
    let K := constructibleSubfield
    obtain ⟨hQ1, hQ2⟩ := (isConstructible_iff_mem_constructibleSubfield Q.1 Q.2).mp hQ
    let d := euclidDist Q P₀
    have hd_pos : 0 < d := Real.sqrt_pos.mpr (sqDist_pos_iff.mpr hQ0)
    have hd_ne : d ≠ 0 := ne_of_gt hd_pos
    have hd_K : d ∈ K := sqrt_mem_constructibleSubfield
      (K.add_mem (K.pow_mem (K.sub_mem hQ1 K.zero_mem) 2)
                 (K.pow_mem (K.sub_mem hQ2 K.zero_mem) 2))
      (sqDist_nonneg Q P₀)
    have hd2 : d ^ 2 = Q.1 ^ 2 + Q.2 ^ 2 := by
      have h := euclidDist_sq Q P₀
      dsimp [d, P₀]
      dsimp [sqDist, P₀] at h
      linear_combination h
    let c := Real.cos (Real.pi / 9)
    let s := Real.sin (Real.pi / 9)
    have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.pi / 9)
    have hz : Q.1 * s - Q.2 * c = 0 := by dsimp [c, s]; linarith
    have hdet : (Q.1 * c + Q.2 * s) ^ 2 = d ^ 2 := by
      calc
        (Q.1 * c + Q.2 * s) ^ 2
            = (Q.1 * c + Q.2 * s) ^ 2 + (Q.1 * s - Q.2 * c) ^ 2 := by
                rw [hz]; ring
        _ = (Q.1 ^ 2 + Q.2 ^ 2) * (s ^ 2 + c ^ 2) := by ring
        _ = d ^ 2 := by rw [hd2, hsc, mul_one]
    have hpm : Q.1 * c + Q.2 * s = d ∨ Q.1 * c + Q.2 * s = -d := by
      have : (Q.1 * c + Q.2 * s - d) * (Q.1 * c + Q.2 * s + d) = 0 := by
        linear_combination hdet
      rcases mul_eq_zero.mp this with h1 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hc_eq : c = (Q.1 / d) ∨ c = -(Q.1 / d) := by
      rcases hpm with hpos | hneg
      · left
        have h1 : Q.1 = d * c := by
          linear_combination c * hpos + s * hz - Q.1 * hsc
        field_simp [hd_ne]; linarith
      · right
        have h1 : Q.1 = -(d * c) := by
          linear_combination c * hneg + s * hz - Q.1 * hsc
        field_simp [hd_ne]; linarith
    have hs_eq : s = (Q.2 / d) ∨ s = -(Q.2 / d) := by
      rcases hpm with hpos | hneg
      · left
        have h2 : Q.2 = d * s := by
          linear_combination s * hpos - c * hz - Q.2 * hsc
        field_simp [hd_ne]; linarith
      · right
        have h2 : Q.2 = -(d * s) := by
          linear_combination s * hneg - c * hz - Q.2 * hsc
        field_simp [hd_ne]; linarith
    have hc_K : c ∈ K := by
      rcases hc_eq with h | h <;> rw [h]
      · exact K.div_mem hQ1 hd_K
      · exact K.neg_mem (K.div_mem hQ1 hd_K)
    have hs_K : s ∈ K := by
      rcases hs_eq with h | h <;> rw [h]
      · exact K.div_mem hQ2 hd_K
      · exact K.neg_mem (K.div_mem hQ2 hd_K)
    exact not_isConstructible_cos_sin_pi_div_nine
      ((isConstructible_iff_mem_constructibleSubfield c s).mpr ⟨hc_K, hs_K⟩)

/-- **Exercise 6.5** (§6.2, printed p. 57 / PDF p. 65):
*"Use the problem of the 'duplication of the cube' to show that `(2^(1/3), 0)` cannot be
constructed using ruler and compasses."*
Includes both the literal real cube-root point `((2 : ℝ) ^ ((1 : ℝ) / 3), 0)` and the geometric
duplication-of-the-cube consequence that no constructible segment `AB` can be the side of a cube of
volume `2` (`euclidDist A B ^ 3 = 2`). -/
theorem exercise_6_5 :
    ¬ IsConstructible ((2 : ℝ) ^ ((1 : ℝ) / 3), 0) ∧
    (∀ s : ℝ, s ^ 3 = 2 → ¬ IsConstructible (s, 0)) ∧
    ¬ ∃ A B : PlanePoint, IsConstructible A ∧ IsConstructible B ∧ euclidDist A B ^ 3 = 2 := by
  have hprime := real_rpow_inv_nat_minpoly_of_prime (p := 2) (n := 3) Nat.prime_two (by omega)
  dsimp at hprime
  obtain ⟨hpow3, halg, _, hdeg⟩ := hprime
  let α : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)
  have hnot_α : ¬ IsConstructible (α, 0) := by
    have hmem : α ∈ ratPointField α 0 :=
      IntermediateField.subset_adjoin ℚ ({α, (0 : ℝ)} : Set ℝ) (Or.inl rfl)
    exact not_isConstructible_of_minpoly_deg_three hmem halg hdeg
  have hα_pos : 0 < α := by
    dsimp [α]
    positivity
  have hcube_unique : ∀ s : ℝ, s ^ 3 = 2 → s = α := by
    intro s hs3
    have hα3 : α ^ 3 = 2 := by dsimp [α]; exact_mod_cast hpow3
    have hdiff : (s - α) * ((s + α / 2) ^ 2 + 3 * α ^ 2 / 4) = 0 := by
      linear_combination hs3 - hα3
    have hquad_pos : (s + α / 2) ^ 2 + 3 * α ^ 2 / 4 ≠ 0 := by
      have : 0 < 3 * α ^ 2 / 4 := by positivity
      have : 0 ≤ (s + α / 2) ^ 2 := sq_nonneg _
      linarith
    linarith [(mul_eq_zero.mp hdiff).resolve_right hquad_pos]
  refine ⟨hnot_α, fun s hs3 => by rw [hcube_unique s hs3]; exact hnot_α, ?_⟩
  rintro ⟨A, B, hA, hB, hvol⟩
  let K := constructibleSubfield
  obtain ⟨hA1, hA2⟩ := (isConstructible_iff_mem_constructibleSubfield A.1 A.2).mp hA
  obtain ⟨hB1, hB2⟩ := (isConstructible_iff_mem_constructibleSubfield B.1 B.2).mp hB
  have hd_K : euclidDist A B ∈ K := sqrt_mem_constructibleSubfield
    (K.add_mem (K.pow_mem (K.sub_mem hA1 hB1) 2) (K.pow_mem (K.sub_mem hA2 hB2) 2))
    (sqDist_nonneg A B)
  exact (hcube_unique (euclidDist A B) hvol ▸ hd_K |> hnot_α)

/-- **Exercise 6.6(a) — Regular nonagon (`9`-sided polygon)** (§6.2, printed p. 57 / PDF p. 65):
It is not possible to construct a regular nonagon using ruler and compasses (simultaneously across
all four regular-polygon constructibility formulations). -/
theorem exercise_6_6_a :
    ¬ IsGarlingUnitCircleGeneratorConstructible 9 ∧
    ¬ IsUnitCircleRegularPolygonConstructible 9 ∧
    ¬ IsUnitSideRegularPolygonConstructible 9 ∧
    ¬ IsAnyRegularPolygonConstructible 9 := by
  have hnot_A : ¬ IsGarlingUnitCircleGeneratorConstructible 9 := by
    let x := Real.cos (2 * Real.pi / (9 : ℝ))
    let y := Real.sin (2 * Real.pi / (9 : ℝ))
    let τ := -(2 * x)
    have hx_mem : x ∈ ratPointField x y :=
      IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inl rfl)
    have hτ_mem : τ ∈ ratPointField x y :=
      (ratPointField x y).neg_mem
        ((ratPointField x y).mul_mem ((ratPointField x y).algebraMap_mem 2) hx_mem)
    let p : ℚ[X] := Polynomial.X ^ 3 - 3 * Polynomial.X - 1
    have hp_deg : p.natDegree = 3 := by dsimp [p]; compute_degree!
    have hp_monic : p.Monic := by
      rw [Polynomial.Monic, Polynomial.leadingCoeff, hp_deg]
      dsimp [p]
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
    have hp_irr : Irreducible p := example_5_1_cubic_irreducible.2.2.2
    have hcos3 : Real.cos (3 * (2 * Real.pi / (9 : ℝ))) = -(1 / 2) := by
      have : 3 * (2 * Real.pi / (9 : ℝ)) = Real.pi - Real.pi / 3 := by ring
      rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [Real.cos_three_mul] at hcos3
    have hp_eval : Polynomial.aeval τ p = 0 := by
      dsimp [p, τ, x]
      simp only [map_sub, map_pow, map_mul, map_ofNat, map_one, Polynomial.aeval_X]
      linear_combination -2 * hcos3
    exact not_isConstructible_of_irr_monic_cubic hτ_mem hp_monic hp_irr hp_deg hp_eval
  obtain ⟨_, hAB, hBC, hCD⟩ := regularPolygon_constructible_iff (n := 9) (by omega)
  exact ⟨hnot_A, mt hAB.mpr hnot_A, mt (hAB.trans hBC).mpr hnot_A,
    mt ((hAB.trans hBC).trans hCD).mpr hnot_A⟩

/-- **Exercise 6.6(b) — Regular heptagon (`7`-sided polygon)** (§6.2, printed p. 57 / PDF p. 65):
It is not possible to construct a regular heptagon using ruler and compasses (simultaneously across
all four regular-polygon constructibility formulations, using Exercise 5.12's minimal polynomial
`x³ + x² - 2x - 1` of `2 cos(2π/7)`). -/
theorem exercise_6_6_b :
    ¬ IsGarlingUnitCircleGeneratorConstructible 7 ∧
    ¬ IsUnitCircleRegularPolygonConstructible 7 ∧
    ¬ IsUnitSideRegularPolygonConstructible 7 ∧
    ¬ IsAnyRegularPolygonConstructible 7 := by
  have hnot_A : ¬ IsGarlingUnitCircleGeneratorConstructible 7 := by
    let x := Real.cos (2 * Real.pi / (7 : ℝ))
    let y := Real.sin (2 * Real.pi / (7 : ℝ))
    let α := 2 * x
    have hx_mem : x ∈ ratPointField x y :=
      IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inl rfl)
    have hα_mem : α ∈ ratPointField x y :=
      (ratPointField x y).mul_mem ((ratPointField x y).algebraMap_mem 2) hx_mem
    have hmin_pair := exercise_5_12_two_cos
    dsimp at hmin_pair
    have hmin : minpoly ℚ α =
        (Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1 : ℚ[X]) := by
      simpa [α, x] using hmin_pair.1
    have hq_deg :
        (Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1 : ℚ[X]).natDegree = 3 := by
      compute_degree!
    have hdeg : (minpoly ℚ α).natDegree = 3 := by rw [hmin, hq_deg]
    have halg : IsGarlingAlgebraic ℚ α := by
      let q : ℚ[X] := Polynomial.X ^ 3 + Polynomial.X ^ 2 - 2 * Polynomial.X - 1
      have hq_ne : q ≠ 0 := by
        intro hz
        have := congrArg Polynomial.natDegree hz
        dsimp [q] at this; rw [hq_deg] at this; omega
      have hq_eval : Polynomial.aeval α q = 0 := by
        dsimp [q]; rw [← hmin]; exact minpoly.aeval ℚ α
      exact ⟨q, hq_ne, hq_eval⟩
    exact not_isConstructible_of_minpoly_deg_three hα_mem halg hdeg
  obtain ⟨_, hAB, hBC, hCD⟩ := regularPolygon_constructible_iff (n := 7) (by omega)
  exact ⟨hnot_A, mt hAB.mpr hnot_A, mt (hAB.trans hBC).mpr hnot_A,
    mt ((hAB.trans hBC).trans hCD).mpr hnot_A⟩

/-- **Exercise 6.6 (Combined)** (§6.2, printed p. 57 / PDF p. 65):
*"Show that it is not possible to construct a regular (a) nonagon (9-sided polygon) or (b) heptagon
(7-sided polygon) using ruler and compasses."* -/
theorem exercise_6_6 :
    (¬ IsGarlingUnitCircleGeneratorConstructible 9 ∧
     ¬ IsUnitCircleRegularPolygonConstructible 9 ∧
     ¬ IsUnitSideRegularPolygonConstructible 9 ∧
     ¬ IsAnyRegularPolygonConstructible 9) ∧
    (¬ IsGarlingUnitCircleGeneratorConstructible 7 ∧
     ¬ IsUnitCircleRegularPolygonConstructible 7 ∧
     ¬ IsUnitSideRegularPolygonConstructible 7 ∧
     ¬ IsAnyRegularPolygonConstructible 7) :=
  ⟨exercise_6_6_a, exercise_6_6_b⟩

/-! ## §6.3 Concluding remarks & Exercise 6.7 (printed p. 58, PDF p. 66) -/

/-- Quadratic tower step for `Exercise 6.7`: if `E ≤ F` are subfields of `ℝ` (viewed as
`IntermediateField ℚ ℝ`) with `(E : Set ℝ) ⊆ constructibleSubfield` and `[F : E] = 2`, then
`(F : Set ℝ) ⊆ constructibleSubfield`. -/
private theorem subset_constructibleSubfield_of_finrank_two
    {E F : IntermediateField ℚ ℝ} (hEF : E ≤ F)
    (hE : ∀ z ∈ E, z ∈ constructibleSubfield)
    (hdeg : let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
            Module.finrank E F = 2) :
    ∀ α ∈ F, α ∈ constructibleSubfield := by
  let _ : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have hfin : Module.Finite E F := Module.finite_of_finrank_pos (by omega)
  intro α hα
  let K := constructibleSubfield
  let αF : F := ⟨α, hα⟩
  have hint : IsIntegral E αF := Algebra.IsIntegral.isIntegral αF
  let p : E[X] := minpoly E αF
  have hp_monic : p.Monic := minpoly.monic hint
  have hp_eval : Polynomial.aeval αF p = 0 := minpoly.aeval E αF
  have hdvd : p.natDegree ∣ 2 := by
    have hrank_adj : Module.finrank E (IntermediateField.adjoin E ({αF} : Set F)) = p.natDegree :=
      IntermediateField.adjoin.finrank hint
    have hmul := Module.finrank_mul_finrank E (IntermediateField.adjoin E ({αF} : Set F)) F
    exact ⟨Module.finrank (IntermediateField.adjoin E ({αF} : Set F)) F,
      by rw [← hrank_adj, hmul, hdeg]⟩
  have hp_pos : 0 < p.natDegree := minpoly.natDegree_pos hint
  have hp_le2 : p.natDegree ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  have hdeg_cases : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
  rcases hdeg_cases with hd1 | hd2
  · -- Linear minimal polynomial `X + c₀`
    have hp_eq : p = Polynomial.X + Polynomial.C (p.coeff 0) := by
      ext k
      rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
      rcases k with _ | _ | k
      · simp
      · have hlead : p.coeff 1 = 1 := by
          rw [← hd1, ← Polynomial.leadingCoeff, hp_monic.leadingCoeff]
        simp [hlead]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    rw [hp_eq, map_add, Polynomial.aeval_X, Polynomial.aeval_C] at hp_eval
    have hval : α + (p.coeff 0 : ℝ) = 0 := congrArg Subtype.val hp_eval
    have hα_eq : α = -(p.coeff 0 : ℝ) := by linarith
    rw [hα_eq]
    exact K.neg_mem (hE (p.coeff 0 : ℝ) (p.coeff 0).2)
  · -- Quadratic minimal polynomial `X² + b X + c`: complete the square in `ℝ`
    have hp_eq :
        p = Polynomial.X ^ 2 + Polynomial.C (p.coeff 1) * Polynomial.X +
            Polynomial.C (p.coeff 0) := by
      ext k
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
      rcases k with _ | _ | _ | k
      · simp
      · simp
      · have hlead : p.coeff 2 = 1 := by
          rw [← hd2, ← Polynomial.leadingCoeff, hp_monic.leadingCoeff]
        simp [hlead]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    rw [hp_eq, map_add, map_add, map_pow, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C, Polynomial.aeval_C] at hp_eval
    let b : ℝ := (p.coeff 1 : ℝ)
    let c : ℝ := (p.coeff 0 : ℝ)
    have hb_K : b ∈ K := hE b (p.coeff 1).2
    have hc_K : c ∈ K := hE c (p.coeff 0).2
    have hquad : α ^ 2 + b * α + c = 0 := congrArg Subtype.val hp_eval
    have hsq : (α + b / 2) ^ 2 = (b / 2) ^ 2 - c := by linear_combination hquad
    have hdisc_nonneg : 0 ≤ (b / 2) ^ 2 - c := by rw [← hsq]; exact sq_nonneg _
    have htwo_K : (2 : ℝ) ∈ K := by exact_mod_cast SubfieldClass.ratCast_mem K (2 : ℚ)
    have hb2_K : b / 2 ∈ K := K.div_mem hb_K htwo_K
    have hdisc_K : (b / 2) ^ 2 - c ∈ K := K.sub_mem (K.pow_mem hb2_K 2) hc_K
    let s : ℝ := Real.sqrt ((b / 2) ^ 2 - c)
    have hs_K : s ∈ K := sqrt_mem_constructibleSubfield hdisc_K hdisc_nonneg
    have hs2 : s ^ 2 = (b / 2) ^ 2 - c := Real.sq_sqrt hdisc_nonneg
    have hprod : (α + b / 2 - s) * (α + b / 2 + s) = 0 := by linear_combination hsq - hs2
    rcases mul_eq_zero.mp hprod with h1 | h2
    · have hα_eq : α = s - b / 2 := by linarith
      rw [hα_eq]; exact K.sub_mem hs_K hb2_K
    · have hα_eq : α = -(b / 2) - s := by linarith
      rw [hα_eq]; exact K.sub_mem (K.neg_mem hb2_K) hs_K

/-- Helper converting `extDegree E F = 2` into `Module.finrank E F = 2`. -/
private theorem finrank_eq_two_of_extDegree_eq_two {E F : Type*} [Field E] [Field F]
    [Algebra E F] (h : extDegree E F = 2) :
    Module.finrank E F = 2 := by
  have hlt : extDegree E F < ⊤ := by rw [h]; exact ENat.natCast_lt_top 2
  have _ : Module.Finite E F := (isFiniteExtension_iff_moduleFinite E F).mp hlt
  rw [extDegree_eq_finrank E F] at h
  exact Nat.cast_injective (h : ((Module.finrank E F : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞))

/-- General quadratic-extension constructibility lemma: for any subfield `L ⊆ ℝ` with `[L : ℚ] = 2`
and any `x, y ∈ L`, `(x, y)` is constructible. -/
theorem exercise_6_7_a_general (L : IntermediateField ℚ ℝ) (hdeg : extDegree ℚ L = 2)
    {x y : ℝ} (hx : x ∈ L) (hy : y ∈ L) :
    IsConstructible (x, y) := by
  have hbot : ∀ z ∈ (⊥ : IntermediateField ℚ ℝ), z ∈ constructibleSubfield := by
    intro z hz
    rcases IntermediateField.mem_bot.mp hz with ⟨q, rfl⟩
    exact SubfieldClass.ratCast_mem constructibleSubfield q
  have hrank :
      (let _ : Algebra (⊥ : IntermediateField ℚ ℝ) L :=
        (IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ ℝ) ≤ L)).toAlgebra
       Module.finrank (⊥ : IntermediateField ℚ ℝ) L) = 2 := by
    let _ : Algebra (⊥ : IntermediateField ℚ ℝ) L :=
      (IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ ℝ) ≤ L)).toAlgebra
    have _ : IsScalarTower ℚ (⊥ : IntermediateField ℚ ℝ) L :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hrankQ : Module.finrank ℚ L = 2 := finrank_eq_two_of_extDegree_eq_two hdeg
    have _ : Module.Finite ℚ L := Module.finite_of_finrank_pos (by omega)
    have hbot_rank : Module.finrank ℚ (⊥ : IntermediateField ℚ ℝ) = 1 :=
      IntermediateField.finrank_bot
    have hmul := Module.finrank_mul_finrank ℚ (⊥ : IntermediateField ℚ ℝ) L
    rw [hbot_rank, one_mul] at hmul
    exact hmul.trans hrankQ
  have hsub := subset_constructibleSubfield_of_finrank_two (bot_le : (⊥ : IntermediateField ℚ ℝ) ≤ L)
    hbot hrank
  exact (isConstructible_iff_mem_constructibleSubfield x y).mpr ⟨hsub x hx, hsub y hy⟩

/-- **Exercise 6.7(a)** (§6.3, printed p. 58 / PDF p. 66):
*"Suppose that `x` and `y` are real numbers such that `[ℚ(x, y) : ℚ] = 2`. Show that `(x, y)` is
constructible."* -/
theorem exercise_6_7_a {x y : ℝ} (hdeg : extDegree ℚ (ratPointField x y) = 2) :
    IsConstructible (x, y) :=
  exercise_6_7_a_general (ratPointField x y) hdeg
    (IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inl rfl))
    (IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inr rfl))

/-- **Exercise 6.7(a) (Garling subfield form)** (§6.3, printed p. 58 / PDF p. 66):
Version phrased directly on Chapter 4's `garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)`. -/
theorem exercise_6_7_a_subfield {x y : ℝ}
    (hdeg : extDegree ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) = 2) :
    IsConstructible (x, y) := by
  have hsub := ratPointField_toSubfield_eq_garlingFieldGenSubfield x y
  have hmem_iff : ∀ w : ℝ, w ∈ garlingFieldGenSubfield ℚ ({x, y} : Set ℝ) ↔
      w ∈ ratPointField x y := fun w => (SetLike.ext_iff.mp hsub w).symm
  let e : garlingFieldGenSubfield ℚ ({x, y} : Set ℝ) ≃ₐ[ℚ] ratPointField x y :=
    { toFun := fun z => ⟨z.1, (hmem_iff z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (hmem_iff z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun q => Subtype.ext (by simp) }
  have hrank : Module.finrank ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) = 2 :=
    finrank_eq_two_of_extDegree_eq_two hdeg
  have _ : Module.Finite ℚ (garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)) :=
    Module.finite_of_finrank_pos (by omega)
  have _ : Module.Finite ℚ (ratPointField x y) := Module.Finite.equiv e.toLinearEquiv
  have hdeg' : extDegree ℚ (ratPointField x y) = 2 := by
    rw [extDegree_eq_finrank ℚ (ratPointField x y), ← LinearEquiv.finrank_eq e.toLinearEquiv,
      hrank]
    rfl
  exact exercise_6_7_a hdeg'

/-- General quadratic-tower constructibility lemma: for any increasing sequence of subfields
`ℚ = F_0 ⊆ F_1 ⊆ … ⊆ F_r ⊆ ℝ` with `[F_{j+1} : F_j] = 2` (`0 ≤ j < r`), every `x, y ∈ F_r` gives a
constructible point `(x, y)`. -/
theorem exercise_6_7_b_general {r : ℕ} (F : Fin (r + 1) → IntermediateField ℚ ℝ)
    (h0 : F 0 = ⊥)
    (hchain : ∀ j : Fin r, F j.castSucc ≤ F j.succ)
    (hdeg : ∀ j : Fin r,
      let _ : Algebra (F j.castSucc) (F j.succ) :=
        (IntermediateField.inclusion (hchain j)).toAlgebra
      extDegree (F j.castSucc) (F j.succ) = 2)
    {x y : ℝ} (hx : x ∈ F (Fin.last r)) (hy : y ∈ F (Fin.last r)) :
    IsConstructible (x, y) := by
  have hall : ∀ (m : ℕ) (L' : Fin (m + 1) → IntermediateField ℚ ℝ)
      (h0' : L' 0 = ⊥)
      (hch' : ∀ j : Fin m, L' j.castSucc ≤ L' j.succ)
      (hdeg' : ∀ j : Fin m,
        let _ : Algebra (L' j.castSucc) (L' j.succ) :=
          (IntermediateField.inclusion (hch' j)).toAlgebra
        Module.finrank (L' j.castSucc) (L' j.succ) = 2),
      ∀ z ∈ L' (Fin.last m), z ∈ constructibleSubfield := by
    intro m
    induction m with
    | zero =>
      intro L' h0' _ _ z hz
      change z ∈ L' 0 at hz
      rw [h0'] at hz
      rcases IntermediateField.mem_bot.mp hz with ⟨q, rfl⟩
      exact SubfieldClass.ratCast_mem constructibleSubfield q
    | succ m ih =>
      intro L' h0' hch' hdeg' z hz
      have hprev : ∀ w ∈ L' (Fin.castSucc (Fin.last m)), w ∈ constructibleSubfield :=
        ih (fun i => L' i.castSucc) h0'
          (fun j => hch' j.castSucc)
          (fun j => hdeg' j.castSucc)
      have hstep := subset_constructibleSubfield_of_finrank_two
        (hch' (Fin.last m)) hprev (hdeg' (Fin.last m))
      exact hstep z hz
  have hdeg_fin : ∀ j : Fin r,
      (let _ : Algebra (F j.castSucc) (F j.succ) :=
        (IntermediateField.inclusion (hchain j)).toAlgebra
       Module.finrank (F j.castSucc) (F j.succ)) = 2 := by
    intro j
    let _ : Algebra (F j.castSucc) (F j.succ) :=
      (IntermediateField.inclusion (hchain j)).toAlgebra
    exact finrank_eq_two_of_extDegree_eq_two (hdeg j)
  have hsub := hall r F h0 hchain hdeg_fin
  exact (isConstructible_iff_mem_constructibleSubfield x y).mpr ⟨hsub x hx, hsub y hy⟩

/-- **Exercise 6.7(b)** (§6.3, printed p. 58 / PDF p. 66):
*"Suppose that `x` and `y` are real numbers, and that `ℚ = F_0 ⊆ F_1 ⊆ … ⊆ F_r = ℚ(x, y)` is an
increasing sequence of fields such that `[F_{j+1} : F_j] = 2` for `0 ≤ j < r`. Show, by induction
on `r`, that `(x, y)` is constructible."* -/
theorem exercise_6_7_b {x y : ℝ} {r : ℕ} (F : Fin (r + 1) → IntermediateField ℚ ℝ)
    (h0 : F 0 = ⊥) (hr : F (Fin.last r) = ratPointField x y)
    (hchain : ∀ j : Fin r, F j.castSucc ≤ F j.succ)
    (hdeg : ∀ j : Fin r,
      let _ : Algebra (F j.castSucc) (F j.succ) :=
        (IntermediateField.inclusion (hchain j)).toAlgebra
      extDegree (F j.castSucc) (F j.succ) = 2) :
    IsConstructible (x, y) := by
  have hx : x ∈ F (Fin.last r) := by
    rw [hr]; exact IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inl rfl)
  have hy : y ∈ F (Fin.last r) := by
    rw [hr]; exact IntermediateField.subset_adjoin ℚ ({x, y} : Set ℝ) (Or.inr rfl)
  exact exercise_6_7_b_general F h0 hchain hdeg hx hy

/-- **Exercise 6.7(b) (`Subfield ℝ` form)** (§6.3, printed p. 58 / PDF p. 66):
Version phrased directly on a chain `F : Fin (r + 1) → Subfield ℝ` with `F 0 = ⊥` and
`F (Fin.last r) = garlingFieldGenSubfield ℚ ({x, y} : Set ℝ)`. -/
theorem exercise_6_7_b_subfield {x y : ℝ} {r : ℕ} (F : Fin (r + 1) → Subfield ℝ)
    (h0 : F 0 = (⊥ : Subfield ℝ))
    (hr : F (Fin.last r) = garlingFieldGenSubfield ℚ ({x, y} : Set ℝ))
    (hchain : ∀ j : Fin r, F j.castSucc ≤ F j.succ)
    (hdeg : ∀ j : Fin r,
      let _ : Algebra (F j.castSucc) (F j.succ) := (Subfield.inclusion (hchain j)).toAlgebra
      extDegree (F j.castSucc) (F j.succ) = 2) :
    IsConstructible (x, y) := by
  let F_int : Fin (r + 1) → IntermediateField ℚ ℝ :=
    fun i => (F i).toIntermediateField (fun q => SubfieldClass.ratCast_mem (F i) q)
  have h0_int : F_int 0 = ⊥ := by
    apply IntermediateField.toSubfield_injective
    change F 0 = (⊥ : IntermediateField ℚ ℝ).toSubfield
    rw [h0]
    ext z
    constructor
    · intro hz
      exact (bot_le : (⊥ : Subfield ℝ) ≤ (⊥ : IntermediateField ℚ ℝ).toSubfield) hz
    · intro hz
      rcases IntermediateField.mem_bot.mp hz with ⟨q, rfl⟩
      exact SubfieldClass.ratCast_mem (⊥ : Subfield ℝ) q
  have hr_int : F_int (Fin.last r) = ratPointField x y := by
    apply IntermediateField.toSubfield_injective
    change F (Fin.last r) = (ratPointField x y).toSubfield
    rw [hr, ratPointField_toSubfield_eq_garlingFieldGenSubfield]
  have hchain_int : ∀ j : Fin r, F_int j.castSucc ≤ F_int j.succ := fun j => hchain j
  have hdeg_int : ∀ j : Fin r,
      (let _ : Algebra (F_int j.castSucc) (F_int j.succ) :=
        (IntermediateField.inclusion (hchain_int j)).toAlgebra
       extDegree (F_int j.castSucc) (F_int j.succ)) = 2 := fun j => hdeg j
  exact exercise_6_7_b F_int h0_int hr_int hchain_int hdeg_int

/-- **Exercise 6.7 (Combined `(a)` and `(b)`)** (§6.3, printed p. 58 / PDF p. 66). -/
theorem exercise_6_7 :
    (∀ {x y : ℝ}, extDegree ℚ (ratPointField x y) = 2 → IsConstructible (x, y)) ∧
    (∀ {x y : ℝ} {r : ℕ} (F : Fin (r + 1) → IntermediateField ℚ ℝ),
      F 0 = ⊥ → F (Fin.last r) = ratPointField x y →
      ∀ (hchain : ∀ j : Fin r, F j.castSucc ≤ F j.succ),
      (∀ j : Fin r,
        let _ : Algebra (F j.castSucc) (F j.succ) :=
          (IntermediateField.inclusion (hchain j)).toAlgebra
        extDegree (F j.castSucc) (F j.succ) = 2) →
      IsConstructible (x, y)) :=
  ⟨fun hdeg => exercise_6_7_a hdeg,
   fun F h0 hr hch hdeg => exercise_6_7_b F h0 hr hch hdeg⟩

end Garling.Chapter06
