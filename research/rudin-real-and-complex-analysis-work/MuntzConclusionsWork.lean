import MellinFunctionalWork
import MuntzNonDensityWork

noncomputable section
open Set Filter
open scoped Topology

namespace RudinRCA.Chapter15.MuntzSzaszWork

/-- The exact density criterion, combining the two implications of 15.26. -/
theorem muntz_szasz_iff {λ : ℕ → ℝ} (hλ0 : 0 < λ 0) (hλ : StrictMono λ) :
    muntzClosure λ (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) = ⊤ ↔
      ¬ Summable (fun n ↦ 1 / λ n) := by
  constructor
  · intro htop hs
    have hq : 0 < λ 0 / 2 := half_pos hλ0
    have hqλ : ∀ n, λ 0 / 2 ≠ λ n := by
      intro n heq
      have hn := hλ.monotone (Nat.zero_le n)
      linarith
    have hnot := muntz_szasz_power_not_mem hλ0 hλ hs hq hqλ
    apply hnot
    rw [htop]
    trivial
  · exact muntz_szasz_dense hλ0 hλ

/-- Rudin 15.27: a dense Müntz family remains dense after deleting infinitely
many powers. The retained exponents are explicitly a strictly increasing subsequence. -/
theorem muntz_dense_infinite_deletion {λ : ℕ → ℝ} (hλ0 : 0 < λ 0) (hλ : StrictMono λ)
    (hdense : muntzClosure λ
      (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) = ⊤) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (range b)ᶜ.Infinite ∧
      muntzClosure (λ ∘ b)
        (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le (b n)))).le) = ⊤ :=
  muntz_exists_infinite_removal_dense hλ0 hλ ((muntz_szasz_iff hλ0 hλ).mp hdense)

/-- The increasing enumeration of all natural indices except `j`. -/
def skipExponent (j n : ℕ) : ℕ := if n < j then n else n + 1

theorem strictMono_skipExponent (j : ℕ) : StrictMono (skipExponent j) := by
  intro n m hnm
  dsimp [skipExponent]
  split_ifs <;> omega

theorem skipExponent_ne (j n : ℕ) : skipExponent j n ≠ j := by
  dsimp [skipExponent]
  split_ifs <;> omega

theorem range_skipExponent (j : ℕ) : range (skipExponent j) = {j}ᶜ := by
  ext n
  constructor
  · rintro ⟨m, rfl⟩
    exact skipExponent_ne j m
  · intro hn
    change n ≠ j at hn
    by_cases hnj : n < j
    · exact ⟨n, by simp [skipExponent, hnj]⟩
    · refine ⟨n - 1, ?_⟩
      have hnj' : ¬ n - 1 < j := by omega
      simp only [skipExponent, if_neg hnj']
      omega

/-- With a convergent reciprocal sum, removal of any positive power strictly
shrinks the closed span, while retaining the constant. -/
theorem muntz_power_removal_strict_of_summable {λ : ℕ → ℝ}
    (hλ0 : 0 < λ 0) (hλ : StrictMono λ) (hs : Summable (fun n ↦ 1 / λ n)) (j : ℕ) :
    muntzClosure (λ ∘ skipExponent j)
      (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le (skipExponent j n)))).le) <
      muntzClosure λ (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) := by
  let hpos : ∀ n, 0 < λ n := fun n ↦ hλ0.trans_le (hλ.monotone (Nat.zero_le n))
  have hb := strictMono_skipExponent j
  have hs' : Summable (fun n ↦ 1 / λ (skipExponent j n)) := hs.comp_injective hb.injective
  have hnot := muntz_szasz_power_not_mem (hpos (skipExponent j 0)) (hλ.comp hb) hs' (hpos j)
    (fun n heq ↦ skipExponent_ne j n (hλ.injective heq).symm)
  apply closed_span_strictly_decreases_of_removed_vector
    (v := intervalRealPower (λ j) (hpos j).le)
  · intro f hf
    rcases hf with rfl | ⟨n, rfl⟩
    · exact mem_insert 1 _
    · exact mem_insert_of_mem _ ⟨skipExponent j n, rfl⟩
  · exact mem_insert_of_mem _ ⟨j, rfl⟩
  · exact hnot

/-- The non-dense alternative in Rudin 15.27. This statement covers every
positive power; `muntz_constant_removal_strict` covers the constant member. -/
theorem muntz_nondense_power_removal_strict {λ : ℕ → ℝ}
    (hλ0 : 0 < λ 0) (hλ : StrictMono λ)
    (hnotdense : muntzClosure λ
      (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) ≠ ⊤) (j : ℕ) :
    muntzClosure (λ ∘ skipExponent j)
      (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le (skipExponent j n)))).le) <
      muntzClosure λ (fun n ↦ (hλ0.trans_le (hλ.monotone (Nat.zero_le n))).le) := by
  have hs : Summable (fun n ↦ 1 / λ n) := by
    by_contra h
    exact hnotdense (muntz_szasz_dense hλ0 hλ h)
  exact muntz_power_removal_strict_of_summable hλ0 hλ hs j

#print axioms muntz_szasz_iff
#print axioms muntz_dense_infinite_deletion
#print axioms strictMono_skipExponent
#print axioms skipExponent_ne
#print axioms range_skipExponent
#print axioms muntz_power_removal_strict_of_summable
#print axioms muntz_nondense_power_removal_strict

end RudinRCA.Chapter15.MuntzSzaszWork
