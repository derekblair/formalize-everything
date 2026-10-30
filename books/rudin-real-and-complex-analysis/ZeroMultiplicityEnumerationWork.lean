import ZeroSetNormalizationWork
import Mathlib.Basic.Denumerable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.SetTheory.Cardinal.Finite

/-! Enumeration of a discrete set with arbitrary positive finite multiplicities. Draft. -/

noncomputable section

open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

def ZeroCopy (A : Set ℂ) (m : ℂ → ℕ) := Σ a : A, Fin (m a)

def zeroCopyValue {A : Set ℂ} {m : ℂ → ℕ} (i : ZeroCopy A m) : ℂ := i.1

def zeroCopyFiberEquiv {A : Set ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∈ A) :
    {i : ZeroCopy A m // zeroCopyValue i = z} ≃ Fin (m z) where
  toFun i := ⟨i.1.2, by simpa only [← i.2] using i.1.2.isLt⟩
  invFun j := ⟨⟨⟨z, hz⟩, j⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨⟨a, ha⟩, j⟩, h⟩
    change a = z at h
    subst a
    rfl
  right_inv := by intro j; rfl

theorem finite_zeroCopy_fiber (A : Set ℂ) (m : ℂ → ℕ) (z : ℂ) :
    Finite {i : ZeroCopy A m // zeroCopyValue i = z} := by
  by_cases hz : z ∈ A
  · exact Finite.of_equiv (Fin (m z)) (zeroCopyFiberEquiv hz).symm
  · haveI : IsEmpty {i : ZeroCopy A m // zeroCopyValue i = z} :=
      ⟨fun i ↦ hz (i.2 ▸ i.1.1.property)⟩
    infer_instance

theorem zeroCopy_range {A : Set ℂ} {m : ℂ → ℕ} (hm : ∀ z ∈ A, 0 < m z) :
    range (@zeroCopyValue A m) = A := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact i.1.property
  · intro hz
    exact ⟨⟨⟨z, hz⟩, ⟨0, hm z hz⟩⟩, rfl⟩

/-- Counting the finite multiplicity fiber gives an actual convergent natural
sum, without an implicit summability assumption. -/
theorem zeroCopy_indicator_hasSum {A : Set ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : z ∈ A) :
    HasSum (fun i : ZeroCopy A m ↦ if z = zeroCopyValue i then (1 : ℕ) else 0) (m z) := by
  classical
  let S : Set (ZeroCopy A m) := {i | zeroCopyValue i = z}
  haveI : Finite S := finite_zeroCopy_fiber A m z
  letI : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = m z := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (zeroCopyFiberEquiv (m := m) hz)
  have hs : Function.support
      (fun i : ZeroCopy A m ↦ if z = zeroCopyValue i then (1 : ℕ) else 0) ⊆ S := by
    intro i hi
    by_contra h
    exact hi (if_neg (Ne.symm h))
  apply (hasSum_subtype_iff_of_support_subset hs).1
  have hone : (fun i : S ↦ if z = zeroCopyValue i.1 then (1 : ℕ) else 0) = fun _ ↦ 1 := by
    funext i
    simp only [i.2, if_pos rfl]
  simpa only [Function.comp_def, hone, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, nsmul_eq_mul, mul_one, hcard] using (hasSum_fintype (fun _ : S ↦ (1 : ℕ)))

/-- Every compact subset of the domain contains finitely many multiplicity
copies, even when the multiplicities are not uniformly bounded. -/
theorem finite_zeroCopy_preimage_compact {A Ω K : Set ℂ} {m : ℂ → ℕ}
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    {i : ZeroCopy A m | zeroCopyValue i ∈ K}.Finite := by
  have hAK := finite_inter_compact_of_no_accumulation hno hK hKΩ
  have hpre : ((@zeroCopyValue A m) ⁻¹' (A ∩ K)).Finite :=
    hAK.preimage' (fun z _ ↦ finite_zeroCopy_fiber A m z)
  apply hpre.subset
  intro i hi
  exact ⟨i.1.property, hi⟩

/-- Reindex all copies by the naturals in the infinite case. The enumeration
has exact prescribed multiplicities and escapes every compact domain subset. -/
theorem exists_zero_enumeration {A Ω : Set ℂ} {m : ℂ → ℕ}
    (hAcount : A.Countable) (hm : ∀ z ∈ A, 0 < m z)
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) [Infinite (ZeroCopy A m)] :
    ∃ a : ℕ → ℂ, range a = A ∧
      (∀ z ∈ A, HasSum (fun n ↦ if z = a n then (1 : ℕ) else 0) (m z)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ᶠ n in atTop, a n ∉ K) := by
  classical
  haveI : Countable A := hAcount.to_subtype
  haveI : Countable (ZeroCopy A m) := by unfold ZeroCopy; infer_instance
  let e : ℕ ≃ ZeroCopy A m := Classical.choice inferInstance
  let a : ℕ → ℂ := fun n ↦ zeroCopyValue (e n)
  refine ⟨a, ?_, ?_, ?_⟩
  · change range ((@zeroCopyValue A m) ∘ e) = A
    rw [e.surjective.range_comp, zeroCopy_range hm]
  · intro z hz
    exact e.hasSum_iff.2 (zeroCopy_indicator_hasSum hz)
  · intro K hK hKΩ
    have hc := finite_zeroCopy_preimage_compact (m := m) hno hK hKΩ
    have hn : {n : ℕ | a n ∈ K}.Finite := hc.preimage e.injective.injOn
    simpa only [Nat.cofinite_eq_atTop] using hn.eventually_cofinite_notMem

#print axioms finite_zeroCopy_fiber
#print axioms zeroCopy_indicator_hasSum
#print axioms finite_zeroCopy_preimage_compact
#print axioms exists_zero_enumeration

end RudinRCA.Chapter15
