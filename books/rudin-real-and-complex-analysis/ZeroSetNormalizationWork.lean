import SphereWork
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Normed.Group.Bounded

/-! Topological normalization of the full sphere data in Rudin 15.11. Draft. -/

noncomputable section

open Filter Set Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def NoAccumulationIn (A Ω : Set ComplexSphere) : Prop :=
  ∀ p ∈ Ω, ¬ AccPt p (𝓟 A)

/-- A nonempty open domain with a prescribed discrete zero set always contains
a point outside that set. This also works when the starting point is infinity. -/
theorem exists_domain_point_outside_zeros {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hΩne : Ω.Nonempty) (hno : NoAccumulationIn A Ω) :
    ∃ pole ∈ Ω, pole ∉ A := by
  obtain ⟨p, hp⟩ := hΩne
  have hnot : ∀ᶠ q in 𝓝[≠] p, q ∉ A := by
    simpa only [accPt_iff_frequently_nhdsNE, not_frequently] using hno p hp
  have hmem : ∀ᶠ q in 𝓝[≠] p, q ∈ Ω :=
    (hΩ.mem_nhds hp).filter_mono nhdsWithin_le_nhds
  exact (hmem.and hnot).exists

theorem normalized_complement_isCompact {Ω : Set ComplexSphere}
    (hΩ : IsOpen Ω) {pole : ComplexSphere} (hpole : pole ∈ Ω) :
    IsCompact (spherePlaneParam pole ⁻¹' Ω)ᶜ := by
  let U : Set ComplexSphere := (spherePoleChart pole).symm ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (spherePoleChart pole).symm.continuous
  have hinfty : (∞ : ComplexSphere) ∈ U := by simpa [U] using hpole
  exact ((OnePoint.isOpen_iff_of_mem' hinfty).1 hU).1

theorem normalized_domain_eq {Ω : Set ComplexSphere} {pole : ComplexSphere}
    (hpole : pole ∈ Ω) :
    (((↑) : ℂ → ComplexSphere) '' (spherePlaneParam pole ⁻¹' Ω)ᶜ)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := by
  ext p
  induction p using OnePoint.rec with
  | infty => simp [hpole]
  | coe z =>
    simp only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right,
      mem_preimage, not_not, spherePlaneParam]

theorem normalized_complement_nonempty {Ω : Set ComplexSphere}
    (hproper : Ω ≠ univ) {pole : ComplexSphere} (hpole : pole ∈ Ω) :
    ((spherePlaneParam pole ⁻¹' Ω)ᶜ).Nonempty := by
  obtain ⟨p, hp⟩ := ne_univ_iff_exists_notMem.mp hproper
  have hpp : p ≠ pole := fun h ↦ hp (h.symm ▸ hpole)
  have hr : p ∈ range (spherePlaneParam pole) := by
    rw [range_spherePlaneParam]
    exact hpp
  obtain ⟨z, hz⟩ := hr
  exact ⟨z, by simpa [mem_preimage, hz] using hp⟩

theorem normalized_zeros_no_accumulation {Ω A : Set ComplexSphere}
    (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    ∀ z ∈ spherePlaneParam pole ⁻¹' Ω,
      ¬ AccPt z (𝓟 (spherePlaneParam pole ⁻¹' A)) := by
  intro z hz hacc
  apply hno (spherePlaneParam pole z) hz
  apply (isOpenEmbedding_spherePlaneParam pole).accPt_comap_iff.mp
  simpa only [comap_principal] using hacc

theorem normalized_zeros_isDiscrete {Ω A : Set ComplexSphere}
    (hA : A ⊆ Ω) (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    IsDiscrete (spherePlaneParam pole ⁻¹' A) := by
  apply isDiscrete_iff_nhdsNE.2
  intro z hz
  have h := normalized_zeros_no_accumulation hno pole z (hA hz)
  simpa only [AccPt, not_neBot] using h

theorem normalized_zeros_countable {Ω A : Set ComplexSphere}
    (hA : A ⊆ Ω) (hno : NoAccumulationIn A Ω) (pole : ComplexSphere) :
    (spherePlaneParam pole ⁻¹' A).Countable :=
  (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (normalized_zeros_isDiscrete hA hno pole)

/-- Moving a domain point outside A to infinity makes the finite zero set
bounded, which is needed by the printed boundary-pole construction. -/
theorem normalized_zeros_isBounded {Ω A : Set ComplexSphere}
    (hno : NoAccumulationIn A Ω) {pole : ComplexSphere}
    (hpole : pole ∈ Ω) (hpoleA : pole ∉ A) :
    IsBounded (spherePlaneParam pole ⁻¹' A) := by
  have hpcl : pole ∉ closure A := by
    intro h
    have hcp := mem_closure_iff_clusterPt.mp h
    exact (clusterPt_principal.mp hcp).elim hpoleA (hno pole hpole)
  have hcompact : IsCompact (spherePlaneParam pole ⁻¹' (closure A)ᶜ)ᶜ :=
    normalized_complement_isCompact isClosed_closure.isOpen_compl hpcl
  apply hcompact.isBounded.subset
  intro z hz
  exact fun h ↦ h (subset_closure hz)

/-- No accumulation points in the domain implies finite intersection with
every compact subset, in any topological space. -/
theorem finite_inter_compact_of_no_accumulation {X : Type*} [TopologicalSpace X]
    {A Ω K : Set X} (hno : ∀ x ∈ Ω, ¬ AccPt x (𝓟 A))
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (A ∩ K).Finite := by
  by_contra hinfinite
  obtain ⟨x, hxK, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinfinite hK inter_subset_right
  exact hno x (hKΩ hxK) (hx.mono (principal_mono.2 inter_subset_left))

#print axioms exists_domain_point_outside_zeros
#print axioms normalized_complement_isCompact
#print axioms normalized_domain_eq
#print axioms normalized_complement_nonempty
#print axioms normalized_zeros_countable
#print axioms normalized_zeros_isBounded
#print axioms finite_inter_compact_of_no_accumulation

end RudinRCA.Chapter15
