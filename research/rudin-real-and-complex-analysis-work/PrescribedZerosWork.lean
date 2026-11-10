import BoundaryProductWork
import ZeroMultiplicityEnumerationWork

/-!
Full assembly target for Rudin 15.11, including proper open sphere domains,
arbitrary positive multiplicities, and finite and empty prescribed zero sets.
This file and its scratch prerequisites are drafts awaiting serialized checks.
-/

noncomputable section

open Filter Set Finset Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

/-- The normalized existence theorem. The omitted set is a nonempty compact
plane set; prescribed zeros are bounded and have no domain accumulation. -/
theorem normalized_prescribed_zeros {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S)) (m : ℂ → ℕ) (hm : ∀ z ∈ S, 0 < m z) :
    ∃ g : ComplexSphere → ℂ,
      SphereHolomorphicOn g (((↑) : ℂ → ComplexSphere) '' C)ᶜ ∧ g ∞ = 1 ∧
      (∀ z ∈ Cᶜ, g (↑z) = 0 ↔ z ∈ S) ∧
      (∀ z ∈ S, sphereAnalyticOrderAt g (↑z) = (m z : ℕ∞)) := by
  classical
  cases finite_or_infinite (ZeroCopy S m) with
  | inl hfinite =>
    letI := hfinite
    letI : Fintype (ZeroCopy S m) := Fintype.ofFinite _
    obtain ⟨b, hb⟩ := hCne
    let F : ZeroCopy S m → ComplexSphere → ℂ :=
      fun i ↦ boundarySphereFactor 0 (zeroCopyValue i) b
    let g : ComplexSphere → ℂ := fun p ↦ ∏ i : ZeroCopy S m, F i p
    have hgb : SphereHolomorphicOn g (((↑) : ℂ → ComplexSphere) '' C)ᶜ :=
      sphereHolomorphicOn_finset_product univ F
        (fun i _ ↦ boundarySphereFactor_holomorphic 0 (zeroCopyValue i) b hb)
    refine ⟨g, hgb, by simp [g, F], ?_, ?_⟩
    · intro z hz
      have hzb : z ≠ b := fun h ↦ hz (h.symm ▸ hb)
      change (∏ i : ZeroCopy S m, boundaryFactor 0 (zeroCopyValue i) b z) = 0 ↔ z ∈ S
      rw [Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨i, _, hi⟩
        have heq := (boundaryFactor_eq_zero_iff 0 (zeroCopyValue i) b hzb).1 hi
        exact heq.symm ▸ i.1.property
      · intro hzS
        obtain ⟨i, hi⟩ := (zeroCopy_range (m := m) hm).symm ▸ hzS
        exact ⟨i, mem_univ _, (boundaryFactor_eq_zero_iff 0 (zeroCopyValue i) b hzb).2 hi.symm⟩
    · intro z hz
      have hzb : z ≠ b := fun h ↦ hS hz (h.symm ▸ hb)
      have hab (i : ZeroCopy S m) : zeroCopyValue i ≠ b :=
        fun h ↦ hS i.1.property (h.symm ▸ hb)
      have ho (i : ZeroCopy S m) :
          analyticOrderAt (boundaryFactor 0 (zeroCopyValue i) b) z =
            if z = zeroCopyValue i then 1 else 0 :=
        analyticOrderAt_boundaryFactor 0 (hab i) hzb
      change analyticOrderAt (fun w ↦ ∏ i : ZeroCopy S m,
        boundaryFactor 0 (zeroCopyValue i) b w) z = (m z : ℕ∞)
      rw [analyticOrderAt_finset_product univ
        (F := fun i ↦ boundaryFactor 0 (zeroCopyValue i) b) (z := z)
        (fun i _ ↦ analyticAt_boundaryFactor 0 (zeroCopyValue i) b hzb)]
      simp only [ho]
      have hsum : (∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ) else 0) = m z :=
        (hasSum_fintype _).unique (zeroCopy_indicator_hasSum hz)
      calc
        (∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ∞) else 0) =
            ((∑ i : ZeroCopy S m, if z = zeroCopyValue i then (1 : ℕ) else 0) : ℕ∞) := by
          rw [Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> rfl
        _ = (m z : ℕ∞) := congrArg (fun n : ℕ ↦ (n : ℕ∞)) hsum
  | inr hinfinite =>
    letI := hinfinite
    obtain ⟨a, haS, hcount, hescape⟩ := exists_zero_enumeration hScount hm hno
    have haS' (n : ℕ) : a n ∈ S := haS ▸ mem_range_self n
    have ha (n : ℕ) : a n ∉ C := hS (haS' n)
    choose b hb hnearest using (fun n ↦ hC.exists_infDist_eq_dist hCne (a n))
    obtain ⟨R, hR⟩ := hSbound.exists_norm_le
    have hd := infDist_tendsto_zero_of_bounded_escape a C R
      (fun n ↦ hR (a n) (haS' n)) hescape
    have hsmall := nearest_boundary_difference_tendsto_zero a b C hnearest hd
    have hprod := boundary_product_on_complement a b hC.isClosed hCne ha hb hsmall
    refine ⟨boundarySphereProduct a b,
      normalized_boundarySphereProduct_holomorphic a b hC hCne ha hb hsmall, rfl, ?_, ?_⟩
    · intro z hz
      rw [boundarySphereProduct_coe, (hprod.2.2 z hz).1]
      have hr : (∃ n, z = a n) ↔ z ∈ range a := by
        simp only [mem_range, eq_comm]
      rw [hr, haS]
    · intro z hz
      obtain ⟨_, hfinite, horder⟩ := hprod.2.2 z (hS hz)
      rw [(hcount z hz).tsum_eq] at horder
      change analyticOrderAt (fun w ↦ ∏' n, boundaryFactor n (a n) (b n) w) z = (m z : ℕ∞)
      calc
        _ = (analyticOrderNatAt (fun w ↦ ∏' n, boundaryFactor n (a n) (b n) w) z : ℕ∞) :=
          (ENat.natCast_toNat hfinite).symm
        _ = (m z : ℕ∞) := congrArg (fun n : ℕ ↦ (n : ℕ∞)) horder

/-- Rudin 15.11 on its full printed domain: every positive divisor with no
accumulation in a proper open subset of the Riemann sphere is the zero divisor
of a holomorphic function. No plane-only restriction or construction premise
appears in this statement. -/
theorem prescribed_zeros_on_sphere {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hproper : Ω ≠ univ) (hA : A ⊆ Ω)
    (hno : NoAccumulationIn A Ω) (m : ComplexSphere → ℕ) (hm : ∀ p ∈ A, 0 < m p) :
    ∃ f : ComplexSphere → ℂ, SphereHolomorphicOn f Ω ∧
      (∀ p ∈ Ω, f p = 0 ↔ p ∈ A) ∧
      (∀ p ∈ A, sphereAnalyticOrderAt f p = (m p : ℕ∞)) := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩempty | hΩne
  · refine ⟨fun _ ↦ 1, ?_, ?_, ?_⟩
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hp
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hp
    · intro p hp; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hA hp
  obtain ⟨pole, hpole, hpoleA⟩ := exists_domain_point_outside_zeros hΩ hΩne hno
  let C : Set ℂ := (spherePlaneParam pole ⁻¹' Ω)ᶜ
  let S : Set ℂ := spherePlaneParam pole ⁻¹' A
  let m' : ℂ → ℕ := fun z ↦ m (spherePlaneParam pole z)
  have hC : IsCompact C := normalized_complement_isCompact hΩ hpole
  have hCne : C.Nonempty := normalized_complement_nonempty hproper hpole
  have hS : S ⊆ Cᶜ := by
    intro z hz
    exact not_not.mpr (hA hz)
  have hScount : S.Countable := normalized_zeros_countable hA hno pole
  have hSbound : IsBounded S := normalized_zeros_isBounded hno hpole hpoleA
  have hno' : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S) := by
    intro z hz
    exact normalized_zeros_no_accumulation hno pole z (not_not.mp hz)
  have hm' : ∀ z ∈ S, 0 < m' z := fun z hz ↦ hm (spherePlaneParam pole z) hz
  obtain ⟨g, hg, hginfty, hgzero, hgorder⟩ :=
    normalized_prescribed_zeros hC hCne hS hScount hSbound hno' m' hm'
  let f : ComplexSphere → ℂ := g ∘ spherePoleChart pole
  have hdom : (((↑) : ℂ → ComplexSphere) '' C)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := normalized_domain_eq hpole
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p hp
    apply (sphereAnalyticAt_comp_poleChart_iff g pole p).2
    apply hg
    rw [hdom]
    simpa using hp
  · intro p hp
    by_cases hpp : p = pole
    · subst p
      simp [f, hginfty, hpoleA]
    · have hr : p ∈ range (spherePlaneParam pole) := by
        rw [range_spherePlaneParam]
        exact hpp
      obtain ⟨z, rfl⟩ := hr
      have hz : z ∈ Cᶜ := not_not.mpr hp
      simpa only [f, Function.comp_def, spherePlaneParam, Homeomorph.apply_symm_apply]
        using hgzero z hz
  · intro p hp
    have hpp : p ≠ pole := fun h ↦ hpoleA (h ▸ hp)
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact hpp
    obtain ⟨z, rfl⟩ := hr
    change sphereAnalyticOrderAt (g ∘ spherePoleChart pole) (spherePlaneParam pole z) = _
    rw [sphereAnalyticOrderAt_comp_poleChart]
    simpa only [spherePlaneParam, Homeomorph.apply_symm_apply] using hgorder z hp

/-- The plane-domain corollary used by 15.12 and later nodes. It is obtained
from the full sphere theorem, so it does not replace the printed sphere scope. -/
theorem prescribed_zeros_on_plane {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ z ∈ Ω, ¬ AccPt z (𝓟 A)) (m : ℂ → ℕ) (hm : ∀ z ∈ A, 0 < m z) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      (∀ z ∈ Ω, f z = 0 ↔ z ∈ A) ∧
      (∀ z ∈ A, analyticOrderAt f z = (m z : ℕ∞)) := by
  let Ωs : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' Ω
  let As : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' A
  let ms : ComplexSphere → ℕ := fun p ↦ p.elim 0 m
  have hΩs : IsOpen Ωs := OnePoint.isOpen_image_coe.2 hΩ
  have hproper : Ωs ≠ univ := by
    intro h
    have hin : (∞ : ComplexSphere) ∈ Ωs := by rw [h]; trivial
    exact OnePoint.infty_notMem_image_coe hin
  have hAs : As ⊆ Ωs := image_mono hA
  have hnos : NoAccumulationIn As Ωs := by
    rintro p ⟨z, hz, rfl⟩ hacc
    have hacc' := OnePoint.isOpenEmbedding_coe.accPt_comap_iff.mpr hacc
    apply hno z hz
    simpa only [comap_principal, As, preimage_image_eq _ OnePoint.coe_injective] using hacc'
  have hms : ∀ p ∈ As, 0 < ms p := by
    rintro p ⟨z, hz, rfl⟩
    exact hm z hz
  obtain ⟨f, hf, hzero, horder⟩ := prescribed_zeros_on_sphere hΩs hproper hAs hnos ms hms
  refine ⟨fun z ↦ f (↑z), ?_, ?_, ?_⟩
  · intro z hz
    have ha := hf (↑z) ⟨z, hz, rfl⟩
    change AnalyticAt ℂ (fun w : ℂ ↦ f (↑w)) z at ha
    exact ha.differentiableAt.differentiableWithinAt
  · intro z hz
    simpa only [As, mem_image, OnePoint.coe_eq_coe, exists_eq_right] using
      hzero (↑z) ⟨z, hz, rfl⟩
  · intro z hz
    exact horder (↑z) ⟨z, hz, rfl⟩

#print axioms normalized_prescribed_zeros
#print axioms prescribed_zeros_on_sphere
#print axioms prescribed_zeros_on_plane

end RudinRCA.Chapter15
