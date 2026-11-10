import NormalizedInterpolationWork

/-!
Rudin 15.13: unrestricted finite jets on a discrete subset of an open plane
domain. The proof normalizes the domain, invokes the explicitly constructed
normalized interpolation theorem, and transports analytic order through the
sphere chart. No interpolation or Mittag-Leffler existence premise occurs in
the final statements. All source dependencies remain drafts awaiting checks.
-/

noncomputable section
open Filter Set Finset
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

/-- A chart-invariant interpolation statement. It is useful for transport; the
printed plane-domain derivative formulation is given below. -/
theorem sphere_interpolate_analytic_germs {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hproper : Ω ≠ univ) (hA : A ⊆ Ω)
    (hno : NoAccumulationIn A Ω)
    (m : ComplexSphere → ℕ) (G : ComplexSphere → ComplexSphere → ℂ)
    (hG : ∀ a ∈ A, SphereAnalyticAt (G a) a) :
    ∃ H : ComplexSphere → ℂ, SphereHolomorphicOn H Ω ∧
      ∀ a ∈ A, (m a : ℕ∞) ≤ sphereAnalyticOrderAt (fun z ↦ H z - G a z) a := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩempty | hΩne
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro a ha; exfalso; simpa only [hΩempty, mem_empty_iff_false] using ha
    · intro a ha; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hA ha
  obtain ⟨pole, hpole, hpoleA⟩ := exists_domain_point_outside_zeros hΩ hΩne hno
  let C : Set ℂ := (spherePlaneParam pole ⁻¹' Ω)ᶜ
  let S : Set ℂ := spherePlaneParam pole ⁻¹' A
  let m' : ℂ → ℕ := fun z ↦ m (spherePlaneParam pole z)
  let G' : ℂ → ℂ → ℂ := fun a z ↦ G (spherePlaneParam pole a) (spherePlaneParam pole z)
  have hC : IsCompact C := normalized_complement_isCompact hΩ hpole
  have hCne : C.Nonempty := normalized_complement_nonempty hproper hpole
  have hS : S ⊆ Cᶜ := fun z hz ↦ not_not.mpr (hA hz)
  have hScount : S.Countable := normalized_zeros_countable hA hno pole
  have hSbound := normalized_zeros_isBounded hno hpole hpoleA
  have hno' : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S) :=
    fun z hz ↦ normalized_zeros_no_accumulation hno pole z (not_not.mp hz)
  have hG' : ∀ a ∈ S, AnalyticAt ℂ (G' a) a := by
    intro a ha
    exact (sphereAnalyticAt_iff_planeParam (G (spherePlaneParam pole a)) pole a).1
      (hG (spherePlaneParam pole a) ha)
  obtain ⟨H', hH', hjet⟩ :=
    normalized_interpolate_analytic_germs hC hCne hS hScount hSbound hno' m' G' hG'
  let H : ComplexSphere → ℂ := H' ∘ spherePoleChart pole
  have hdom : (((↑) : ℂ → ComplexSphere) '' C)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := normalized_domain_eq hpole
  refine ⟨H, ?_, ?_⟩
  · intro p hp
    apply (sphereAnalyticAt_comp_poleChart_iff H' pole p).2
    apply hH'
    rw [hdom]
    simpa using hp
  · intro p hp
    have hpp : p ≠ pole := fun h ↦ hpoleA (h ▸ hp)
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact hpp
    obtain ⟨z, rfl⟩ := hr
    rw [sphereAnalyticOrderAt_planeParam]
    simpa only [H, G', m', Function.comp_def, spherePlaneParam,
      Homeomorph.apply_symm_apply] using hjet z hp

/-- Exact interpolation of analytic germs to arbitrary finite order on an
arbitrary open plane domain, including disconnected domains and empty data. -/
theorem interpolate_analytic_germs {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ a ∈ Ω, ¬ AccPt a (𝓟 A))
    (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ) (hG : ∀ a ∈ A, AnalyticAt ℂ (G a) a) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧
      ∀ a ∈ A, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ F z - G a z) a := by
  let Ωs : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' Ω
  let As : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' A
  let ms : ComplexSphere → ℕ := fun p ↦ p.elim 0 m
  let Gs : ComplexSphere → ComplexSphere → ℂ := fun p ↦
    p.elim (fun _ ↦ 0) (fun a q ↦ q.elim 0 (G a))
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
  have hGs : ∀ a ∈ As, SphereAnalyticAt (Gs a) a := by
    rintro p ⟨a, ha, rfl⟩
    exact hG a ha
  obtain ⟨F, hF, hjet⟩ := sphere_interpolate_analytic_germs hΩs hproper hAs hnos ms Gs hGs
  exact ⟨fun z ↦ F (↑z), fun z hz ↦ hF (↑z) ⟨z, hz, rfl⟩,
    fun a ha ↦ hjet (↑a) ⟨a, ha, rfl⟩⟩

def prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ) (a z : ℂ) : ℂ :=
  ∑ i ∈ range (m + 1), (z - a) ^ i * w i

theorem analyticAt_prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ) (a z : ℂ) :
    AnalyticAt ℂ (prescribedJetPolynomial m w a) z := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((analyticAt_id.sub analyticAt_const).pow i).mul analyticAt_const

theorem iteratedDeriv_prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ)
    (a : ℂ) {k : ℕ} (hk : k ≤ m) :
    iteratedDeriv k (prescribedJetPolynomial m w a) a = (k.factorial : ℂ) * w k := by
  change iteratedDeriv k
    (fun z ↦ (fun v : ℂ ↦ ∑ i ∈ range (m + 1), v ^ i * w i) (z - a)) a = _
  rw [iteratedDeriv_comp_sub_const, sub_self]
  rw [iteratedDeriv_fun_sum (fun i _ ↦ by fun_prop)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero, ite_mul, zero_mul]
  exact sum_ite_eq_of_mem _ _ _ (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- Rudin 15.13 in the printed derivative convention: the data w_(n,a) are
Taylor coefficients, so the prescribed nth derivative is n! * w_(n,a), for all
0 ≤ n ≤ m(a). No boundedness or growth restriction is imposed on those data. -/
theorem interpolate_prescribed_derivative_jets {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ a ∈ Ω, ¬ AccPt a (𝓟 A))
    (m : ℂ → ℕ) (w : ℂ → ℕ → ℂ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      ∀ a ∈ A, ∀ n ≤ m a, iteratedDeriv n F a = (n.factorial : ℂ) * w a n := by
  let G : ℂ → ℂ → ℂ := fun a ↦ prescribedJetPolynomial (m a) (w a) a
  have hG : ∀ a ∈ A, AnalyticAt ℂ (G a) a :=
    fun a _ ↦ analyticAt_prescribedJetPolynomial (m a) (w a) a a
  obtain ⟨F, hF, hjet⟩ := interpolate_analytic_germs hΩ hA hno (fun a ↦ m a + 1) G hG
  refine ⟨F, hF.differentiableOn, ?_⟩
  intro a ha n hn
  have hFa : AnalyticAt ℂ F a := hF a (hA ha)
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFa.sub (hG a ha))).1
    (hjet a ha) n (Nat.lt_succ_of_le hn)
  rw [iteratedDeriv_fun_sub hFa.contDiffAt (hG a ha).contDiffAt] at hz
  exact (sub_eq_zero.mp hz).trans (iteratedDeriv_prescribedJetPolynomial (m a) (w a) a hn)

#print axioms sphere_interpolate_analytic_germs
#print axioms interpolate_analytic_germs
#print axioms analyticAt_prescribedJetPolynomial
#print axioms iteratedDeriv_prescribedJetPolynomial
#print axioms interpolate_prescribed_derivative_jets

end RudinRCA.Chapter15
