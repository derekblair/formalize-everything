import RudinRCA.Chapter15

/-!
Final 15.12 assembly against the planned Chapter15 interface. This file requires
the actual 15.11 existence theorem and the pole-data/quotient prerequisites to
have been integrated; no denominator-existence hypothesis is assumed here.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- Theorem 15.12 in Mathlib's meromorphic-class interpretation. A scalar-valued
`MeromorphicOn` function may have arbitrary isolated point values, so the identity
is initially stated as equality outside a codiscrete set. The denominator has
exactly the actual poles as its zeros and finite order everywhere. -/
theorem meromorphic_function_quotient {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicOn f Ω) :
    ∃ g h : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ AnalyticOnNhd ℂ h Ω ∧
      (∀ z ∈ Ω, h z = 0 ↔ z ∈ meromorphicPoleSet f Ω) ∧
      (∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤) ∧
      f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z) := by
  obtain ⟨h, hhol, hzeros, horders⟩ := prescribed_zeros_on_plane hΩ
    (meromorphicPoleSet_subset f Ω) (meromorphicPoleSet_no_accPt f Ω)
    (meromorphicPoleMultiplicity f Ω) (fun z hz ↦ meromorphicPoleMultiplicity_pos hz)
  have hhan : AnalyticOnNhd ℂ h Ω := hhol.analyticOnNhd hΩ
  have hall := denominator_order_of_pole_data hhan hzeros horders
  obtain ⟨hfinite, hcancel⟩ := nonnegative_order_of_pole_denominator hf hhan hall
  obtain ⟨g, hga, heq⟩ := meromorphic_quotient_of_canceling_denominator hf hhan hfinite hcancel
  exact ⟨g, h, hga, hhan, hzeros, hfinite, heq⟩

/-- At an analytic nonpole, equality of meromorphic classes is actual equality.
This supplies the printed identity on Ω minus its pole set. -/
theorem quotient_eq_at_of_codiscrete {Ω : Set ℂ} {f g h : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : AnalyticOnNhd ℂ g Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (heq : f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z))
    {z : ℂ} (hz : z ∈ Ω) (hfz : AnalyticAt ℂ f z) (hhz : h z ≠ 0) :
    f z = g z / h z := by
  have hnear : f =ᶠ[𝓝[≠] z] (fun w ↦ g w / h w) := by
    have hlocal := eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE.mp heq z hz
    filter_upwards [hlocal, (hΩ.mem_nhds hz).filter_mono nhdsWithin_le_nhds] with w hw hwΩ
    exact hw hwΩ
  exact (hfz.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (((hg z hz).div (hh z hz) hhz).continuousAt)).mp hnear |>.eq_of_nhds

/-- The pointwise form of 15.12 for the normal-form representative of a
meromorphic function: f=g/h at every point outside its actual poles. This
convention removes Mathlib's arbitrary isolated values, not any mathematical
domain components. -/
theorem meromorphic_function_quotient_off_poles {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicNFOn f Ω) :
    ∃ g h : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ AnalyticOnNhd ℂ h Ω ∧
      (∀ z ∈ Ω, h z = 0 ↔ z ∈ meromorphicPoleSet f Ω) ∧
      (∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤) ∧
      ∀ z ∈ Ω, z ∉ meromorphicPoleSet f Ω → f z = g z / h z := by
  obtain ⟨g, h, hg, hh, hzeros, hfinite, heq⟩ :=
    meromorphic_function_quotient hΩ hf.meromorphicOn
  refine ⟨g, h, hg, hh, hzeros, hfinite, ?_⟩
  intro z hz hpole
  have hfz : AnalyticAt ℂ f z :=
    (hf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (meromorphicOrderAt_nonneg_of_not_pole hf.meromorphicOn hz hpole)
  have hhz : h z ≠ 0 := fun hzero ↦ hpole ((hzeros z hz).mp hzero)
  exact quotient_eq_at_of_codiscrete hΩ hg hh heq hz hfz hhz

#print axioms meromorphic_function_quotient
#print axioms quotient_eq_at_of_codiscrete
#print axioms meromorphic_function_quotient_off_poles

end RudinRCA.Chapter15
