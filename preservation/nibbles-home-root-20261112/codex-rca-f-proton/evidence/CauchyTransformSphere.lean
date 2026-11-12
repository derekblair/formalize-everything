import RudinRCA.Chapter13
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Connected.Clopen

/- This scratch file depends on the declarations in RungeFunctional.lean.
   It is intended for the parent's aggregate check after that source. -/
noncomputable section
open Set Filter Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter13

/-- Transfer a punctured inverse-chart property to the exterior of every compact set. -/
theorem eventually_cobounded_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    {P : ℂ → Prop} (hg : ∀ᶠ w in 𝓝[≠] (0 : ℂ), P (g w)) :
    ∀ᶠ z in Bornology.cobounded ℂ, P (H (z : RiemannSphere)) := by
  have h := (tendsto_inv₀_cobounded' (α := ℂ)).eventually hg
  filter_upwards [h, isBounded_singleton (x := (0 : ℂ))] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  simpa only [heq z⁻¹ (inv_ne_zero hz0'), inv_inv] using hz

/-- The punctured neighborhoods of infinity are exactly the cofinite-compact planar filter. -/
theorem eventually_nhdsNE_infty_iff_cobounded {P : RiemannSphere → Prop} :
    (∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), P p) ↔
      ∀ᶠ z in Bornology.cobounded ℂ, P (z : RiemannSphere) := by
  rw [OnePoint.nhdsNE_infty_eq, Filter.eventually_map,
    coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]

/-- A zero inverse-chart germ is a zero germ at infinity. -/
theorem zeroGerm_infty_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (h∞ : H ∞ = 0)
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    (hg : ∀ᶠ w in 𝓝 (0 : ℂ), g w = 0) :
    ∀ᶠ p in 𝓝 (∞ : RiemannSphere), H p = 0 := by
  have hext := eventually_cobounded_of_inverseChart heq (hg.filter_mono inf_le_left)
  have hpunct : ∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), H p = 0 :=
    eventually_nhdsNE_infty_iff_cobounded.mpr hext
  rw [← nhdsNE_sup_pure (∞ : RiemannSphere), Filter.eventually_sup]
  exact ⟨hpunct, by simpa using h∞⟩

/-- An analytic inverse chart supplies the isolated-zero dichotomy at infinity. -/
theorem zero_dichotomy_infty_of_inverseChart {H : RiemannSphere → ℂ} {g : ℂ → ℂ}
    (h∞ : H ∞ = 0)
    (heq : ∀ w ≠ 0, g w = H ((w⁻¹ : ℂ) : RiemannSphere))
    (hg : AnalyticAt ℂ g 0) :
    (∀ᶠ p in 𝓝 (∞ : RiemannSphere), H p = 0) ∨
      ∀ᶠ p in 𝓝[≠] (∞ : RiemannSphere), H p ≠ 0 := by
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with hz | hn
  · exact Or.inl (zeroGerm_infty_of_inverseChart h∞ heq hz)
  · exact Or.inr (eventually_nhdsNE_infty_iff_cobounded.mpr
      (eventually_cobounded_of_inverseChart heq hn))

/-- The finite complex chart transports the analytic isolated-zero dichotomy. -/
theorem zero_dichotomy_coe {H : RiemannSphere → ℂ} {z : ℂ}
    (hz : AnalyticAt ℂ (fun w : ℂ ↦ H (w : RiemannSphere)) z) :
    (∀ᶠ p in 𝓝 (z : RiemannSphere), H p = 0) ∨
      ∀ᶠ p in 𝓝[≠] (z : RiemannSphere), H p ≠ 0 := by
  rcases hz.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · left
    rwa [OnePoint.nhds_coe_eq, Filter.eventually_map]
  · right
    simpa [OnePoint.nhdsWithin_coe, Filter.eventually_map, preimage, OnePoint.coe_eq_coe] using hne

/-- Restriction to a subspace preserves the isolated-zero dichotomy. -/
theorem zero_dichotomy_subtype {X : Type*} [TopologicalSpace X] (H : X → ℂ)
    (D : Set X) (h : ∀ x ∈ D,
      (∀ᶠ y in 𝓝 x, H y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, H y ≠ 0) (x : D) :
    (∀ᶠ y in 𝓝 x, H y = 0) ∨ ∀ᶠ y in 𝓝[≠] x, H y ≠ 0 := by
  rcases h x x.property with hz | hn
  · exact Or.inl (continuous_subtype_val.continuousAt.tendsto.eventually hz)
  · right
    have ht : Tendsto (Subtype.val : D → X) (𝓝[≠] x) (𝓝[≠] (x : X)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left inf_le_left, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact fun heq ↦ hy (Subtype.ext heq)
    exact ht.eventually hn

/-- The Cauchy transform on the Riemann sphere, with value zero at infinity. -/
def sphereCauchyTransform (K : Set ℂ) [CompactSpace K] (L : C(K, ℂ) →L[ℂ] ℂ) :
    RiemannSphere → ℂ :=
  fun p ↦ OnePoint.elim p 0 (fun z ↦ L (resolvent (compactCoordinate K) z))

@[simp] theorem sphereCauchyTransform_infty (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) : sphereCauchyTransform K L ∞ = 0 := rfl

@[simp] theorem sphereCauchyTransform_coe (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    sphereCauchyTransform K L z = L (resolvent (compactCoordinate K) z) := rfl

/-- The sphere Cauchy transform has isolated zeros or a zero germ at every point off K. -/
theorem sphereCauchyTransform_zero_dichotomy (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) :
    ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      (∀ᶠ q in 𝓝 p, sphereCauchyTransform K L q = 0) ∨
        ∀ᶠ q in 𝓝[≠] p, sphereCauchyTransform K L q ≠ 0 := by
  intro p hp
  induction p using OnePoint.rec with
  | infty =>
    apply zero_dichotomy_infty_of_inverseChart (g := fun w : ℂ ↦
      L (w • Ring.inverse (1 - w • compactCoordinate K))) (by rfl)
    · intro w hw
      rw [sphereCauchyTransform_coe, inverseChart_resolvent_eq _ hw]
    · exact analyticAt_dual_inverseChart_resolvent _ L
  | coe z =>
    apply zero_dichotomy_coe
    have hz : z ∈ Kᶜ := by simpa using hp
    have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
    exact ((differentiableOn_compact_cauchy_transform K L).analyticOnNhd
      hK.isClosed.isOpen_compl) z hz

/-- Prescribed finite poles and infinity each supply the required zero germ. -/
theorem sphereCauchyTransform_zeroGerm_at_prescribed_point (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, L (resolvent (compactCoordinate K) α ^ (n + 1)) = 0)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, L (compactCoordinate K ^ n) = 0) :
    ∀ a ∈ A, ∀ᶠ p in 𝓝 a, sphereCauchyTransform K L p = 0 := by
  intro a ha
  induction a using OnePoint.rec with
  | infty =>
    apply zeroGerm_infty_of_inverseChart (g := fun w : ℂ ↦
      L (w • Ring.inverse (1 - w • compactCoordinate K))) (by rfl)
    · intro w hw
      rw [sphereCauchyTransform_coe, inverseChart_resolvent_eq _ hw]
    · exact dual_inverseChart_resolvent_eventually_eq_zero _ L (hinfty ha)
  | coe α =>
    have hα : α ∈ resolventSet ℂ (compactCoordinate K) := by
      apply spectrum.notMem_iff.mp
      rw [spectrum_compactCoordinate]
      simpa using hA ha
    have hz := dual_resolvent_eventually_eq_zero (compactCoordinate K) L hα (hfinite α ha)
    simpa [OnePoint.nhds_coe_eq, Filter.eventually_map, sphereCauchyTransform] using hz

/-- The analytic core of Runge: annihilating principal parts at a point in every
    spherical complement component annihilates every Cauchy kernel off K. -/
theorem compact_cauchy_transform_eq_zero (K : Set ℂ) [CompactSpace K]
    (L : C(K, ℂ) →L[ℂ] ℂ) (A : Set RiemannSphere)
    (hA : A ⊆ (((↑) : ℂ → RiemannSphere) '' K)ᶜ)
    (hcomponents : ∀ p ∈ (((↑) : ℂ → RiemannSphere) '' K)ᶜ,
      ∃ a ∈ A, a ∈ connectedComponentIn (((↑) : ℂ → RiemannSphere) '' K)ᶜ p)
    (hfinite : ∀ α : ℂ, (α : RiemannSphere) ∈ A →
      ∀ n : ℕ, L (resolvent (compactCoordinate K) α ^ (n + 1)) = 0)
    (hinfty : (∞ : RiemannSphere) ∈ A → ∀ n : ℕ, L (compactCoordinate K ^ n) = 0) :
    ∀ z ∉ K, L (resolvent (compactCoordinate K) z) = 0 := by
  let D : Set RiemannSphere := (((↑) : ℂ → RiemannSphere) '' K)ᶜ
  let H : D → ℂ := fun p ↦ sphereCauchyTransform K L p
  have hiso : ∀ p : D, (∀ᶠ q in 𝓝 p, H q = 0) ∨ ∀ᶠ q in 𝓝[≠] p, H q ≠ 0 :=
    zero_dichotomy_subtype _ D (sphereCauchyTransform_zero_dichotomy K L)
  have hall : ∀ p : D, H p = 0 := by
    apply eq_zero_of_zeroGerm_in_each_component H hiso
    intro p
    obtain ⟨a, ha, hac⟩ := hcomponents p p.property
    let aD : D := ⟨a, hA ha⟩
    have hac' : aD ∈ connectedComponent p := by
      rw [connectedComponentIn_eq_image p.property] at hac
      obtain ⟨b, hb, hba⟩ := hac
      have hba' : b = aD := Subtype.ext hba
      simpa only [hba'] using hb
    refine ⟨aD, hac', ?_⟩
    exact continuous_subtype_val.continuousAt.tendsto.eventually
      (sphereCauchyTransform_zeroGerm_at_prescribed_point K L A hA hfinite hinfty a ha)
  intro z hz
  have hzd : (z : RiemannSphere) ∈ D := by simpa [D] using hz
  exact hall ⟨z, hzd⟩

end RudinRCA.Chapter13

#print axioms RudinRCA.Chapter13.compact_cauchy_transform_eq_zero
