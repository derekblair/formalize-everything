import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open MeasureTheory
namespace RudinRCA.Chapter06
variable {X : Type*} [MeasurableSpace X]

private theorem norm_star_lp_two (μ : Measure X) (g : Lp ℂ 2 μ) : ‖star g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star g), eLpNorm_star]

private theorem inner_star_lp_two (μ : Measure X) (g f : Lp ℂ 2 μ) :
    inner ℂ (star g) f = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star g] with x hx
  rw [hx]
  simp [RCLike.inner_apply]

/-- 6.17: the Hilbert-space case of complex Lp duality, with the book's
unconjugated product convention explicitly obtained by conjugating the Riesz vector.
The general 6.16 theorem remains a separate obligation. -/
theorem hilbert_lp_duality (μ : Measure X) (Φ : Lp ℂ 2 μ →L[ℂ] ℂ) :
    ∃! g : Lp ℂ 2 μ, (∀ f, Φ f = ∫ x, f x * g x ∂μ) ∧ ‖Φ‖ = ‖g‖ := by
  let y := (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm Φ
  have hre : ∀ f, Φ f = ∫ x, f x * (star y) x ∂μ := by
    intro f
    calc
      Φ f = inner ℂ y f := InnerProductSpace.toDual_symm_apply.symm
      _ = inner ℂ (star (star y)) f := by rw [star_star]
      _ = ∫ x, f x * (star y) x ∂μ := inner_star_lp_two μ (star y) f
  refine ⟨star y, ⟨hre, ?_⟩, ?_⟩
  · rw [norm_star_lp_two]
    exact ((InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).symm.norm_map Φ).symm
  · intro g hg
    apply star_injective
    apply (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ)).injective
    ext f
    simpa only [InnerProductSpace.toDual_apply_apply, inner_star_lp_two] using
      (hg.1 f).symm.trans (hre f)

#print axioms hilbert_lp_duality
end RudinRCA.Chapter06
