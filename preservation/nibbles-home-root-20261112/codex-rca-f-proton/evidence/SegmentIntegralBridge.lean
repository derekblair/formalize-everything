import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Ring

open Complex intervalIntegral
open scoped Topology

namespace RudinRCA.Chapter13Scratch

/-- Complex line integration over an oriented segment, using its affine parametrization. -/
noncomputable def complexSegmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t : ℝ in 0..1, f (AffineMap.lineMap a b t) * (b - a)

/-- The explicit affine-parameter integral is Mathlib's curve integral of the complex 1-form
`f(z) dz` over `Path.segment a b`. -/
theorem curveIntegral_segment_eq_complexSegmentIntegral (f : ℂ → ℂ) (a b : ℂ) :
    curveIntegral (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (Path.segment a b) =
      complexSegmentIntegral f a b := by
  simpa only [complexSegmentIntegral, ContinuousLinearMap.mul_apply'] using
    curveIntegral_segment (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) a b

/-- Horizontal segment integration agrees with an ordinary oriented real interval integral. -/
theorem complexSegmentIntegral_horizontal (f : ℂ → ℂ) (a b c : ℝ) :
    complexSegmentIntegral f ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (c : ℂ) * I) =
      ∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * I) := by
  have hdelta : ((b : ℂ) + (c : ℂ) * I) - ((a : ℂ) + (c : ℂ) * I) =
      ((b - a : ℝ) : ℂ) := by push_cast; ring
  have hline (t : ℝ) :
      AffineMap.lineMap ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (c : ℂ) * I) t =
      (((b - a) * t + a : ℝ) : ℂ) + (c : ℂ) * I := by
    rw [AffineMap.lineMap_apply_module', hdelta]
    change (t : ℂ) * ((b - a : ℝ) : ℂ) + ((a : ℂ) + (c : ℂ) * I) = _
    push_cast
    ring
  calc
    _ = (b - a) • (∫ t : ℝ in 0..1,
        f ((((b - a) * t + a : ℝ) : ℂ) + (c : ℂ) * I)) := by
      rw [← integral_smul]
      apply integral_congr
      intro t ht
      rw [hline, hdelta]
      change _ = ((b - a : ℝ) : ℂ) * _
      ring
    _ = ∫ x : ℝ in (b - a) * 0 + a..(b - a) * 1 + a,
        f ((x : ℂ) + (c : ℂ) * I) :=
      smul_integral_comp_mul_add (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)) (b - a) a
    _ = _ := by simp

/-- Vertical segment integration agrees with `I` times an ordinary oriented interval integral. -/
theorem complexSegmentIntegral_vertical (f : ℂ → ℂ) (a b c : ℝ) :
    complexSegmentIntegral f ((c : ℂ) + (a : ℂ) * I) ((c : ℂ) + (b : ℂ) * I) =
      I * ∫ y : ℝ in a..b, f ((c : ℂ) + (y : ℂ) * I) := by
  have hdelta : ((c : ℂ) + (b : ℂ) * I) - ((c : ℂ) + (a : ℂ) * I) =
      ((b - a : ℝ) : ℂ) * I := by push_cast; ring
  have hline (t : ℝ) :
      AffineMap.lineMap ((c : ℂ) + (a : ℂ) * I) ((c : ℂ) + (b : ℂ) * I) t =
      (c : ℂ) + (((b - a) * t + a : ℝ) : ℂ) * I := by
    rw [AffineMap.lineMap_apply_module', hdelta]
    change (t : ℂ) * (((b - a : ℝ) : ℂ) * I) + ((c : ℂ) + (a : ℂ) * I) = _
    push_cast
    ring
  calc
    _ = I * ((b - a) • (∫ t : ℝ in 0..1,
        f ((c : ℂ) + (((b - a) * t + a : ℝ) : ℂ) * I))) := by
      rw [← integral_smul, ← integral_const_mul]
      apply integral_congr
      intro t ht
      rw [hline, hdelta]
      change _ = I * (((b - a : ℝ) : ℂ) * _)
      ring
    _ = I * (∫ y : ℝ in (b - a) * 0 + a..(b - a) * 1 + a,
        f ((c : ℂ) + (y : ℂ) * I)) := by
      rw [smul_integral_comp_mul_add]
    _ = _ := by simp

theorem complexSegmentIntegral_symm (f : ℂ → ℂ) (a b : ℂ) :
    complexSegmentIntegral f b a = -complexSegmentIntegral f a b := by
  rw [← curveIntegral_segment_eq_complexSegmentIntegral,
    ← curveIntegral_segment_eq_complexSegmentIntegral]
  simpa using curveIntegral_symm (fun z => ContinuousLinearMap.mul ℂ ℂ (f z)) (Path.segment a b)

#print axioms curveIntegral_segment_eq_complexSegmentIntegral
#print axioms complexSegmentIntegral_horizontal
#print axioms complexSegmentIntegral_vertical
#print axioms complexSegmentIntegral_symm

end RudinRCA.Chapter13Scratch
