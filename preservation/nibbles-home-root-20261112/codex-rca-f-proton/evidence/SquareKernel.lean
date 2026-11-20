import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Complex intervalIntegral

namespace RudinRCA.Chapter13Scratch

theorem square_kernel_integrand (t : ℝ) :
    ((t : ℂ) - I)⁻¹ - ((t : ℂ) + I)⁻¹ +
      I * (1 + (t : ℂ) * I)⁻¹ - I * (-1 + (t : ℂ) * I)⁻¹ =
      4 * I * ((1 / (1 + t ^ 2) : ℝ) : ℂ) := by
  have h₁ : (t : ℂ) - I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h₂ : (t : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h₃ : 1 + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h₄ : -1 + (t : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have h₅ : (1 : ℂ) + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1 + t ^ 2 by positivity))
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq, pow_succ]
  <;> ring

/-- The positively oriented unit-square boundary integral of `1 / z` is `2πi`.
The four summands are bottom, top (reversed), right, and left (reversed). -/
theorem unit_square_kernel :
    (∫ t : ℝ in -1..1, ((t : ℂ) - I)⁻¹) -
      (∫ t : ℝ in -1..1, ((t : ℂ) + I)⁻¹) +
      I * (∫ t : ℝ in -1..1, (1 + (t : ℂ) * I)⁻¹) -
      I * (∫ t : ℝ in -1..1, (-1 + (t : ℂ) * I)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  have h₁ : Continuous (fun t : ℝ => ((t : ℂ) - I)⁻¹) := by
    refine (Complex.continuous_ofReal.sub continuous_const).inv₀ ?_
    intro t h
    have := congrArg Complex.im h
    norm_num at this
  have h₂ : Continuous (fun t : ℝ => ((t : ℂ) + I)⁻¹) := by
    refine (Complex.continuous_ofReal.add continuous_const).inv₀ ?_
    intro t h
    have := congrArg Complex.im h
    norm_num at this
  have h₃ : Continuous (fun t : ℝ => (1 + (t : ℂ) * I)⁻¹) := by
    refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
    intro t h
    have := congrArg Complex.re h
    norm_num at this
  have h₄ : Continuous (fun t : ℝ => (-1 + (t : ℂ) * I)⁻¹) := by
    refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
    intro t h
    have := congrArg Complex.re h
    norm_num at this
  have hi₁ : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - I)⁻¹)
      MeasureTheory.volume (-1) 1 := h₁.intervalIntegrable (-1) 1
  have hi₂ : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + I)⁻¹)
      MeasureTheory.volume (-1) 1 := h₂.intervalIntegrable (-1) 1
  have hi₃ : IntervalIntegrable (fun t : ℝ => I * (1 + (t : ℂ) * I)⁻¹)
      MeasureTheory.volume (-1) 1 := (h₃.intervalIntegrable (-1) 1).const_mul I
  have hi₄ : IntervalIntegrable (fun t : ℝ => I * (-1 + (t : ℂ) * I)⁻¹)
      MeasureTheory.volume (-1) 1 := (h₄.intervalIntegrable (-1) 1).const_mul I
  calc
    _ = ∫ t : ℝ in -1..1, (((t : ℂ) - I)⁻¹ - ((t : ℂ) + I)⁻¹ +
        I * (1 + (t : ℂ) * I)⁻¹ - I * (-1 + (t : ℂ) * I)⁻¹) := by
      rw [integral_sub ((hi₁.sub hi₂).add hi₃) hi₄,
        integral_add (hi₁.sub hi₂) hi₃, integral_sub hi₁ hi₂,
        integral_const_mul, integral_const_mul]
    _ = ∫ t : ℝ in -1..1, 4 * I * ((1 / (1 + t ^ 2) : ℝ) : ℂ) := by
      apply integral_congr
      intro t ht
      exact square_kernel_integrand t
    _ = 2 * (Real.pi : ℂ) * I := by
      rw [integral_const_mul, intervalIntegral.integral_ofReal, integral_one_div_one_add_sq,
        Real.arctan_neg, Real.arctan_one]
      push_cast
      ring

#print axioms square_kernel_integrand
#print axioms unit_square_kernel

theorem integral_scaled_affine_inv {r : ℝ} (hr : r ≠ 0) (a b : ℂ) :
    (∫ t : ℝ in -r..r, ((r : ℂ) * a + (t : ℂ) * b)⁻¹) =
      ∫ t : ℝ in -1..1, (a + (t : ℂ) * b)⁻¹ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have h := smul_integral_comp_mul_left
    (fun t : ℝ => ((r : ℂ) * a + (t : ℂ) * b)⁻¹) (a := -1) (b := 1) r
  simp only [mul_neg_one, mul_one] at h
  rw [← h, ← integral_smul]
  apply integral_congr
  intro t ht
  change (r : ℂ) * ((r : ℂ) * a + ((r * t : ℝ) : ℂ) * b)⁻¹ = _
  push_cast
  rw [show (r : ℂ) * a + (r : ℂ) * (t : ℂ) * b =
    (r : ℂ) * (a + (t : ℂ) * b) by ring, mul_inv_rev]
  calc
    _ = ((a + (t : ℂ) * b)⁻¹) * ((r : ℂ) * (r : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hrC, mul_one]

/-- Positively oriented boundary integral of the centered square with side length `2r`.
This is the local normalization needed in the polygonal Cauchy construction. -/
theorem centered_square_kernel {r : ℝ} (hr : r ≠ 0) :
    (∫ t : ℝ in -r..r, ((t : ℂ) - (r : ℂ) * I)⁻¹) -
      (∫ t : ℝ in -r..r, ((t : ℂ) + (r : ℂ) * I)⁻¹) +
      I * (∫ t : ℝ in -r..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) -
      I * (∫ t : ℝ in -r..r, (-(r : ℂ) + (t : ℂ) * I)⁻¹) =
      2 * (Real.pi : ℂ) * I := by
  have hb : (∫ t : ℝ in -r..r, ((t : ℂ) - (r : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, ((t : ℂ) - I)⁻¹ := by
    simpa [sub_eq_add_neg, add_comm] using integral_scaled_affine_inv hr (-I) 1
  have ht : (∫ t : ℝ in -r..r, ((t : ℂ) + (r : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, ((t : ℂ) + I)⁻¹ := by
    simpa [add_comm] using integral_scaled_affine_inv hr I 1
  have hr' : (∫ t : ℝ in -r..r, ((r : ℂ) + (t : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, (1 + (t : ℂ) * I)⁻¹ := by
    simpa using integral_scaled_affine_inv hr 1 I
  have hl : (∫ t : ℝ in -r..r, (-(r : ℂ) + (t : ℂ) * I)⁻¹) =
      ∫ t : ℝ in -1..1, (-1 + (t : ℂ) * I)⁻¹ := by
    simpa using integral_scaled_affine_inv hr (-1) I
  rw [hb, ht, hr', hl]
  exact unit_square_kernel

/-- Counterclockwise boundary integral on an axis-parallel rectangle. -/
noncomputable def rectangleIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
    (∫ x : ℝ in a..b, f ((x : ℂ) + (c : ℂ) * I)) -
      (∫ x : ℝ in a..b, f ((x : ℂ) + (d : ℂ) * I)) +
      I * (∫ y : ℝ in c..d, f ((b : ℂ) + (y : ℂ) * I)) -
      I * (∫ y : ℝ in c..d, f ((a : ℂ) + (y : ℂ) * I))

theorem rectangleIntegral_eq_zero (f : ℂ → ℂ) (a b c d : ℝ)
    (hf : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    rectangleIntegral f a b c d = 0 := by
  simpa [rectangleIntegral, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (c : ℂ) * I) ((b : ℂ) + (d : ℂ) * I) (by simpa using hf)

theorem rectangle_kernel_zero_of_horizontal (a b c d : ℝ)
    (h : (0 : ℝ) ∉ Set.uIcc c d) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  apply differentiableOn_id.inv
  intro z hz heq
  apply h
  simpa [heq] using hz.2

theorem rectangle_kernel_zero_of_vertical (a b c d : ℝ)
    (h : (0 : ℝ) ∉ Set.uIcc a b) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  apply differentiableOn_id.inv
  intro z hz heq
  apply h
  simpa [heq] using hz.1

#print axioms integral_scaled_affine_inv
#print axioms centered_square_kernel
#print axioms rectangleIntegral_eq_zero
#print axioms rectangle_kernel_zero_of_horizontal
#print axioms rectangle_kernel_zero_of_vertical

theorem rectangleIntegral_split_vertical (f : ℂ → ℂ) (a b c d e : ℝ)
    (ha : Continuous (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I)))
    (hb : Continuous (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I))) :
    rectangleIntegral f a b c e =
      rectangleIntegral f a b c d + rectangleIntegral f a b d e := by
  have hA := integral_add_adjacent_intervals
    (ha.intervalIntegrable (μ := MeasureTheory.volume) (a := c) (b := d))
    (ha.intervalIntegrable (μ := MeasureTheory.volume) (a := d) (b := e))
  have hB := integral_add_adjacent_intervals
    (hb.intervalIntegrable (μ := MeasureTheory.volume) (a := c) (b := d))
    (hb.intervalIntegrable (μ := MeasureTheory.volume) (a := d) (b := e))
  dsimp [rectangleIntegral]
  rw [← hA, ← hB]
  ring

theorem rectangleIntegral_split_horizontal (f : ℂ → ℂ) (a b c d e : ℝ)
    (hc : Continuous (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I)))
    (hd : Continuous (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))) :
    rectangleIntegral f a e c d =
      rectangleIntegral f a b c d + rectangleIntegral f b e c d := by
  have hC := integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b))
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (a := b) (b := e))
  have hD := integral_add_adjacent_intervals
    (hd.intervalIntegrable (μ := MeasureTheory.volume) (a := a) (b := b))
    (hd.intervalIntegrable (μ := MeasureTheory.volume) (a := b) (b := e))
  dsimp [rectangleIntegral]
  rw [← hC, ← hD]
  ring

theorem continuous_horizontal_kernel {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((t : ℂ) + (c : ℂ) * I)⁻¹) := by
  refine (Complex.continuous_ofReal.add continuous_const).inv₀ ?_
  intro t h
  apply hc
  simpa using congrArg Complex.im h

theorem continuous_vertical_kernel {c : ℝ} (hc : c ≠ 0) :
    Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I)⁻¹) := by
  refine (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ ?_
  intro t h
  apply hc
  simpa using congrArg Complex.re h

/-- Kernel normalization on every axis-parallel rectangle containing the origin in its interior.
The proof excises a smaller centered square using four rectangles avoiding the singularity. -/
theorem rectangle_kernel {a b c d : ℝ} (ha : a < 0) (hb : 0 < b)
    (hc : c < 0) (hd : 0 < d) :
    rectangleIntegral (fun z : ℂ => z⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  let r := min (min (-a) b) (min (-c) d) / 2
  have hmin : 0 < min (min (-a) b) (min (-c) d) :=
    lt_min (lt_min (neg_pos.mpr ha) hb) (lt_min (neg_pos.mpr hc) hd)
  have hr : 0 < r := half_pos hmin
  have hsmall : r < min (min (-a) b) (min (-c) d) := half_lt_self hmin
  have hra : a < -r := by
    have := hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    linarith
  have hrb : r < b := hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hrc : c < -r := by
    have := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hrd : r < d := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hV₁ := rectangleIntegral_split_vertical (fun z : ℂ => z⁻¹) a b c (-r) d
    (continuous_vertical_kernel (ne_of_lt ha)) (continuous_vertical_kernel (ne_of_gt hb))
  have hV₂ := rectangleIntegral_split_vertical (fun z : ℂ => z⁻¹) a b (-r) r d
    (continuous_vertical_kernel (ne_of_lt ha)) (continuous_vertical_kernel (ne_of_gt hb))
  have hH₁ := rectangleIntegral_split_horizontal (fun z : ℂ => z⁻¹) a (-r) (-r) r b
    (continuous_horizontal_kernel (neg_ne_zero.mpr (ne_of_gt hr)))
    (continuous_horizontal_kernel (ne_of_gt hr))
  have hH₂ := rectangleIntegral_split_horizontal (fun z : ℂ => z⁻¹) (-r) r (-r) r b
    (continuous_horizontal_kernel (neg_ne_zero.mpr (ne_of_gt hr)))
    (continuous_horizontal_kernel (ne_of_gt hr))
  have hbottom : rectangleIntegral (fun z : ℂ => z⁻¹) a b c (-r) = 0 := by
    apply rectangle_kernel_zero_of_horizontal
    rw [Set.uIcc_of_le hrc.le]
    intro h
    linarith [h.2]
  have htop : rectangleIntegral (fun z : ℂ => z⁻¹) a b r d = 0 := by
    apply rectangle_kernel_zero_of_horizontal
    rw [Set.uIcc_of_le hrd.le]
    intro h
    linarith [h.1]
  have hleft : rectangleIntegral (fun z : ℂ => z⁻¹) a (-r) (-r) r = 0 := by
    apply rectangle_kernel_zero_of_vertical
    rw [Set.uIcc_of_le hra.le]
    intro h
    linarith [h.2]
  have hright : rectangleIntegral (fun z : ℂ => z⁻¹) r b (-r) r = 0 := by
    apply rectangle_kernel_zero_of_vertical
    rw [Set.uIcc_of_le hrb.le]
    intro h
    linarith [h.1]
  rw [hV₁, hV₂, hH₁, hH₂, hbottom, htop, hleft, hright]
  simpa [rectangleIntegral, sub_eq_add_neg] using centered_square_kernel (ne_of_gt hr)

#print axioms rectangleIntegral_split_vertical
#print axioms rectangleIntegral_split_horizontal
#print axioms continuous_horizontal_kernel
#print axioms continuous_vertical_kernel
#print axioms rectangle_kernel

theorem rectangleIntegral_translate (f : ℂ → ℂ) (a b c d : ℝ) (z : ℂ) :
    rectangleIntegral (fun w => f (w + z)) a b c d =
      rectangleIntegral f (a + z.re) (b + z.re) (c + z.im) (d + z.im) := by
  have hh (q : ℝ) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (q : ℂ) * I + z)) =
      ∫ x : ℝ in a + z.re..b + z.re, f ((x : ℂ) + ((q + z.im : ℝ) : ℂ) * I) := by
    calc
      _ = ∫ x : ℝ in a..b,
          f (((x + z.re : ℝ) : ℂ) + ((q + z.im : ℝ) : ℂ) * I) := by
        apply integral_congr
        intro x hx
        apply congrArg f
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right
        (fun x : ℝ => f ((x : ℂ) + ((q + z.im : ℝ) : ℂ) * I)) (a := a) (b := b) z.re
  have hv (q : ℝ) :
      (∫ y : ℝ in c..d, f ((q : ℂ) + (y : ℂ) * I + z)) =
      ∫ y : ℝ in c + z.im..d + z.im, f (((q + z.re : ℝ) : ℂ) + (y : ℂ) * I) := by
    calc
      _ = ∫ y : ℝ in c..d,
          f (((q + z.re : ℝ) : ℂ) + ((y + z.im : ℝ) : ℂ) * I) := by
        apply integral_congr
        intro y hy
        apply congrArg f
        apply Complex.ext <;> simp <;> ring
      _ = _ := integral_comp_add_right
        (fun y : ℝ => f (((q + z.re : ℝ) : ℂ) + (y : ℂ) * I)) (a := c) (b := d) z.im
  dsimp [rectangleIntegral]
  rw [hh, hh, hv, hv]

theorem rectangle_kernel_at {a b c d : ℝ} {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleIntegral (fun w : ℂ => (w - z)⁻¹) a b c d =
      2 * (Real.pi : ℂ) * I := by
  have ht := rectangleIntegral_translate (fun w : ℂ => (w - z)⁻¹)
    (a - z.re) (b - z.re) (c - z.im) (d - z.im) z
  simp only [add_sub_cancel_right, sub_add_cancel] at ht
  rw [← ht]
  exact rectangle_kernel (by linarith) (by linarith) (by linarith) (by linarith)

#print axioms rectangleIntegral_translate
#print axioms rectangle_kernel_at

structure RectangleBoundaryIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (c : ℂ) * I))
    MeasureTheory.volume a b
  top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (d : ℂ) * I))
    MeasureTheory.volume a b
  right : IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * I))
    MeasureTheory.volume c d
  left : IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * I))
    MeasureTheory.volume c d

theorem rectangleBoundaryIntegrable_of_continuousOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (Set.uIcc a b ×ℂ Set.uIcc c d)) :
    RectangleBoundaryIntegrable f a b c d := by
  have hh (q : ℝ) (hq : q ∈ Set.uIcc c d) :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + (q : ℂ) * I)) (Set.uIcc a b) := by
    refine hf.comp (by fun_prop) ?_
    intro x hx
    simpa [Complex.mem_reProdIm] using And.intro hx hq
  have hv (q : ℝ) (hq : q ∈ Set.uIcc a b) :
      ContinuousOn (fun y : ℝ => f ((q : ℂ) + (y : ℂ) * I)) (Set.uIcc c d) := by
    refine hf.comp (by fun_prop) ?_
    intro y hy
    simpa [Complex.mem_reProdIm] using And.intro hq hy
  exact ⟨(hh c (Set.left_mem_uIcc)).intervalIntegrable,
    (hh d (Set.right_mem_uIcc)).intervalIntegrable,
    (hv b (Set.right_mem_uIcc)).intervalIntegrable,
    (hv a (Set.left_mem_uIcc)).intervalIntegrable⟩

theorem rectangle_kernel_boundaryIntegrable {a b c d : ℝ} {z : ℂ}
    (ha : a ≠ z.re) (hb : b ≠ z.re) (hc : c ≠ z.im) (hd : d ≠ z.im) :
    RectangleBoundaryIntegrable (fun w : ℂ => (w - z)⁻¹) a b c d := by
  have hh (q : ℝ) (hq : q ≠ z.im) :
      Continuous (fun x : ℝ => ((x : ℂ) + (q : ℂ) * I - z)⁻¹) := by
    refine ((Complex.continuous_ofReal.add continuous_const).sub continuous_const).inv₀ ?_
    intro x h
    apply hq
    have h' := congrArg Complex.im h
    have : q - z.im = 0 := by simpa using h'
    exact sub_eq_zero.mp this
  have hv (q : ℝ) (hq : q ≠ z.re) :
      Continuous (fun y : ℝ => ((q : ℂ) + (y : ℂ) * I - z)⁻¹) := by
    refine ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
      continuous_const).inv₀ ?_
    intro y h
    apply hq
    have h' := congrArg Complex.re h
    have : q - z.re = 0 := by simpa using h'
    exact sub_eq_zero.mp this
  exact ⟨(hh c hc).intervalIntegrable a b, (hh d hd).intervalIntegrable a b,
    (hv b hb).intervalIntegrable c d, (hv a ha).intervalIntegrable c d⟩

theorem rectangleIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleBoundaryIntegrable f a b c d)
    (hg : RectangleBoundaryIntegrable g a b c d) :
    rectangleIntegral (fun w => f w + g w) a b c d =
      rectangleIntegral f a b c d + rectangleIntegral g a b c d := by
  dsimp [rectangleIntegral]
  rw [integral_add hf.bottom hg.bottom, integral_add hf.top hg.top,
    integral_add hf.right hg.right, integral_add hf.left hg.left]
  ring

theorem rectangleIntegral_mul_const (f : ℂ → ℂ) (a b c d : ℝ) (v : ℂ) :
    rectangleIntegral (fun w => f w * v) a b c d = rectangleIntegral f a b c d * v := by
  simp only [rectangleIntegral, integral_mul_const]
  ring

theorem rectangleIntegral_congr_off_interiorPoint {f g : ℂ → ℂ} {a b c d : ℝ} {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d)
    (hfg : ∀ w ≠ z, f w = g w) : rectangleIntegral f a b c d = rectangleIntegral g a b c d := by
  have hh (q : ℝ) (hq : q ≠ z.im) :
      (∫ x : ℝ in a..b, f ((x : ℂ) + (q : ℂ) * I)) =
      ∫ x : ℝ in a..b, g ((x : ℂ) + (q : ℂ) * I) := by
    apply integral_congr
    intro x hx
    apply hfg
    intro h
    apply hq
    simpa using congrArg Complex.im h
  have hv (q : ℝ) (hq : q ≠ z.re) :
      (∫ y : ℝ in c..d, f ((q : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in c..d, g ((q : ℂ) + (y : ℂ) * I) := by
    apply integral_congr
    intro y hy
    apply hfg
    intro h
    apply hq
    simpa using congrArg Complex.re h
  dsimp [rectangleIntegral]
  rw [hh c (ne_of_lt hc), hh d (ne_of_gt hd), hv b (ne_of_gt hb), hv a (ne_of_lt ha)]

/-- Cauchy's evaluation formula on a positively oriented rectangle compactly contained in an
open holomorphy domain. The integrals are the ordinary four oriented edge integrals. -/
theorem rectangle_cauchy_formula {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {a b c d : ℝ}
    (hrect : Set.uIcc a b ×ℂ Set.uIcc c d ⊆ Ω) {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleIntegral (fun w => f w / (w - z)) a b c d =
      2 * (Real.pi : ℂ) * I * f z := by
  have hz : z ∈ Ω := hrect ⟨Set.mem_uIcc.mpr (Or.inl ⟨ha.le, hb.le⟩),
    Set.mem_uIcc.mpr (Or.inl ⟨hc.le, hd.le⟩)⟩
  have hg : DifferentiableOn ℂ (dslope f z) Ω :=
    (Complex.differentiableOn_dslope (hΩ.mem_nhds hz)).mpr hf
  have hgint := rectangleBoundaryIntegrable_of_continuousOn (hg.continuousOn.mono hrect)
  have hkint := rectangle_kernel_boundaryIntegrable
    (ne_of_lt ha) (ne_of_gt hb) (ne_of_lt hc) (ne_of_gt hd)
  have hkmul : RectangleBoundaryIntegrable (fun w : ℂ => (w - z)⁻¹ * f z) a b c d :=
    ⟨hkint.bottom.mul_const _, hkint.top.mul_const _,
      hkint.right.mul_const _, hkint.left.mul_const _⟩
  have hdecomp : rectangleIntegral (fun w => f w / (w - z)) a b c d =
      rectangleIntegral (fun w => dslope f z w + (w - z)⁻¹ * f z) a b c d := by
    apply rectangleIntegral_congr_off_interiorPoint ha hb hc hd
    intro w hw
    rw [dslope_of_ne f hw, slope_def_field]
    simp only [div_eq_mul_inv]
    ring
  rw [hdecomp, rectangleIntegral_add hgint hkmul,
    rectangleIntegral_eq_zero (dslope f z) a b c d (hg.mono hrect), zero_add,
    rectangleIntegral_mul_const, rectangle_kernel_at ha hb hc hd]

#print axioms rectangleBoundaryIntegrable_of_continuousOn
#print axioms rectangle_kernel_boundaryIntegrable
#print axioms rectangleIntegral_add
#print axioms rectangleIntegral_mul_const
#print axioms rectangleIntegral_congr_off_interiorPoint
#print axioms rectangle_cauchy_formula

/-- The same rectangle integral vanishes when the evaluation point lies outside the closed
rectangle. Together with the interior formula this supplies the two cases in a square-grid sum. -/
theorem rectangle_cauchy_formula_of_not_mem {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f Ω) {a b c d : ℝ}
    (hrect : Set.uIcc a b ×ℂ Set.uIcc c d ⊆ Ω) {z : ℂ}
    (hz : z ∉ Set.uIcc a b ×ℂ Set.uIcc c d) :
    rectangleIntegral (fun w => f w / (w - z)) a b c d = 0 := by
  apply rectangleIntegral_eq_zero
  refine (hf.mono hrect).div (differentiableOn_id.sub_const z) ?_
  intro w hw
  apply sub_ne_zero.mpr
  intro hwz
  exact hz (hwz ▸ hw)

#print axioms rectangle_cauchy_formula_of_not_mem

end RudinRCA.Chapter13Scratch
