import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
open scoped OnePoint
open Set Metric Submodule
open scoped RealInnerProductSpace

namespace RudinRCA.Chapter13

abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)

def northPole : SphereAmbient := !₂[0, 0, 1]

theorem norm_northPole : ‖northPole‖ = 1 := by
  simp [northPole, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

theorem mem_north_orthogonal_iff (w : SphereAmbient) :
    w ∈ (ℝ ∙ northPole)ᗮ ↔ w 2 = 0 := by
  simp [Submodule.mem_orthogonal_singleton_iff_inner_left, northPole,
    PiLp.inner_apply, Fin.sum_univ_succ]

/-- The factor two accounts for Mathlib's normalization of stereographic projection. -/
def complexPlaneEquiv : ℂ ≃ₗ[ℝ] (ℝ ∙ northPole)ᗮ where
  toFun z := ⟨!₂[2 * z.re, 2 * z.im, 0], (mem_north_orthogonal_iff _).mpr (by simp)⟩
  invFun w := (w.1 0 / 2 : ℝ) + (w.1 1 / 2 : ℝ) * Complex.I
  left_inv z := by
    apply Complex.ext <;> simp <;> ring
  right_inv w := by
    apply Subtype.ext
    ext i
    have hw := (mem_north_orthogonal_iff w.1).mp w.2
    fin_cases i <;> simp [hw] <;> ring
  map_add' z w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' r z := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem complexPlaneEquiv_coe (z : ℂ) :
    (complexPlaneEquiv z : SphereAmbient) = !₂[2 * z.re, 2 * z.im, 0] := rfl

def bookSphereHomeomorph :
    OnePoint ℂ ≃ₜ sphere (0 : SphereAmbient) 1 :=
  complexPlaneEquiv.toContinuousLinearEquiv.toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere norm_northPole)

theorem bookSphereHomeomorph_infty :
    (bookSphereHomeomorph ∞ : SphereAmbient) = northPole := by
  simp [bookSphereHomeomorph, onePointHyperplaneHomeoUnitSphere]

theorem norm_complexPlaneEquiv_sq (z : ℂ) :
    ‖(complexPlaneEquiv z : SphereAmbient)‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
  rw [complexPlaneEquiv_coe, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Rudin's displayed stereographic coordinates, in Cartesian form. -/
theorem bookSphereHomeomorph_coe (z : ℂ) :
    (bookSphereHomeomorph (z : OnePoint ℂ) : SphereAmbient) =
      !₂[2 * z.re / (‖z‖ ^ 2 + 1), 2 * z.im / (‖z‖ ^ 2 + 1),
        (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)] := by
  change stereoInvFunAux northPole (complexPlaneEquiv z) = _
  rw [stereoInvFunAux_apply, norm_complexPlaneEquiv_sq, complexPlaneEquiv_coe]
  have hpos : 0 < ‖z‖ ^ 2 + 1 := by positivity
  have hpos' : 0 < 4 * ‖z‖ ^ 2 + 4 := by positivity
  ext i
  fin_cases i <;> simp [northPole] <;>
    field_simp [ne_of_gt hpos, ne_of_gt hpos'] <;> ring

#print axioms norm_northPole
#print axioms mem_north_orthogonal_iff
#print axioms complexPlaneEquiv
#print axioms bookSphereHomeomorph
#print axioms bookSphereHomeomorph_infty
#print axioms norm_complexPlaneEquiv_sq
#print axioms bookSphereHomeomorph_coe

end RudinRCA.Chapter13
