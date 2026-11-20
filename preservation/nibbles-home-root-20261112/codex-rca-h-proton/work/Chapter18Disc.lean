import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open Set Metric Filter
open scoped Topology NNReal ENNReal

namespace RudinRCA.Chapter18

set_option backward.isDefEq.respectTransparency false

abbrev DiscClosed := ↥(closedBall (0 : ℂ) 1)
abbrev DiscCircle := ↥(sphere (0 : ℂ) 1)

instance discClosedNonempty : Nonempty DiscClosed := ⟨⟨0, by simp⟩⟩
instance discCircleNonempty : Nonempty DiscCircle := ⟨⟨1, by simp⟩⟩

/-- The values outside the closed disc only totalize a function on a subtype. -/
def discExtend (f : C(DiscClosed, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ closedBall (0 : ℂ) 1 then f ⟨z, hz⟩ else 0

@[simp] theorem discExtend_apply (f : C(DiscClosed, ℂ)) (z : DiscClosed) :
    discExtend f z = f z := by simp [discExtend, z.property]

theorem discExtend_continuousOn (f : C(DiscClosed, ℂ)) :
    ContinuousOn (discExtend f) (closedBall (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (closedBall (0 : ℂ) 1).domRestrict (discExtend f) = f :=
    funext (fun z => discExtend_apply f z)
  rw [heq]
  exact f.continuous

/-- The disc algebra: continuous on the closed disc and holomorphic in its interior. -/
def discSubalgebra : Subalgebra ℂ C(DiscClosed, ℂ) where
  carrier := {f | DifferentiableOn ℂ (discExtend f) (ball (0 : ℂ) 1)}
  algebraMap_mem' c := by
    apply (differentiableOn_const c).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]
  add_mem' hf hg := by
    apply (hf.add hg).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]
  mul_mem' hf hg := by
    apply (hf.mul hg).congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]

abbrev DiscAlgebra := ↥discSubalgebra

instance discNormOneClass : NormOneClass DiscAlgebra where
  norm_one := show ‖(1 : C(DiscClosed, ℂ))‖ = 1 from norm_one

theorem disc_diffContOnCl (f : DiscAlgebra) :
    DiffContOnCl ℂ (discExtend f.val) (ball (0 : ℂ) 1) :=
  DiffContOnCl.mk_ball f.property (discExtend_continuousOn f.val)

theorem discSubalgebra_isClosed : IsClosed (discSubalgebra : Set C(DiscClosed, ℂ)) := by
  apply IsSeqClosed.isClosed
  intro F f hF ht
  have hu : TendstoUniformlyOn (fun n => discExtend (F n)) (discExtend f)
      atTop (ball (0 : ℂ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with n hn z hz
    simpa [discExtend, ball_subset_closedBall hz, dist_comm] using
      (ContinuousMap.dist_apply_le_dist (f := F n) (g := f)
        ⟨z, ball_subset_closedBall hz⟩).trans_lt hn
  exact hu.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hF) isOpen_ball

instance discCompleteSpace : CompleteSpace DiscAlgebra :=
  discSubalgebra_isClosed.isComplete.completeSpace_coe

def discEval (z : DiscClosed) : DiscAlgebra →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ z).comp discSubalgebra.val

@[simp] theorem discEval_apply (z : DiscClosed) (f : DiscAlgebra) :
    discEval z f = f.val z := rfl

/-- Reciprocal of a nowhere-zero disc-algebra function, with its full holomorphy proof. -/
def discReciprocal (f : DiscAlgebra) (hf : ∀ z : DiscClosed, f.val z ≠ 0) :
    DiscAlgebra := by
  let g : C(DiscClosed, ℂ) := ⟨fun z => (f.val z)⁻¹, f.val.continuous.inv₀ hf⟩
  refine ⟨g, ?_⟩
  have hn : ∀ z ∈ ball (0 : ℂ) 1, discExtend f.val z ≠ 0 := by
    intro z hz
    simpa [discExtend, ball_subset_closedBall hz] using hf ⟨z, ball_subset_closedBall hz⟩
  apply (f.property.inv hn).congr
  intro z hz
  simp [discExtend, ball_subset_closedBall hz, g]

@[simp] theorem discReciprocal_apply (f : DiscAlgebra)
    (hf : ∀ z : DiscClosed, f.val z ≠ 0) (z : DiscClosed) :
    (discReciprocal f hf).val z = (f.val z)⁻¹ := rfl

theorem disc_isUnit_iff (f : DiscAlgebra) :
    IsUnit f ↔ ∀ z : DiscClosed, f.val z ≠ 0 := by
  constructor
  · intro hf z
    exact isUnit_iff_ne_zero.mp (hf.map (discEval z))
  · intro hf
    refine ⟨⟨f, discReciprocal f hf, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact mul_inv_cancel₀ (hf z)
    · apply Subtype.ext
      apply ContinuousMap.ext
      intro z
      exact inv_mul_cancel₀ (hf z)

theorem disc_spectrum_eq_range (f : DiscAlgebra) :
    spectrum ℂ f = Set.range f.val := by
  ext c
  simp only [spectrum.mem_iff, disc_isUnit_iff, not_forall, Classical.not_not,
    Set.mem_range]
  change (∃ z : DiscClosed, c - f.val z = 0) ↔ ∃ z : DiscClosed, f.val z = c
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, sub_eq_zero.mpr hz.symm⟩

def discCoordinate : DiscAlgebra :=
  ⟨⟨Subtype.val, continuous_subtype_val⟩, by
    apply differentiableOn_id.congr
    intro z hz
    simp [discExtend, ball_subset_closedBall hz]⟩

@[simp] theorem discCoordinate_apply (z : DiscClosed) :
    discCoordinate.val z = (z : ℂ) := rfl

/-- The coordinate function's spectrum in the disc algebra is the closed unit disc. -/
theorem discCoordinate_spectrum :
    spectrum ℂ discCoordinate = closedBall (0 : ℂ) 1 := by
  rw [disc_spectrum_eq_range]
  exact Subtype.range_coe

def discBoundaryInclusion : C(DiscCircle, DiscClosed) :=
  ⟨fun z => ⟨z.val, sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def discBoundary : DiscAlgebra →ₐ[ℂ] C(DiscCircle, ℂ) where
  toFun f := f.val.comp discBoundaryInclusion
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem discBoundary_apply (f : DiscAlgebra) (z : DiscCircle) :
    discBoundary f z = f.val ⟨z.val, sphere_subset_closedBall z.property⟩ := rfl

theorem discBoundary_norm (f : DiscAlgebra) : ‖discBoundary f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro z
    exact f.val.norm_coe_le_norm _
  · change ‖f.val‖ ≤ ‖discBoundary f‖
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (disc_diffContOnCl f) (C := ‖discBoundary f‖)
    have hz : (z : ℂ) ∈ closure (ball (0 : ℂ) 1) := by
      simpa only [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] using z.property
    rw [← discExtend_apply f.val z]
    apply hmax _ hz
    intro w hw
    rw [frontier_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)] at hw
    simpa [discExtend, sphere_subset_closedBall hw] using
      (discBoundary f).norm_coe_le_norm ⟨w, hw⟩

theorem discBoundary_isometry : Isometry discBoundary := by
  exact AddMonoidHomClass.isometry_of_norm discBoundary discBoundary_norm

def discBoundarySubalgebra : Subalgebra ℂ C(DiscCircle, ℂ) := discBoundary.range

instance discBoundaryNormOneClass : NormOneClass discBoundarySubalgebra where
  norm_one := show ‖(1 : C(DiscCircle, ℂ))‖ = 1 from norm_one

theorem discBoundarySubalgebra_isClosed :
    IsClosed (discBoundarySubalgebra : Set C(DiscCircle, ℂ)) :=
  discBoundary_isometry.isClosedEmbedding.isClosed_range

instance discBoundaryCompleteSpace : CompleteSpace discBoundarySubalgebra :=
  discBoundarySubalgebra_isClosed.isComplete.completeSpace_coe

def discBoundaryEquiv : DiscAlgebra ≃ₐ[ℂ] discBoundarySubalgebra :=
  AlgEquiv.ofInjective discBoundary discBoundary_isometry.injective

def discBoundaryCoordinate : discBoundarySubalgebra := discBoundaryEquiv discCoordinate

/-- Passing to boundary values preserves the disc-algebra spectrum. -/
theorem discBoundaryCoordinate_subalgebra_spectrum :
    spectrum ℂ discBoundaryCoordinate = closedBall (0 : ℂ) 1 := by
  rw [discBoundaryCoordinate, AlgEquiv.spectrum_eq, discCoordinate_spectrum]

/-- In the full circle-function algebra, the same coordinate has only the circle as spectrum. -/
theorem discBoundaryCoordinate_spectrum :
    spectrum ℂ (discBoundary discCoordinate) = sphere (0 : ℂ) 1 := by
  rw [ContinuousMap.spectrum_eq_range]
  exact Subtype.range_coe

/-- The printed example exhibits genuinely different spectra in the two algebras. -/
theorem discCoordinate_spectra_differ :
    spectrum ℂ discBoundaryCoordinate ≠ spectrum ℂ (discBoundary discCoordinate) := by
  rw [discBoundaryCoordinate_subalgebra_spectrum, discBoundaryCoordinate_spectrum]
  intro h
  have hz : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  rw [h] at hz
  simpa using hz

theorem disc_radius_eq_one_of_spectrum {A : Type*} [Ring A] [Algebra ℂ A] (a : A)
    (h1 : (1 : ℂ) ∈ spectrum ℂ a)
    (hb : ∀ z ∈ spectrum ℂ a, ‖z‖ ≤ 1) : spectralRadius ℂ a = 1 := by
  rw [spectralRadius_eq_of_unital]
  apply le_antisymm
  · apply iSup₂_le
    intro z hz
    exact_mod_cast hb z hz
  · simpa using le_iSup₂ (f := fun z (_ : z ∈ spectrum ℂ a) => (‖z‖₊ : ℝ≥0∞)) 1 h1

theorem discBoundaryCoordinate_subalgebra_radius :
    spectralRadius ℂ discBoundaryCoordinate = 1 := by
  apply disc_radius_eq_one_of_spectrum
  · simp [discBoundaryCoordinate_subalgebra_spectrum]
  · intro z hz
    simpa only [discBoundaryCoordinate_subalgebra_spectrum, mem_closedBall_zero_iff] using hz

theorem discBoundaryCoordinate_radius :
    spectralRadius ℂ (discBoundary discCoordinate) = 1 := by
  apply disc_radius_eq_one_of_spectrum
  · simp [discBoundaryCoordinate_spectrum]
  · intro z hz
    exact le_of_eq (by simpa only [discBoundaryCoordinate_spectrum, mem_sphere_zero_iff_norm] using hz)

/-- Although the spectra in Rudin 18.11 differ, both spectral radii are one. -/
theorem discCoordinate_spectralRadii_equal :
    spectralRadius ℂ discBoundaryCoordinate =
      spectralRadius ℂ (discBoundary discCoordinate) :=
  discBoundaryCoordinate_subalgebra_radius.trans discBoundaryCoordinate_radius.symm

/-- A polynomial in the disc coordinate, represented by finitely many coefficients. -/
def discPolynomial (c : ℕ → ℂ) (n : ℕ) : DiscAlgebra :=
  ∑ k ∈ Finset.range n, c k • discCoordinate ^ k

@[simp] theorem discPolynomial_apply (c : ℕ → ℂ) (n : ℕ) (z : DiscClosed) :
    (discPolynomial c n).val z = ∑ k ∈ Finset.range n, c k * (z : ℂ) ^ k := by
  simp [discPolynomial]

theorem discPolynomial_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (r : ℝ) (n : ℕ) (z : DiscClosed) :
    (discPolynomial (fun k => (r : ℂ) ^ k * p.coeff k) n).val z =
      p.partialSum n ((r : ℂ) * z) := by
  rw [discPolynomial_apply, FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  simp only [smul_eq_mul, mul_pow]
  ring

def discPowerSeries (f : DiscAlgebra) : FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries (discExtend f.val) 0 1

theorem disc_hasPowerSeries (f : DiscAlgebra) :
    HasFPowerSeriesOnBall (discExtend f.val) (discPowerSeries f) 0 (1 : ℝ≥0∞) :=
  (disc_diffContOnCl f).hasFPowerSeriesOnBall (R := (1 : ℝ≥0)) (by norm_num)

theorem disc_powerSeries_tendstoUniformly (f : DiscAlgebra) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < 1) :
    TendstoUniformlyOn (fun n z => (discPowerSeries f).partialSum n z)
      (fun z => discExtend f.val (0 + z)) atTop (ball (0 : ℂ) s) :=
  (disc_hasPowerSeries f).tendstoUniformlyOn (r' := s) hs

set_option maxHeartbeats 1000000 in
/-- Polynomial density in the disc algebra, including boundary-continuous functions. -/
theorem disc_polynomial_approx (f : DiscAlgebra) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ → ℂ, ∃ n : ℕ, ‖f - discPolynomial c n‖ < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, huc⟩ := f.val.uniform_continuity (ε / 3) hthird
  obtain ⟨r, hr, hr1⟩ := exists_between
    (max_lt (sub_lt_self (1 : ℝ) hδ) zero_lt_one)
  have hr0 : 0 < r := (le_max_right (1 - δ) 0).trans_lt hr
  have hnear : 1 - r < δ := by
    have := (le_max_left (1 - δ) 0).trans_lt hr
    linarith
  obtain ⟨s, hrs, hs1⟩ := exists_between hr1
  have hs0 : 0 ≤ s := le_of_lt (hr0.trans hrs)
  let s' : ℝ≥0 := ⟨s, hs0⟩
  let p : FormalMultilinearSeries ℂ ℂ ℂ := discPowerSeries f
  have hs' : (s' : ℝ≥0∞) < (1 : ℝ≥0∞) := by exact_mod_cast hs1
  have hu := disc_powerSeries_tendstoUniformly f (s := s') hs'
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 3) hthird).exists
  let c : ℕ → ℂ := fun k => (r : ℂ) ^ k * p.coeff k
  refine ⟨c, n, lt_of_le_of_lt ?_ (by linarith : 2 * (ε / 3) < ε)⟩
  change ‖(f - discPolynomial c n).val‖ ≤ 2 * (ε / 3)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro z
  have hz : ‖(z : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall_zero_iff] using z.property
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr0]
  have hrz : ‖(r : ℂ) * z‖ ≤ r := by
    rw [norm_mul, hrnorm]
    exact (mul_le_mul_of_nonneg_left hz hr0.le).trans_eq (mul_one r)
  have hrzclosed : (r : ℂ) * z ∈ closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (hrz.trans hr1.le)
  let rz : DiscClosed := ⟨(r : ℂ) * z, hrzclosed⟩
  have hdist : dist rz z < δ := by
    change dist ((r : ℂ) * (z : ℂ)) (z : ℂ) < δ
    rw [dist_eq_norm, ← sub_one_mul, norm_mul]
    have hrminus : ‖(r : ℂ) - 1‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real]
      exact abs_of_nonpos (sub_nonpos.mpr hr1.le) |>.trans (by ring)
    rw [hrminus]
    exact ((mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hr1.le)).trans_eq
      (mul_one (1 - r))).trans_lt hnear
  have hclose : dist (f.val z) (f.val rz) < ε / 3 := by
    simpa only [dist_comm] using huc hdist
  have hseries := hn ((r : ℂ) * z) (mem_ball_zero_iff.mpr (hrz.trans_lt hrs))
  have happrox : dist (f.val rz) ((discPolynomial c n).val z) < ε / 3 := by
    have hpoly : (discPolynomial c n).val z = p.partialSum n ((r : ℂ) * z) :=
      discPolynomial_partialSum p r n z
    rw [hpoly]
    change dist (discExtend f.val (0 + (r : ℂ) * z))
      (p.partialSum n ((r : ℂ) * z)) < ε / 3 at hseries
    rw [zero_add] at hseries
    have hext : discExtend f.val ((r : ℂ) * z) = f.val rz := discExtend_apply f.val rz
    rw [hext] at hseries
    exact hseries
  have htri := (dist_triangle (f.val z) (f.val rz) ((discPolynomial c n).val z)).trans
    (add_le_add hclose.le happrox.le)
  change ‖f.val z - (discPolynomial c n).val z‖ ≤ 2 * (ε / 3)
  simpa only [dist_eq_norm, two_mul] using htri

set_option maxHeartbeats 1000000 in
/-- Every complex algebra character of the disc algebra is evaluation at one closed-disc point. -/
theorem disc_character_evaluation (h : DiscAlgebra →ₐ[ℂ] ℂ) :
    ∃ z : DiscClosed, ∀ f : DiscAlgebra, h f = f.val z := by
  have hc : h discCoordinate ∈ closedBall (0 : ℂ) 1 := by
    simpa only [discCoordinate_spectrum] using AlgHom.apply_mem_spectrum h discCoordinate
  let z : DiscClosed := ⟨h discCoordinate, hc⟩
  refine ⟨z, fun f => ?_⟩
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨c, n, hn⟩ := disc_polynomial_approx f (half_pos hε)
  let q := discPolynomial c n
  have hnq : ‖f - q‖ < ε / 2 := hn
  have hq : h q = q.val z := by
    simp [q, discPolynomial, z]
  have hleft : dist (h f) (h q) ≤ ‖f - q‖ := by
    simpa only [dist_eq_norm, map_sub] using AlgHom.norm_apply_le_self h (f - q)
  have hright : dist (q.val z) (f.val z) ≤ ‖f - q‖ := by
    rw [dist_eq_norm, norm_sub_rev]
    exact (f - q).val.norm_coe_le_norm z
  calc
    dist (h f) (f.val z) ≤ dist (h f) (h q) + dist (h q) (f.val z) :=
      dist_triangle _ _ _
    _ ≤ ‖f - q‖ + ‖f - q‖ := add_le_add hleft (by simpa only [hq] using hright)
    _ ≤ ε := (add_le_add hnq.le hnq.le).trans_eq (add_halves ε)

/-- The maximal-ideal quotient supplies a complex character vanishing on that ideal. -/
theorem disc_maximal_character {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (I : Ideal A) [I.IsMaximal] :
    ∃ h : A →ₐ[ℂ] ℂ, ∀ a ∈ I, h a = 0 := by
  let h : A →ₐ[ℂ] ℂ :=
    ((NormedRing.algEquivComplexOfComplete
      (letI := Ideal.Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm.toAlgHom).comp
        (Ideal.Quotient.mkₐ ℂ I)
  refine ⟨h, fun a ha => ?_⟩
  dsimp only [h]
  rw [AlgHom.comp_apply]
  have hmk : (Ideal.Quotient.mkₐ ℂ I) a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hmk, map_zero]

theorem discEval_surjective (z : DiscClosed) : Function.Surjective (discEval z) := by
  intro c
  exact ⟨algebraMap ℂ DiscAlgebra c, (discEval z).commutes c⟩

theorem discEval_kernel_isMaximal (z : DiscClosed) :
    (RingHom.ker (discEval z)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (discEval z) (discEval_surjective z)

/-- The note following 18.18: the maximal ideals are exactly point-evaluation kernels. -/
theorem disc_maximal_iff_evaluation_kernel (I : Ideal DiscAlgebra) :
    I.IsMaximal ↔ ∃ z : DiscClosed, I = RingHom.ker (discEval z) := by
  constructor
  · intro hI
    letI := hI
    obtain ⟨h, hh⟩ := disc_maximal_character I
    obtain ⟨z, hz⟩ := disc_character_evaluation h
    refine ⟨z, hI.eq_of_le (RingHom.ker_ne_top (discEval z)) ?_⟩
    intro f hf
    change f.val z = 0
    rw [← hz f]
    exact hh f hf
  · rintro ⟨z, rfl⟩
    exact discEval_kernel_isMaximal z

/-- Rudin 18.18: a finite family with no common closed-disc zero has a Bezout identity. -/
theorem disc_bezout {ι : Type*} [Fintype ι] (f : ι → DiscAlgebra)
    (hf : ∀ z : DiscClosed, ∃ i, (f i).val z ≠ 0) :
    ∃ g : ι → DiscAlgebra, ∑ i, f i * g i = 1 := by
  have htop : Ideal.span (Set.range f) = ⊤ := by
    by_contra hproper
    obtain ⟨I, hI, hle⟩ := (Ideal.span (Set.range f)).exists_le_maximal hproper
    letI := hI
    obtain ⟨h, hh⟩ := disc_maximal_character I
    obtain ⟨z, hz⟩ := disc_character_evaluation h
    obtain ⟨i, hi⟩ := hf z
    apply hi
    rw [← hz (f i)]
    have hmem : f i ∈ I := hle (Ideal.subset_span ⟨i, rfl⟩)
    exact hh _ hmem
  have hone : (1 : DiscAlgebra) ∈ Ideal.span (Set.range f) := by rw [htop]; trivial
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  exact ⟨g, by simpa only [mul_comm] using hg⟩

/-- The printed positive-sum hypothesis and pointwise conclusion of Rudin 18.18. -/
theorem disc_bezout_positive {n : ℕ} (f : Fin n → DiscAlgebra)
    (hf : ∀ z : DiscClosed, 0 < ∑ i, ‖(f i).val z‖) :
    ∃ g : Fin n → DiscAlgebra, ∀ z : DiscClosed,
      ∑ i, (f i).val z * (g i).val z = 1 := by
  have hnonzero : ∀ z : DiscClosed, ∃ i, (f i).val z ≠ 0 := by
    intro z
    by_contra h
    push_neg at h
    have hsum : ∑ i, ‖(f i).val z‖ = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [h i, norm_zero])
    have := hf z
    rw [hsum] at this
    exact (lt_irrefl 0) this
  obtain ⟨g, hg⟩ := disc_bezout f hnonzero
  refine ⟨g, fun z => ?_⟩
  have := congrArg (discEval z) hg
  simpa using this

theorem discBoundary_eq_closure_adjoin :
    discBoundarySubalgebra =
      (Algebra.adjoin ℂ {discBoundary discCoordinate}).topologicalClosure := by
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    change discBoundary f ∈ closure
      (Algebra.adjoin ℂ {discBoundary discCoordinate} : Set C(DiscCircle, ℂ))
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c, n, hn⟩ := disc_polynomial_approx f hε
    refine ⟨discBoundary (discPolynomial c n), ?_, ?_⟩
    · let B := Algebra.adjoin ℂ {discBoundary discCoordinate}
      have hx : discBoundary discCoordinate ∈ B := Algebra.self_mem_adjoin_singleton _ _
      have hsum : ∑ k ∈ Finset.range n, c k • (discBoundary discCoordinate) ^ k ∈ B :=
        B.sum_mem (fun k _ => B.smul_mem (B.pow_mem hx k) (c k))
      simpa [discPolynomial] using hsum
    · simpa only [dist_eq_norm, ← map_sub, discBoundary_norm] using hn
  · apply Subalgebra.topologicalClosure_minimal _ discBoundarySubalgebra_isClosed
    apply Algebra.adjoin_le
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact ⟨discCoordinate, rfl⟩

instance discAnglePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The standard angular parameterization, with values in the printed unit circle. -/
def discAngleHomeomorph : AddCircle (2 * Real.pi) ≃ₜ DiscCircle :=
  AddCircle.homeomorphCircle (by positivity)

def discAngleTransport : C(DiscCircle, ℂ) →ₐ[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ (discAngleHomeomorph : C(AddCircle (2 * Real.pi), DiscCircle))

theorem discAngleTransport_norm (f : C(DiscCircle, ℂ)) :
    ‖discAngleTransport f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro t
    exact f.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro z
    obtain ⟨t, rfl⟩ := discAngleHomeomorph.surjective z
    exact (discAngleTransport f).norm_coe_le_norm t

def discAngleBoundary : DiscAlgebra →ₐ[ℂ] C(AddCircle (2 * Real.pi), ℂ) :=
  discAngleTransport.comp discBoundary

theorem discAngleBoundary_norm (f : DiscAlgebra) : ‖discAngleBoundary f‖ = ‖f‖ :=
  (discAngleTransport_norm (discBoundary f)).trans (discBoundary_norm f)

theorem discAngleBoundary_isometry : Isometry discAngleBoundary :=
  AddMonoidHomClass.isometry_of_norm discAngleBoundary discAngleBoundary_norm

theorem discAngleBoundary_coordinate :
    discAngleBoundary discCoordinate = @fourier (2 * Real.pi) 1 := by
  apply ContinuousMap.ext
  intro t
  change ((AddCircle.homeomorphCircle (by positivity) t : Circle) : ℂ) = fourier 1 t
  rw [AddCircle.homeomorphCircle_apply, fourier_one]

def discAngleSubalgebra : Subalgebra ℂ C(AddCircle (2 * Real.pi), ℂ) :=
  discAngleBoundary.range

theorem discAngleSubalgebra_isClosed :
    IsClosed (discAngleSubalgebra : Set C(AddCircle (2 * Real.pi), ℂ)) :=
  discAngleBoundary_isometry.isClosedEmbedding.isClosed_range

theorem discAngleBoundary_power (n : ℕ) :
    discAngleBoundary (discCoordinate ^ n) = @fourier (2 * Real.pi) (n : ℤ) := by
  induction n with
  | zero => ext t; simp [fourier_zero]
  | succ n ih =>
    rw [pow_succ, map_mul, ih, discAngleBoundary_coordinate]
    ext t
    simp only [ContinuousMap.mul_apply, Nat.cast_add, Nat.cast_one]
    exact fourier_add.symm

/-- Bridge from disc-algebra boundary values to the closed span of nonnegative Fourier modes. -/
theorem discAngleSubalgebra_eq_positive_closure :
    discAngleSubalgebra.toSubmodule =
      (Submodule.span ℂ (Set.range
        (fun n : ℕ => @fourier (2 * Real.pi) (n : ℤ)))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range
    (fun n : ℕ => @fourier (2 * Real.pi) (n : ℤ)))
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    change discAngleBoundary f ∈ closure (S : Set C(AddCircle (2 * Real.pi), ℂ))
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c, n, hn⟩ := disc_polynomial_approx f hε
    refine ⟨discAngleBoundary (discPolynomial c n), ?_, ?_⟩
    · have hsum : ∑ k ∈ Finset.range n, c k • @fourier (2 * Real.pi) (k : ℤ) ∈ S := by
        apply S.sum_mem
        intro k hk
        exact S.smul_mem (c k) (Submodule.subset_span ⟨k, rfl⟩)
      change discAngleBoundary (discPolynomial c n) ∈ S
      simpa only [discPolynomial, map_sum, map_smul, discAngleBoundary_power] using hsum
    · simpa only [dist_eq_norm, ← map_sub, discAngleBoundary_norm] using hn
  · apply Submodule.topologicalClosure_minimal S _ discAngleSubalgebra_isClosed
    apply Submodule.span_le.mpr
    rintro y ⟨n, rfl⟩
    exact ⟨discCoordinate ^ n, discAngleBoundary_power n⟩

#print axioms discSubalgebra_isClosed
#print axioms disc_isUnit_iff
#print axioms disc_spectrum_eq_range
#print axioms discCoordinate_spectrum
#print axioms discBoundary_norm
#print axioms discBoundarySubalgebra_isClosed
#print axioms discBoundaryCompleteSpace
#print axioms discBoundaryCoordinate_subalgebra_spectrum
#print axioms discBoundaryCoordinate_spectrum
#print axioms discCoordinate_spectra_differ
#print axioms discCoordinate_spectralRadii_equal
#print axioms disc_polynomial_approx
#print axioms disc_character_evaluation
#print axioms disc_maximal_iff_evaluation_kernel
#print axioms disc_bezout
#print axioms disc_bezout_positive
#print axioms discBoundary_eq_closure_adjoin
#print axioms discAngleBoundary_coordinate
#print axioms discAngleSubalgebra_eq_positive_closure

end RudinRCA.Chapter18
