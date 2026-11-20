import Humphreys.Ch7.ChevalleyBasis25_2
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.Derivation.IntegralExp
import TauCeti.Algebra.Lie.InnerAutomorphism
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.Algebra.Lie.Weights.Root.IntegralBasis
import TauCeti.Algebra.Lie.Weights.Root.KostantStability
import TauCeti.LinearAlgebra.TensorProduct.Basis

open LieAlgebra LieAlgebra.IsKilling LieModule Polynomial RootPairing TauCeti
open scoped TensorProduct

universe u v w

namespace Humphreys25_5

section ChevalleyGroup

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Humphreys §25.4 (p. 149): The Chevalley algebra `L(F) = F ⊗[ℤ] L(ℤ)`.**
Defined uniformly for any commutative ring (in particular any field) `F` of arbitrary
characteristic; `Mathlib.Algebra.Lie.BaseChange` equips `ChevalleyAlgebra hx F` with its
canonical `LieRing` and `LieAlgebra F` structures (`⁅a ⊗ₜ u, b ⊗ₜ v⁆ = (a * b) ⊗ₜ ⁅u, v⁆`). -/
abbrev ChevalleyAlgebra
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (F : Type w) [CommRing F] : Type (max v w) :=
  F ⊗[ℤ] hx.chevalleyLieLattice

/-- **Humphreys §25.4 (p. 149): The Chevalley `F`-basis `{1 ⊗ x_α, 1 ⊗ h_i}` of `L(F)`.** -/
noncomputable def chevalleyAlgebraBasis
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (F : Type w) [CommRing F] :
    Module.Basis (H.root ⊕ ↥b.support) F (ChevalleyAlgebra hx F) :=
  (hx.rootSimpleCorootBasis b).baseChange F

/-- **Humphreys §25.4 (p. 149): Dimension of the Chevalley algebra `L(F)` over any field `F`.** -/
theorem finrank_chevalleyAlgebra
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (F : Type w) [Field F] :
    Module.finrank F (ChevalleyAlgebra hx F) = Module.finrank K L := by
  obtain ⟨b⟩ := (rootSystem H).nonempty_base
  rw [Module.finrank_eq_card_basis (chevalleyAlgebraBasis hx b F)]
  exact TauCeti.card_root_sum_support_eq_finrank H b

/-- **Humphreys Proposition 25.5 (p. 149): Integral divided-power operator `(ad x_α)^m / m!`
restricted to `L(ℤ)`.** -/
noncomputable def adDividedPowerEnd
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : Weight K H L) (m : ℕ) :
    Module.End ℤ hx.chevalleyLieLattice where
  toFun v := ⟨(m.factorial : K)⁻¹ • ((LieAlgebra.ad K L (x α)) ^ m) (v : L),
    hx.inv_factorial_smul_ad_pow_mem_chevalleyLieLattice α m v.2⟩
  map_add' u v := Subtype.ext (by simp [smul_add])
  map_smul' z v := Subtype.ext (by simp only [AddSubgroupClass.coe_zsmul, map_zsmul]; exact smul_comm _ _ _)

/-- **Humphreys Proposition 25.5 (p. 149, verbatim):**
For every root `α ∈ Φ = H.root`, `m ∈ ℕ` (`= ℤ⁺`), and `y ∈ L(ℤ)`,
`((ad x_α)^m / m!)(y) ∈ L(ℤ)` and agrees with `adDividedPowerEnd hx α m`. -/
theorem adDividedPower_mem_chevalleyLieLattice
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : H.root) (m : ℕ) {y : L} (hy : y ∈ hx.chevalleyLieLattice) :
    (m.factorial : K)⁻¹ • ((LieAlgebra.ad K L (x (α : Weight K H L))) ^ m) y ∈
        hx.chevalleyLieLattice ∧
      ((adDividedPowerEnd hx (α : Weight K H L) m ⟨y, hy⟩ : hx.chevalleyLieLattice) : L) =
        (m.factorial : K)⁻¹ • ((LieAlgebra.ad K L (x (α : Weight K H L))) ^ m) y := by
  exact ⟨hx.inv_factorial_smul_ad_pow_mem_chevalleyLieLattice (α : Weight K H L) m hy, rfl⟩

/-- **Humphreys §25.5 (p. 150): Specialized root-exponential endomorphism
`exp ad(t x_α) = ∑_{m=0}^∞ t^m ((ad x_α)^m / m!)` on `L(F)`.**
Truncated at `nilpotencyClass (ad K L (x α))`, above which every divided power vanishes. -/
noncomputable def expAdRootEnd
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : Weight K H L) (F : Type w) [CommRing F] (t : F) :
    Module.End F (ChevalleyAlgebra hx F) :=
  ∑ m ∈ Finset.range (nilpotencyClass (LieAlgebra.ad K L (x α))),
    t ^ m • (adDividedPowerEnd hx α m).baseChange F

/-- **Humphreys §25.5 (pp. 150–151): Additive one-parameter group law, invertibility, and
Lie-bracket preservation of `exp ad(t x_α)` on `L(F)`.** -/
theorem expAdRootEnd_zero_add_neg_and_map_lie
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : H.root) (F : Type w) [CommRing F] :
    expAdRootEnd hx (α : Weight K H L) F 0 = 1 ∧
      (∀ s t : F,
        expAdRootEnd hx (α : Weight K H L) F (s + t) =
          expAdRootEnd hx (α : Weight K H L) F s *
            expAdRootEnd hx (α : Weight K H L) F t) ∧
      (∀ t : F,
        expAdRootEnd hx (α : Weight K H L) F t *
            expAdRootEnd hx (α : Weight K H L) F (-t) = 1 ∧
          expAdRootEnd hx (α : Weight K H L) F (-t) *
            expAdRootEnd hx (α : Weight K H L) F t = 1) ∧
      ∀ (t : F) (u v : ChevalleyAlgebra hx F),
        expAdRootEnd hx (α : Weight K H L) F t ⁅u, v⁆ =
          ⁅expAdRootEnd hx (α : Weight K H L) F t u,
            expAdRootEnd hx (α : Weight K H L) F t v⁆ := by
  let _ : LieAlgebra ℚ L := TauCeti.ratLieAlgebra K L
  let D : LieDerivation ℚ L L := LieDerivation.ad ℚ L (x (α : Weight K H L))
  have hD_eq : D.toLinearMap = LieAlgebra.ad ℚ L (x (α : Weight K H L)) :=
    LieDerivation.coe_ad_apply_eq_ad_apply (x (α : Weight K H L))
  have hpow_apply : ∀ (n : ℕ) (y : L),
      (D.toLinearMap ^ n) y = ((LieAlgebra.ad K L (x (α : Weight K H L))) ^ n) y := by
    intro n y
    rw [hD_eq]
    exact TauCeti.ad_pow_apply_eq_ad_pow_apply ℚ K (x (α : Weight K H L)) y n
  have hdiv_apply : ∀ (n : ℕ) (y : L),
      TauCeti.Associative.dividedPower n D.toLinearMap • y =
        (n.factorial : K)⁻¹ • ((LieAlgebra.ad K L (x (α : Weight K H L))) ^ n) y := by
    intro n y
    rw [TauCeti.Associative.dividedPower_def]
    change (n.factorial : ℚ)⁻¹ • (D.toLinearMap ^ n) y = _
    rw [hpow_apply n y]
    have hnfK : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have hnfQ : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    apply smul_right_injective L hnfK
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ hnfK, one_smul, Nat.cast_smul_eq_nsmul K,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hnfQ, one_smul]
  have hM : ∀ n, ∀ v ∈ hx.chevalleyLieLattice,
      TauCeti.Associative.dividedPower n D.toLinearMap • v ∈ hx.chevalleyLieLattice := by
    intro n v hv
    rw [hdiv_apply n v]
    exact hx.inv_factorial_smul_ad_pow_mem_chevalleyLieLattice (α : Weight K H L) n hv
  have hdiv_eq : ∀ m, adDividedPowerEnd hx (α : Weight K H L) m =
      TauCeti.integralDividedPower D.toLinearMap hx.chevalleyLieLattice m (hM m) := by
    intro m
    ext v
    exact (hdiv_apply m v).symm
  have hnilK : IsNilpotent (LieAlgebra.ad K L (x (α : Weight K H L))) :=
    hx.toIsSl2System.isNilpotent_ad_rootVector (α : Weight K H L)
  have hpow_iff : ∀ k : ℕ,
      D.toLinearMap ^ k = 0 ↔ (LieAlgebra.ad K L (x (α : Weight K H L))) ^ k = 0 := by
    intro k
    simp only [LinearMap.ext_iff, LinearMap.zero_apply, hpow_apply]
  have hD : IsNilpotent D.toLinearMap := by
    obtain ⟨k, hk⟩ := hnilK
    exact ⟨k, (hpow_iff k).2 hk⟩
  have hnc : nilpotencyClass (LieAlgebra.ad K L (x (α : Weight K H L))) =
      nilpotencyClass D.toLinearMap := by
    simp only [nilpotencyClass, hpow_iff]
  have hexp : ∀ t : F,
      expAdRootEnd hx (α : Weight K H L) F t =
        TauCeti.baseChangeExp D.toLinearMap hx.chevalleyLieLattice hM t := by
    intro t
    unfold expAdRootEnd TauCeti.baseChangeExp
    rw [hnc]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hdiv_eq m]
  have hzero : expAdRootEnd hx (α : Weight K H L) F 0 = 1 := by
    rw [hexp, TauCeti.baseChangeExp_zero D.toLinearMap hx.chevalleyLieLattice hM hD]
  have hadd : ∀ s t : F,
      expAdRootEnd hx (α : Weight K H L) F (s + t) =
        expAdRootEnd hx (α : Weight K H L) F s *
          expAdRootEnd hx (α : Weight K H L) F t := by
    intro s t
    rw [hexp, hexp, hexp]
    exact TauCeti.baseChangeExp_add D.toLinearMap hx.chevalleyLieLattice hM hD s t
  refine ⟨hzero, hadd, fun t ↦ ⟨?_, ?_⟩, fun t u v ↦ ?_⟩
  · rw [← hadd, add_neg_cancel, hzero]
  · rw [← hadd, neg_add_cancel, hzero]
  · rw [hexp]
    exact TauCeti.baseChangeExp_lie D hx.chevalleyLieLattice hM t u v

open Classical in
/-- **Humphreys §25.5 (p. 150): Universal polynomial matrix `exp ad(T x_α)` over `ℤ[T]`**
relative to the Chevalley `ℤ`-basis `hx.rootSimpleCorootBasis b`. -/
noncomputable def expAdRootPolyMatrix
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (α : H.root) :
    Matrix (H.root ⊕ ↥b.support) (H.root ⊕ ↥b.support) (Polynomial ℤ) :=
  ∑ m ∈ Finset.range (nilpotencyClass (LieAlgebra.ad K L (x (α : Weight K H L)))),
    (Polynomial.X : Polynomial ℤ) ^ m •
      (LinearMap.toMatrix (hx.rootSimpleCorootBasis b) (hx.rootSimpleCorootBasis b)
        (adDividedPowerEnd hx (α : Weight K H L) m)).map Polynomial.C

open Classical in
/-- **Humphreys §25.5 (p. 150, verbatim): Matrix specialization `T ↦ t` from `ℤ[T]` to `F`
and determinant `1`.**
Relative to the Chevalley basis, `exp ad(T x_α)` has entries in `ℤ[T]` and determinant `1`,
and specializing `T ↦ t ∈ F` recovers the matrix of `expAdRootEnd hx α F t` with
determinant `1`. -/
theorem expAdRootEnd_toMatrix_eq_map_aeval_and_det_eq_one
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (α : H.root) (F : Type w) [CommRing F] (t : F) :
    (expAdRootPolyMatrix hx b α).det = 1 ∧
      LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
          (expAdRootEnd hx (α : Weight K H L) F t) =
        (expAdRootPolyMatrix hx b α).map (Polynomial.aeval t).toRingHom ∧
      (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
          (expAdRootEnd hx (α : Weight K H L) F t)).det = 1 := by
  have hspec₀ : ∀ (R : Type) [CommRing R] (r : R),
      LinearMap.toMatrix (chevalleyAlgebraBasis hx b R) (chevalleyAlgebraBasis hx b R)
          (expAdRootEnd hx (α : Weight K H L) R r) =
        (expAdRootPolyMatrix hx b α).map (Polynomial.aeval r).toRingHom := by
    intro R _ r
    unfold expAdRootEnd expAdRootPolyMatrix chevalleyAlgebraBasis
    rw [map_sum]
    ext i j
    simp only [Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul,
      Module.Basis.toMatrix_baseChange_baseChange, Matrix.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C]
  have hspecF : LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
      (expAdRootEnd hx (α : Weight K H L) F t) =
      (expAdRootPolyMatrix hx b α).map (Polynomial.aeval t).toRingHom := by
    unfold expAdRootEnd expAdRootPolyMatrix chevalleyAlgebraBasis
    rw [map_sum]
    ext i j
    simp only [Matrix.sum_apply, map_smul, Matrix.smul_apply, smul_eq_mul,
      Module.Basis.toMatrix_baseChange_baseChange, Matrix.map_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C]
  have hpoly_eq : LinearMap.toMatrix (chevalleyAlgebraBasis hx b (Polynomial ℤ))
      (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (expAdRootEnd hx (α : Weight K H L) (Polynomial ℤ) Polynomial.X) =
      expAdRootPolyMatrix hx b α := by
    unfold expAdRootEnd expAdRootPolyMatrix chevalleyAlgebraBasis
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [map_smul, Module.Basis.toMatrix_baseChange_baseChange]
    congr 1
  have hinv_mat : expAdRootPolyMatrix hx b α *
      LinearMap.toMatrix (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (expAdRootEnd hx (α : Weight K H L) (Polynomial ℤ) (-Polynomial.X)) = 1 := by
    rw [← hpoly_eq, ← LinearMap.toMatrix_mul,
      ((expAdRootEnd_zero_add_neg_and_map_lie hx α (Polynomial ℤ)).2.2.1 Polynomial.X).1,
      LinearMap.toMatrix_one]
  have hdet_mul : (expAdRootPolyMatrix hx b α).det *
      (LinearMap.toMatrix (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (expAdRootEnd hx (α : Weight K H L) (Polynomial ℤ) (-Polynomial.X))).det = 1 := by
    rw [← Matrix.det_mul, hinv_mat, Matrix.det_one]
  have hdet_ne : (expAdRootPolyMatrix hx b α).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet_mul
    exact zero_ne_one hdet_mul
  have hdet_inv_ne :
      (LinearMap.toMatrix (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (chevalleyAlgebraBasis hx b (Polynomial ℤ))
        (expAdRootEnd hx (α : Weight K H L) (Polynomial ℤ) (-Polynomial.X))).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet_mul
    exact zero_ne_one hdet_mul
  have hdeg_zero : (expAdRootPolyMatrix hx b α).det.natDegree = 0 := by
    have hdeg := congrArg Polynomial.natDegree hdet_mul
    rw [Polynomial.natDegree_mul hdet_ne hdet_inv_ne, Polynomial.natDegree_one] at hdeg
    exact Nat.eq_zero_of_add_eq_zero_right hdeg
  have hdet_const : (expAdRootPolyMatrix hx b α).det =
      Polynomial.C ((expAdRootPolyMatrix hx b α).det.eval 0) := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact Polynomial.eq_C_of_natDegree_eq_zero hdeg_zero
  have heval_zero : (expAdRootPolyMatrix hx b α).det.eval 0 = 1 := by
    have h0 := hspec₀ ℤ (0 : ℤ)
    rw [(expAdRootEnd_zero_add_neg_and_map_lie hx α ℤ).1, LinearMap.toMatrix_one] at h0
    have hdet0 := congrArg Matrix.det h0.symm
    rw [Matrix.det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet0
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hdet0
  have hdet_poly : (expAdRootPolyMatrix hx b α).det = 1 := by
    rw [hdet_const, heval_zero, map_one]
  refine ⟨hdet_poly, hspecF, ?_⟩
  rw [hspecF, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet_poly, map_one]

/-- **Humphreys §25.5 (`D25.5`, p. 150): Chevalley group (of adjoint type) `G(F)`.**
The group of invertible `F`-linear transformations of `L(F) = ChevalleyAlgebra hx F`
generated by all `exp ad(t x_α)` (`α ∈ Φ = H.root`, `t ∈ F`). -/
noncomputable def chevalleyGroupAdjoint
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (F : Type w) [CommRing F] :
    Subgroup (LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F)) :=
  Subgroup.closure
    {g : LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F) |
      ∃ (α : H.root) (t : F), g.val = expAdRootEnd hx (α : Weight K H L) F t}

open Classical in
/-- **Humphreys `D25.5` + Exercise 25.11 (pp. 150–151): Generation, Lie-algebra automorphism
action `G(F) ≤ Aut_F(L(F))`, and determinant-`1` matrix specialization over an arbitrary
field `F`.** -/
theorem chevalleyGroupAdjoint_generation_and_lieAut
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (F : Type w) [Field F] :
    (∀ (α : H.root) (t : F),
        ∃! g : LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F),
          g.val = expAdRootEnd hx (α : Weight K H L) F t ∧
            g ∈ chevalleyGroupAdjoint hx F) ∧
      (∀ G : Subgroup (LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F)),
        chevalleyGroupAdjoint hx F ≤ G ↔
          ∀ (α : H.root) (t : F)
            (g : LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F)),
            g.val = expAdRootEnd hx (α : Weight K H L) F t → g ∈ G) ∧
      (∀ g ∈ chevalleyGroupAdjoint hx F, ∀ u v : ChevalleyAlgebra hx F,
        g • ⁅u, v⁆ = ⁅g • u, g • v⁆) ∧
      ∀ (b : (rootSystem H).Base), ∀ g ∈ chevalleyGroupAdjoint hx F,
        (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
            g.val).det = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α t
    have hinv := (expAdRootEnd_zero_add_neg_and_map_lie hx α F).2.2.1 t
    let g : LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F) :=
      ⟨expAdRootEnd hx (α : Weight K H L) F t, expAdRootEnd hx (α : Weight K H L) F (-t),
        hinv.1, hinv.2⟩
    refine ⟨g, ⟨rfl, Subgroup.subset_closure ⟨α, t, rfl⟩⟩, ?_⟩
    rintro g' ⟨hg', _⟩
    exact Units.ext hg'
  · intro G
    rw [chevalleyGroupAdjoint, Subgroup.closure_le]
    refine ⟨fun hG α t g hg ↦ hG ⟨α, t, hg⟩, ?_⟩
    rintro hG g ⟨α, t, hg⟩
    exact hG α t g hg
  · intro g hg u v
    induction hg using Subgroup.closure_induction generalizing u v with
    | mem g h =>
      obtain ⟨α, t, hg⟩ := h
      change g.val ⁅u, v⁆ = ⁅g.val u, g.val v⁆
      rw [hg]
      exact (expAdRootEnd_zero_add_neg_and_map_lie hx α F).2.2.2 t u v
    | one => rfl
    | mul g h _ _ hg hh => rw [mul_smul, mul_smul, mul_smul, hh, hg]
    | inv g _ hg => rw [← smul_left_cancel_iff g, smul_inv_smul, hg, smul_inv_smul, smul_inv_smul]
  · intro b g hg
    induction hg using Subgroup.closure_induction with
    | mem g h =>
      obtain ⟨α, t, hg⟩ := h
      rw [hg]
      exact (expAdRootEnd_toMatrix_eq_map_aeval_and_det_eq_one hx b α F t).2.2
    | one =>
      change (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
        1).det = 1
      rw [LinearMap.toMatrix_one, Matrix.det_one]
    | mul g h _ _ hg hh =>
      rw [Units.val_mul, LinearMap.toMatrix_mul, Matrix.det_mul, hg, hh, mul_one]
    | inv g _ hg =>
      have hmul : (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
          g.val).det *
          (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
            g⁻¹.val).det = 1 := by
        rw [← Matrix.det_mul, ← LinearMap.toMatrix_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, LinearMap.toMatrix_one, Matrix.det_one]
      rw [hg, one_mul] at hmul
      exact hmul

/-- **Bundled Lie-algebra automorphism `g : ChevalleyAlgebra hx F ≃ₗ⁅F⁆ ChevalleyAlgebra hx F`
induced by any element `g` of the Chevalley group `G(F)`.** -/
noncomputable def chevalleyGroupAdjointLieEquiv
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {F : Type w} [Field F] (g : chevalleyGroupAdjoint hx F) :
    ChevalleyAlgebra hx F ≃ₗ⁅F⁆ ChevalleyAlgebra hx F :=
  { g.1.toLinearEquiv with
    map_lie' := (chevalleyGroupAdjoint_generation_and_lieAut hx F).2.2.1 g.1 g.2 _ _ }

open Classical in
/-- **Faithful matrix-group realization `G(F) →* SL(H.root ⊕ b.support, F)` (H p. 150)
relative to any Chevalley basis `b`.** -/
noncomputable def chevalleyGroupAdjointToSL
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (F : Type w) [Field F] :
    chevalleyGroupAdjoint hx F →*
      Matrix.SpecialLinearGroup (H.root ⊕ ↥b.support) F where
  toFun g := ⟨LinearMap.toMatrix (chevalleyAlgebraBasis hx b F) (chevalleyAlgebraBasis hx b F)
      g.1.val,
    (chevalleyGroupAdjoint_generation_and_lieAut hx F).2.2.2 b g.1 g.2⟩
  map_one' := Subtype.ext (LinearMap.toMatrix_one (chevalleyAlgebraBasis hx b F))
  map_mul' g₁ g₂ := Subtype.ext
    (LinearMap.toMatrix_mul (chevalleyAlgebraBasis hx b F) g₁.1.val g₂.1.val)

open Classical in
/-- **Injectivity of `chevalleyGroupAdjointToSL`:** `G(F)` embeds faithfully as a matrix
subgroup of `SL` in the Chevalley basis. -/
theorem chevalleyGroupAdjointToSL_injective
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) (F : Type w) [Field F] :
    Function.Injective (chevalleyGroupAdjointToSL hx b F) := by
  intro g₁ g₂ h
  apply Subtype.ext
  apply Units.ext
  exact (LinearMap.toMatrix (chevalleyAlgebraBasis hx b F)
    (chevalleyAlgebraBasis hx b F)).injective (congrArg Subtype.val h)

open Classical in
/-- **Unconditional existence of the Chevalley algebra `L(F)` and adjoint Chevalley group
`G(F)` (composing landed `ChevalleyBasis25_2.exists_isChevalleySystem` with `D25.5`):**
Every finite-dimensional split Killing Lie algebra `(L, H)` over a characteristic-zero field `K`
admits a Chevalley system `(ω, x, hx)` whose Chevalley group `chevalleyGroupAdjoint hx F` over
any target field `F` is generated by `expAdRootEnd`, acts by `F`-Lie-algebra automorphisms on
`ChevalleyAlgebra hx F`, and embeds faithfully into `SL` in every Chevalley basis. -/
theorem exists_chevalleyGroupAdjoint (F : Type w) [Field F] :
    ∃ (ω : L ≃ₗ⁅K⁆ L) (x : Weight K H L → L) (hx : TauCeti.IsChevalleySystem ω x),
      Module.finrank F (ChevalleyAlgebra hx F) = Module.finrank K L ∧
        (∀ (α : H.root) (t : F),
          ∃! g : LinearMap.GeneralLinearGroup F (ChevalleyAlgebra hx F),
            g.val = expAdRootEnd hx (α : Weight K H L) F t ∧
              g ∈ chevalleyGroupAdjoint hx F) ∧
        (∀ g ∈ chevalleyGroupAdjoint hx F, ∀ u v : ChevalleyAlgebra hx F,
          g • ⁅u, v⁆ = ⁅g • u, g • v⁆) ∧
        ∀ b : (rootSystem H).Base,
          Function.Injective (chevalleyGroupAdjointToSL hx b F) := by
  obtain ⟨ω, x, hx⟩ := Humphreys25_2.exists_isChevalleySystem (K := K) (L := L) (H := H)
  have hgen := chevalleyGroupAdjoint_generation_and_lieAut hx F
  exact ⟨ω, x, hx, finrank_chevalleyAlgebra hx F, hgen.1, hgen.2.2.1,
    fun b ↦ chevalleyGroupAdjointToSL_injective hx b F⟩

end ChevalleyGroup

end Humphreys25_5
