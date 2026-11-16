import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Algebra.Lie.Weights.Faithful
import TauCeti.Algebra.Lie.Weights.Root.CorootSpan
import TauCeti.Algebra.Lie.Weights.WeightLattice
import Humphreys.Ch7.AdmissibleLattice27_1

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v w w'

namespace Humphreys27_2

section AdjointDividedPowerIdentity

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- **Humphreys §27.2, Lemma (p. 159, verbatim):**
For any `u ∈ 𝔘(L)`, `x ∈ L`, and `n ∈ ℕ` (`= ℤ⁺`),
`((ad x)^n / n!)(u) = ∑_{i = 0}^n (-1)^i (x^{n-i} / (n-i)!) u (x^i / i!)` in `𝔘(L)`. -/
theorem ad_dividedPower_apply_uea
    (x : L) (u : _root_.UniversalEnvelopingAlgebra K L) (n : ℕ) :
    (n.factorial : K)⁻¹ •
        ((LieAlgebra.ad K (_root_.UniversalEnvelopingAlgebra K L)
            (_root_.UniversalEnvelopingAlgebra.ι K x)) ^ n) u =
      ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i •
          (dividedPower (n - i) (_root_.UniversalEnvelopingAlgebra.ι K x) * u *
            dividedPower i (_root_.UniversalEnvelopingAlgebra.ι K x)) := by
  let A := _root_.UniversalEnvelopingAlgebra K L
  let a : A := _root_.UniversalEnvelopingAlgebra.ι K x
  let _ : Algebra ℚ (Module.End K A) := Algebra.compHom (Module.End K A) (algebraMap ℚ K)
  let _ : Module ℚ≥0 (Module.End K A) := TauCeti.moduleNNRat
  have had : LieAlgebra.ad K A a = LinearMap.mulLeft K a - LinearMap.mulRight K a := by
    ext y; rfl
  have hcomm : Commute (LinearMap.mulLeft K a) (LinearMap.mulRight K a) :=
    LinearMap.commute_mulLeft_right a a
  have hmulLeft_pow : ∀ (k : ℕ) (y : A), ((LinearMap.mulLeft K a) ^ k) y = a ^ k * y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, ih, LinearMap.mulLeft_apply, pow_succ', mul_assoc]
  have hmulRight_pow : ∀ (k : ℕ) (y : A), ((LinearMap.mulRight K a) ^ k) y = y * a ^ k := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, ih, LinearMap.mulRight_apply, pow_succ, mul_assoc]
  have hdp_end : ∀ (f : Module.End K A) (k : ℕ) (y : A),
      (dividedPower k f) y = (k.factorial : K)⁻¹ • ((f ^ k) y) := by
    intro f k y
    rw [dividedPower_def, Algebra.smul_def]
    change (((algebraMap K (Module.End K A)) ((algebraMap ℚ K) (k.factorial : ℚ)⁻¹)) * f ^ k) y = _
    have hrat : (algebraMap ℚ K) (k.factorial : ℚ)⁻¹ = (k.factorial : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [hrat, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.smul_apply]
  have hdp_uea : ∀ (k : ℕ), dividedPower k a = (k.factorial : K)⁻¹ • a ^ k := by
    intro k
    rw [dividedPower_def, Algebra.smul_def]
    change (algebraMap K A ((algebraMap ℚ K) (k.factorial : ℚ)⁻¹)) * a ^ k = _
    have hrat : (algebraMap ℚ K) (k.factorial : ℚ)⁻¹ = (k.factorial : K)⁻¹ := by
      rw [map_inv₀, map_natCast]
    rw [hrat, Algebra.smul_def]
  have hlhs : (n.factorial : K)⁻¹ • ((LieAlgebra.ad K A a ^ n) u) =
      (dividedPower n (LinearMap.mulLeft K a - LinearMap.mulRight K a)) u := by
    rw [had, hdp_end]
  change (n.factorial : K)⁻¹ • ((LieAlgebra.ad K A a ^ n) u) = _
  rw [hlhs, TauCeti.Associative.dividedPower_sub hcomm n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j i => (-1 : ℚ) ^ i • (dividedPower j (LinearMap.mulLeft K a) *
        dividedPower i (LinearMap.mulRight K a))),
    ← Finset.sum_range_reflect, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : n - (n - i) = i := Nat.sub_sub_self hi_le
  simp only [Nat.add_one_sub_one, hsub]
  have hq : ((-1 : ℚ) ^ i • (dividedPower (n - i) (LinearMap.mulLeft K a) *
      dividedPower i (LinearMap.mulRight K a))) u =
      (-1 : ℤ) ^ i • ((dividedPower (n - i) (LinearMap.mulLeft K a))
        ((dividedPower i (LinearMap.mulRight K a)) u)) := by
    have hsign : (algebraMap ℚ K) ((-1 : ℚ) ^ i) = (((-1 : ℤ) ^ i : ℤ) : K) := by
      push_cast; rfl
    rw [Algebra.smul_def ((-1 : ℚ) ^ i)]
    change (((algebraMap K (Module.End K A)) ((algebraMap ℚ K) ((-1 : ℚ) ^ i))) * _) u = _
    rw [hsign, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      LinearMap.smul_apply, Int.cast_smul_eq_zsmul, mul_apply_eq_comp]
  rw [hq, hdp_end (LinearMap.mulRight K a) i u, hmulRight_pow, map_smul, hdp_end, hmulLeft_pow]
  congr 1
  rw [hdp_uea, hdp_uea, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    smul_smul, mul_comm ((i.factorial : K)⁻¹), mul_assoc]

end AdjointDividedPowerIdentity

section StabilizerLattice

variable {K : Type u} {L : Type v}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA' :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

/-- **Root lattice `Λ_r ⊂ H*` (H §13.1, §27.2 p. 159):** the `ℤ`-span of the roots of `(L, H)`
inside `Module.Dual K H`. -/
noncomputable def rootLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] :
    Submodule ℤ (Module.Dual K H) :=
  Submodule.span ℤ
    (Set.range fun α : H.root => ((rootSystem H).root α : Module.Dual K H))

/-- **Module weight lattice `Λ(V) = ℤ Π(V) ⊂ H*` (`D27.2`, H p. 159):** the `ℤ`-span of the
weights `Weight K H V` of an `L`-module `V` inside `Module.Dual K H`. -/
noncomputable def moduleWeightLattice (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    Submodule ℤ (Module.Dual K H) :=
  Submodule.span ℤ (Set.range fun χ : Weight K H V => (χ : Module.Dual K H))

/-- **Humphreys Exercise 21.5, first assertion (p. 116) as invoked in §27.2 (p. 159):**
For any faithful finite-dimensional `L`-module `V`, `Λ_r ≤ Λ(V) ≤ Λ`. -/
theorem rootLattice_le_moduleWeightLattice_le_integralWeightLattice
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V] :
    rootLattice H ≤ moduleWeightLattice H V ∧
      moduleWeightLattice H V ≤ TauCeti.integralWeightLattice H := by
  refine ⟨?_, ?_⟩
  · rw [rootLattice, Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    dsimp only
    obtain ⟨e, he, he0⟩ := (α : Weight K H L).exists_ne_zero
    have hex_m : ∃ m : V, ⁅e, m⁆ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact he0 ((LieModule.isFaithful_iff' K L V).mp inferInstance e hall)
    have htopW : (⨆ χ : Weight K H V,
        (LieModule.weightSpace V (χ : H → K)).toSubmodule) = ⊤ := by
      simpa only [← LieSubmodule.iSup_toSubmodule, LieSubmodule.toSubmodule_eq_top] using
        TauCeti.iSup_weightSpace_eq_top K H V
    have hex_wt : ∃ (χ : Weight K H V) (v : V),
        v ∈ LieModule.weightSpace V (χ : H → K) ∧ ⁅e, v⁆ ≠ 0 := by
      by_contra hall
      push Not at hall
      obtain ⟨m, hm⟩ := hex_m
      apply hm
      have hm_top : m ∈ (⨆ χ : Weight K H V,
          (LieModule.weightSpace V (χ : H → K)).toSubmodule) := htopW.symm ▸ Submodule.mem_top
      have hker : (⨆ χ : Weight K H V,
          (LieModule.weightSpace V (χ : H → K)).toSubmodule) ≤
          LinearMap.ker (LieModule.toEnd K L V e) := by
        refine iSup_le fun χ v hv => ?_
        rw [LinearMap.mem_ker, LieModule.toEnd_apply_apply]
        exact hall χ v hv
      exact LinearMap.mem_ker.mp (hker hm_top)
    obtain ⟨χ, v, hv, hev_nz⟩ := hex_wt
    rw [← TauCeti.genWeightSpace_eq_weightSpace] at hv
    have hmem_add :
        ⁅e, v⁆ ∈ LieModule.genWeightSpace V (((α : Weight K H L) : H → K) + (χ : H → K)) :=
      LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace he hv
    have hne_bot :
        LieModule.genWeightSpace V (((α : Weight K H L) : H → K) + (χ : H → K)) ≠ ⊥ := by
      intro hbot
      rw [hbot, LieSubmodule.mem_bot] at hmem_add
      exact hev_nz hmem_add
    let χ' : Weight K H V := ⟨((α : Weight K H L) : H → K) + (χ : H → K), hne_bot⟩
    have hdiff : ((rootSystem H).root α : Module.Dual K H) =
        (χ' : Module.Dual K H) - (χ : Module.Dual K H) := by
      ext h
      simp [χ', rootSystem_root_apply]
    rw [hdiff]
    exact (moduleWeightLattice H V).sub_mem
      (Submodule.subset_span ⟨χ', rfl⟩)
      (Submodule.subset_span ⟨χ, rfl⟩)
  · rw [moduleWeightLattice, Submodule.span_le]
    rintro _ ⟨χ, rfl⟩
    dsimp only
    exact TauCeti.isIntegralWeight_of_weight χ

/-- **Stabilizer `L_V` of an additive/integral submodule `M ⊂ V` in `L` (`D27.2`, H p. 159):**
`L_V(M) = {y ∈ L | y · M ⊆ M}` as a `ℤ`-submodule of `L`. -/
def stabilizerLattice (L : Type v) {V : Type w} [LieRing L] [AddCommGroup V]
    [LieRingModule L V] (M : Submodule ℤ V) : Submodule ℤ L where
  carrier := {y : L | ∀ m ∈ M, ⁅y, m⁆ ∈ M}
  zero_mem' m _ := by rw [zero_lie]; exact M.zero_mem
  add_mem' {y₁ y₂} hy₁ hy₂ m hm := by rw [add_lie]; exact M.add_mem (hy₁ m hm) (hy₂ m hm)
  smul_mem' z y hy m hm := by rw [zsmul_lie]; exact M.smul_mem z (hy m hm)

/-- **Cartan dual lattice `{h ∈ H | ∀ μ ∈ Λ(V), μ(h) ∈ ℤ}` (`D27.2`, H p. 159):**
defined intrinsically inside `H` from `Λ(V) = moduleWeightLattice H V` alone (with no reference
to `M`). -/
noncomputable def cartanWeightDualSubmodule (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] :
    Submodule ℤ H :=
  ⨅ μ : moduleWeightLattice H V,
    (1 : Submodule ℤ K).comap ((μ.1 : Module.Dual K H).restrictScalars ℤ)

omit [CharZero K] in
private theorem mem_one_submodule_int_iff (c : K) :
    c ∈ (1 : Submodule ℤ K) ↔ ∃ z : ℤ, (z : K) = c := by
  rw [Submodule.one_eq_span, Submodule.mem_span_singleton]
  simp only [zsmul_one]

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
private theorem mem_cartanWeightDualSubmodule_iff
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] (h : H) :
    h ∈ cartanWeightDualSubmodule H V ↔
      ∀ μ ∈ moduleWeightLattice H V, ∃ z : ℤ, (z : K) = μ h := by
  simp only [cartanWeightDualSubmodule, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, mem_one_submodule_int_iff, Subtype.forall]

omit [CharZero K] [LieModule.IsTriangularizable K H L] in
private theorem mem_cartanWeightDualSubmodule_iff_forall_weight
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V] (h : H) :
    h ∈ cartanWeightDualSubmodule H V ↔
      ∀ χ : Weight K H V, ∃ z : ℤ, (z : K) = χ h := by
  rw [mem_cartanWeightDualSubmodule_iff]
  constructor
  · intro hh χ
    exact hh (χ : Module.Dual K H) (Submodule.subset_span ⟨χ, rfl⟩)
  · intro hh μ hμ
    rw [← mem_one_submodule_int_iff]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hμ
    · rintro _ ⟨χ, rfl⟩
      rw [mem_one_submodule_int_iff]
      exact hh χ
    · simp
    · intro f₁ f₂ _ _ h₁ h₂
      rw [LinearMap.add_apply]
      exact (1 : Submodule ℤ K).add_mem h₁ h₂
    · intro z f _ hf
      rw [LinearMap.smul_apply]
      exact (1 : Submodule ℤ K).smul_mem z hf

/-- **Humphreys §27.2 setup characterization of `H_V = H ∩ L_V` (p. 159):**
For any faithful finite-dimensional `L`-module `V` and any admissible lattice `M` in `V`,
`L_V(M) ∩ H` coincides with the image of `cartanWeightDualSubmodule H V` in `L`, and
`cartanWeightDualSubmodule H V` is a full `ℤ`-lattice in `H`. -/
theorem cartanStabilizer_eq_weightDual_and_isFullZLattice
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M) :
    stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ =
        (cartanWeightDualSubmodule H V).map (H.toSubmodule.restrictScalars ℤ).subtype ∧
      Humphreys27_1.IsFullZLattice K (cartanWeightDualSubmodule H V) := by
  classical
  have hM_decomp_all :=
    Humphreys27_1.weightSpace_inter_directSum_of_isKostantInvariant hx M.toAddSubgroup hM.2
  have hM_decomp := hM_decomp_all.1
  have hInt_Z := hM_decomp_all.2.2
  obtain ⟨hM_fg, hM_span_top, hM_rk_le⟩ :=
    (Humphreys27_1.isFullZLattice_iff_fg_and_span_eq_top_and_finrank_le M).mp hM.1
  let W_K : Weight K H V → Submodule K V :=
    fun η => (LieModule.weightSpace V (η : H → K)).toSubmodule
  let N_M : Weight K H V → Submodule ℤ M := fun η =>
    ((W_K η).restrictScalars ℤ).comap (AddMonoidHom.toIntLinearMap M.toAddSubgroup.subtype)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hM_fg
  have : IsNoetherian ℤ M := inferInstance
  have : Module.IsTorsionFree ℤ V := ⟨fun z hz w₁ w₂ hw => by
    have hsub : (z : K) • (w₁ - w₂) = 0 := by
      rw [Int.cast_smul_eq_zsmul, zsmul_sub, sub_eq_zero]
      exact hw
    exact sub_eq_zero.mp
      ((smul_eq_zero.mp hsub).resolve_left (Int.cast_ne_zero.mpr hz.ne_zero))⟩
  have : Module.IsTorsionFree ℤ M := Submodule.instIsTorsionFree M
  have hN_fin : ∀ η, Module.Finite ℤ (N_M η) := fun η =>
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (N_M η))
  have hN_tf : ∀ η, Module.IsTorsionFree ℤ (N_M η) := fun η => Submodule.instIsTorsionFree (N_M η)
  have hN_free : ∀ η, Module.Free ℤ (N_M η) := fun η => by
    have := hN_fin η; have := hN_tf η; exact Module.free_of_finite_type_torsion_free'
  let b_η : ∀ η : Weight K H V, Module.Basis (Fin (Module.finrank ℤ (N_M η))) ℤ (N_M η) :=
    fun η => by have := hN_fin η; have := hN_free η; exact Module.finBasis ℤ (N_M η)
  let bM : Module.Basis (Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η))) ℤ M :=
    hInt_Z.collectedBasis b_η
  let v_wt : (Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η))) → V := fun idx => (bM idx : V)
  have hspan_v_Z : Submodule.span ℤ (Set.range v_wt) = M := by
    have hmap := congrArg (Submodule.map M.subtype) bM.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at hmap
    exact hmap
  have hspan_v_K : Submodule.span K (Set.range v_wt) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ K (Set.range v_wt), hspan_v_Z, hM_span_top]
  have hcard_bM : Fintype.card (Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η))) =
      Module.finrank ℤ M := (Module.finrank_eq_card_basis bM).symm
  have hle_rk : Module.finrank K V ≤ Module.finrank ℤ M := by
    have hcard := finrank_span_le_card (R := K) (Set.range v_wt)
    rw [hspan_v_K, finrank_top] at hcard
    exact le_trans hcard (le_trans (Set.toFinset_card (Set.range v_wt) ▸ Fintype.card_range_le v_wt)
      (le_of_eq hcard_bM))
  have hrk_eq : Fintype.card (Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η))) =
      Module.finrank K V := hcard_bM.trans (le_antisymm hM_rk_le hle_rk)
  have hli_v : LinearIndependent K v_wt :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan_v_K.ge hrk_eq
  let bV : Module.Basis (Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η))) K V :=
    Module.Basis.mk hli_v hspan_v_K.ge
  have hbV_apply : ∀ idx, bV idx = v_wt idx := Module.Basis.mk_apply hli_v hspan_v_K.ge
  have hbV_wt : ∀ (η : Weight K H V) (j : Fin (Module.finrank ℤ (N_M η))),
      bV ⟨η, j⟩ ∈ W_K η := by
    intro η j
    rw [hbV_apply]
    dsimp only [v_wt, bM]
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact (b_η η j).2
  have hbV_span_Z : Submodule.span ℤ (Set.range bV) = M := by
    have hr : Set.range bV = Set.range v_wt := by ext y; simp [hbV_apply]
    rw [hr, hspan_v_Z]
  have hbV_repr_int : ∀ {y : V}, y ∈ Submodule.span ℤ (Set.range bV) → ∀ idx,
      bV.repr y idx ∈ Set.range (Int.cast : ℤ → K) := by
    intro y hy idx
    rw [Set.mem_range, ← mem_one_submodule_int_iff]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨idx', rfl⟩
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact (mem_one_submodule_int_iff 1).mpr ⟨1, Int.cast_one⟩
      · exact (1 : Submodule ℤ K).zero_mem
    · simp
    · intro a₁ a₂ _ _ h₁ h₂
      rw [map_add, Finsupp.add_apply]
      exact (1 : Submodule ℤ K).add_mem h₁ h₂
    · intro z a₁ _ h₁
      rw [map_zsmul, Finsupp.smul_apply]
      exact (1 : Submodule ℤ K).smul_mem z h₁
  have hcartan_iff : ∀ h : H,
      (h : L) ∈ stabilizerLattice L M ↔ h ∈ cartanWeightDualSubmodule H V := by
    intro h
    rw [mem_cartanWeightDualSubmodule_iff_forall_weight]
    constructor
    · intro hh χ
      have hr_pos : 0 < Module.finrank ℤ (N_M χ) := by
        by_contra hr0
        have hr_eq0 : Module.finrank ℤ (N_M χ) = 0 := by omega
        obtain ⟨v_nz, hv_nz_mem, hv_nz⟩ := χ.exists_ne_zero
        have hv_W : v_nz ∈ W_K χ := by
          dsimp only [W_K]
          rwa [← TauCeti.genWeightSpace_eq_weightSpace]
        have htop_other : ⊤ ≤ ⨆ η : Weight K H V, ⨆ (_ : η ≠ χ), W_K η := by
          rw [← bV.span_eq, Submodule.span_le]
          rintro _ ⟨⟨η, j⟩, rfl⟩
          have hne : η ≠ χ := by
            rintro rfl
            exact Fin.elim0 (hr_eq0 ▸ j)
          exact Submodule.mem_iSup_of_mem η (Submodule.mem_iSup_of_mem hne (hbV_wt η j))
        have hindep := (TauCeti.isInternal_weightSpace K H V).submodule_iSupIndep χ
        have hv0 : v_nz = 0 :=
          Submodule.disjoint_def.mp hindep v_nz hv_W (htop_other Submodule.mem_top)
        exact hv_nz hv0
      let idx₀ : Σ η : Weight K H V, Fin (Module.finrank ℤ (N_M η)) := ⟨χ, ⟨0, hr_pos⟩⟩
      have hb_mem_M : bV idx₀ ∈ M := by
        rw [hbV_apply]
        exact (bM idx₀).2
      have hb_wt : bV idx₀ ∈ LieModule.genWeightSpace V (χ : H → K) := by
        rw [TauCeti.genWeightSpace_eq_weightSpace]
        exact hbV_wt χ ⟨0, hr_pos⟩
      have hlie_eq : ⁅(h : L), bV idx₀⁆ = (χ h) • bV idx₀ :=
        TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hb_wt h
      have hsmul_M : (χ h) • bV idx₀ ∈ M := hlie_eq ▸ hh (bV idx₀) hb_mem_M
      have hsmul_span : (χ h) • bV idx₀ ∈ Submodule.span ℤ (Set.range bV) := by
        change (χ h) • bV idx₀ ∈ (Submodule.span ℤ (Set.range bV) : Set V)
        rw [hbV_span_Z]
        exact hsmul_M
      obtain ⟨z, hz⟩ := hbV_repr_int hsmul_span idx₀
      rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.single_eq_same] at hz
      exact ⟨z, hz⟩
    · intro hh m hm
      have hm' : m ∈ (⨆ η : Weight K H V,
          M.toAddSubgroup ⊓ (W_K η).toAddSubgroup) := hM_decomp.symm ▸ hm
      have hle : (⨆ η : Weight K H V, M.toAddSubgroup ⊓ (W_K η).toAddSubgroup) ≤
          M.toAddSubgroup.comap (LieModule.toEnd K L V (h : L)).toAddMonoidHom := by
        refine iSup_le fun η y hy => ?_
        change ⁅(h : L), y⁆ ∈ M
        have hy_gen : y ∈ LieModule.genWeightSpace V (η : H → K) := by
          rw [TauCeti.genWeightSpace_eq_weightSpace]
          exact hy.2
        have hlie_y : ⁅(h : L), y⁆ = (η h) • y :=
          TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hy_gen h
        obtain ⟨z, hz⟩ := hh η
        rw [hlie_y, ← hz, Int.cast_smul_eq_zsmul]
        exact M.smul_mem z hy.1
      exact hle hm'
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hyL, hyH⟩
      have hyH' : y ∈ H := hyH
      exact ⟨⟨y, hyH'⟩, (hcartan_iff ⟨y, hyH'⟩).mp hyL, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨(hcartan_iff h).mpr hh, h.2⟩
  · let H_dual := cartanWeightDualSubmodule H V
    obtain ⟨h_rl_le, h_mwl_le⟩ :=
      rootLattice_le_moduleWeightLattice_le_integralWeightLattice (H := H) V
    have hcoroot_mem : ∀ α : H.root, (rootSystem H).coroot α ∈ H_dual := by
      intro α
      rw [mem_cartanWeightDualSubmodule_iff]
      intro μ hμ
      have hint : TauCeti.IsIntegralWeight μ :=
        (TauCeti.mem_integralWeightLattice_iff (H := H)).mp (h_mwl_le hμ)
      rw [rootSystem_coroot_apply]
      obtain ⟨z, hz⟩ := hint.exists_int_apply_coroot (α : Weight K H L)
      exact ⟨z, hz.symm⟩
    have hspan_H_top : Submodule.span K (H_dual : Set H) = ⊤ := by
      rw [← top_le_iff, ← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H)]
      refine Submodule.span_mono ?_
      rintro _ ⟨α, rfl⟩
      exact hcoroot_mem α
    obtain ⟨b⟩ := (rootSystem H).nonempty_base
    have hroot_int : ∀ (h : H_dual) (i : ↥b.support),
        ∃ z : ℤ, (z : K) = (rootSystem H).root i.1 h.1 := by
      intro h i
      exact (mem_cartanWeightDualSubmodule_iff h.1).mp h.2 ((rootSystem H).root i.1)
        (h_rl_le (Submodule.subset_span ⟨i.1, rfl⟩))
    choose z_coord hz_coord using hroot_int
    let φ : H_dual →ₗ[ℤ] (↥b.support → ℤ) :=
      { toFun := z_coord
        map_add' := fun h₁ h₂ => by
          ext i
          apply Int.cast_injective (α := K)
          rw [Pi.add_apply, Int.cast_add, hz_coord, hz_coord, hz_coord,
            AddMemClass.coe_add, map_add]
        map_smul' := fun c h₁ => by
          ext i
          apply Int.cast_injective (α := K)
          simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul, hz_coord,
            SetLike.val_smul, map_zsmul, zsmul_eq_mul] }
    have hφ_inj : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro h hh
      rw [LinearMap.mem_ker] at hh
      have hsupp0 : ∀ r ∈ b.support, (rootSystem H).root r h.1 = 0 := by
        intro r hr
        have hi0 : z_coord h ⟨r, hr⟩ = 0 := congrFun hh ⟨r, hr⟩
        rw [← hz_coord h ⟨r, hr⟩, hi0, Int.cast_zero]
      have hroot0 : ∀ α : H.root, (rootSystem H).root α h.1 = 0 := by
        intro α
        have hmem := b.root_mem_span_int α
        refine Submodule.span_induction ?_ (by simp)
          (fun f₁ f₂ _ _ h₁ h₂ => by rw [LinearMap.add_apply, h₁, h₂, add_zero])
          (fun c f₁ _ hf₁ => by rw [LinearMap.smul_apply, hf₁, smul_zero]) hmem
        rintro _ ⟨r, hr, rfl⟩
        exact hsupp0 r hr
      have hdual0 : ∀ f : Module.Dual K H, f h.1 = 0 := by
        intro f
        have htop : f ∈ Submodule.span K (Set.range (rootSystem H).root) := by
          rw [RootPairing.IsRootSystem.span_root_eq_top]
          trivial
        refine Submodule.span_induction ?_ (by simp)
          (fun f₁ f₂ _ _ h₁ h₂ => by rw [LinearMap.add_apply, h₁, h₂, add_zero])
          (fun c f₁ _ hf₁ => by rw [LinearMap.smul_apply, hf₁, smul_zero]) htop
        rintro _ ⟨α, rfl⟩
        exact hroot0 α
      exact Subtype.ext ((Module.forall_dual_apply_eq_zero_iff K h.1).mp hdual0)
    have hH_fin : Module.Finite ℤ H_dual := by
      let eRange : H_dual ≃ₗ[ℤ] LinearMap.range φ := LinearEquiv.ofInjective φ hφ_inj
      have : Module.Finite ℤ (LinearMap.range φ) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (LinearMap.range φ))
      exact Module.Finite.equiv eRange.symm
    have hH_fg : H_dual.FG := Module.Finite.iff_fg.mp hH_fin
    have : Module.IsTorsionFree ℤ H := ⟨fun z hz w₁ w₂ hw => by
      have hsub : (z : K) • (w₁ - w₂) = 0 := by
        rw [Int.cast_smul_eq_zsmul, zsmul_sub, sub_eq_zero]
        exact hw
      exact sub_eq_zero.mp
        ((smul_eq_zero.mp hsub).resolve_left (Int.cast_ne_zero.mpr hz.ne_zero))⟩
    have : Module.IsTorsionFree ℤ H_dual := Submodule.instIsTorsionFree H_dual
    have : Module.Free ℤ H_dual := Module.free_of_finite_type_torsion_free'
    let r_d := Module.finrank ℤ H_dual
    let bHd : Module.Basis (Fin r_d) ℤ H_dual := Module.finBasis ℤ H_dual
    have hcoroot_li : LinearIndependent K (fun i : ↥b.support => (rootSystem H).coroot i.1) := by
      refine LinearIndependent.of_comp H.toSubmodule.subtype ?_
      have hcomp : (H.toSubmodule.subtype ∘ fun i : ↥b.support => (rootSystem H).coroot i.1) =
          (Humphreys26_4.GapB.chevalleyAmbientBasis hx b) ∘ Sum.inr := by
        funext i
        simp [Humphreys26_4.GapB.chevalleyAmbientBasis_inr]
      rw [hcomp]
      exact (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).linearIndependent.comp
        Sum.inr Sum.inr_injective
    have hcard_supp_le : Fintype.card ↥b.support ≤ Module.finrank K H :=
      hcoroot_li.fintype_card_le_finrank
    have hli_Q : LinearIndependent ℚ (fun j : Fin r_d =>
        fun i : ↥b.support => (φ (bHd j) i : ℚ)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc j₀
      let D : ℕ := ∏ j : Fin r_d, (c j).den
      have hD_pos : 0 < D := Finset.prod_pos fun j _ => (c j).pos
      let z_c : Fin r_d → ℤ := fun j => (c j).num * ((D / (c j).den : ℕ) : ℤ)
      have hzc_eq : ∀ j : Fin r_d, (z_c j : ℚ) = (D : ℚ) * c j := by
        intro j
        have hdvd : (c j).den ∣ D :=
          Finset.dvd_prod_of_mem (fun j' : Fin r_d => (c j').den) (Finset.mem_univ j)
        obtain ⟨q_nat, hq⟩ := hdvd
        have hdiv : D / (c j).den = q_nat := by
          rw [hq, Nat.mul_div_cancel_left _ (c j).pos]
        dsimp only [z_c]
        rw [hdiv, hq]
        push_cast
        have hnd := Rat.mul_den_eq_num (c j)
        calc
          ((c j).num : ℚ) * (q_nat : ℚ) = (c j * (c j).den) * (q_nat : ℚ) := by rw [hnd]
          _ = ((c j).den : ℚ) * (q_nat : ℚ) * c j := by ring
      have hsum_φ : φ (∑ j : Fin r_d, z_c j • bHd j) = 0 := by
        ext i
        rw [map_sum, Finset.sum_apply, Pi.zero_apply]
        apply Int.cast_injective (α := ℚ)
        rw [Int.cast_sum, Int.cast_zero]
        have hpt := congrFun hc i
        simp only [Finset.sum_apply, Pi.zero_apply] at hpt
        change (∑ x : Fin r_d, c x * (φ (bHd x) i : ℚ)) = 0 at hpt
        have hmul : (D : ℚ) * (∑ j : Fin r_d, c j * (φ (bHd j) i : ℚ)) = 0 := by
          rw [hpt, mul_zero]
        rw [Finset.mul_sum] at hmul
        refine (Finset.sum_congr rfl fun j _ => ?_).trans hmul
        simp only [map_zsmul, Pi.smul_apply, smul_eq_mul, Int.cast_mul, hzc_eq j, mul_assoc]
      have hsum0 : ∑ j : Fin r_d, z_c j • bHd j = 0 :=
        hφ_inj (hsum_φ.trans (map_zero φ).symm)
      have hz0 : z_c j₀ = 0 :=
        Fintype.linearIndependent_iff.mp bHd.linearIndependent z_c hsum0 j₀
      have hq0 := hzc_eq j₀
      rw [hz0, Int.cast_zero] at hq0
      exact (mul_eq_zero.mp hq0.symm).resolve_left
        (Nat.cast_ne_zero.mpr (ne_of_gt hD_pos))
    have hrd_le_supp : r_d ≤ Fintype.card ↥b.support := by
      have hcard := hli_Q.fintype_card_le_finrank
      simpa only [Fintype.card_fin, Module.finrank_pi (R := ℚ)] using hcard
    exact (Humphreys27_1.isFullZLattice_iff_fg_and_span_eq_top_and_finrank_le H_dual).mpr
      ⟨hH_fg, hspan_H_top, le_trans hrd_le_supp hcard_supp_le⟩

/-- **Humphreys, Proposition 27.2 (p. 160, verbatim):**
For any faithful finite-dimensional `L`-module `V` and any admissible lattice `M` in `V`:
(1) `L_V = stabilizerLattice M` is closed under the Lie bracket of `L`;
(2) `L_V` is an admissible lattice in the adjoint `L`-module `L`;
(3) `L_V ∩ L_α = ℤ x_α` for every root `α ∈ Φ`; and
(4) `L_V = H_V ⊕ ⨁_{α ∈ Φ} ℤ x_α` where `H_V = L_V ∩ H`. -/
theorem isAdmissibleLattice_stabilizerLattice_and_decomposition
    {V : Type w} [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] [LieModule.IsFaithful K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M) :
    (∀ y₁ ∈ stabilizerLattice L M, ∀ y₂ ∈ stabilizerLattice L M,
        ⁅y₁, y₂⁆ ∈ stabilizerLattice L M) ∧
      Humphreys27_1.IsAdmissibleLattice H x (stabilizerLattice L M) ∧
      (∀ α : H.root,
        stabilizerLattice L M ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {x (α : Weight K H L)}) ∧
      stabilizerLattice L M =
        (stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ) ⊔
          (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) ∧
      Disjoint
        (stabilizerLattice L M ⊓ H.toSubmodule.restrictScalars ℤ)
        (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) ∧
      iSupIndep (fun α : H.root => Submodule.span ℤ {x (α : Weight K H L)}) := by
  classical
  let _ : LieRing (_root_.UniversalEnvelopingAlgebra K L) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (_root_.UniversalEnvelopingAlgebra K L) := LieAlgebra.ofAssociativeAlgebra
  let L_V := stabilizerLattice L M
  let ρ_ad := TauCeti.UniversalEnvelopingAlgebra.representation K L L
  let ρ_V := TauCeti.UniversalEnvelopingAlgebra.representation K L V
  let ι : L →ₗ⁅K⁆ _root_.UniversalEnvelopingAlgebra K L := _root_.UniversalEnvelopingAlgebra.ι K
  -- (1) Bracket closure of `L_V`
  have hbracket : ∀ y₁ ∈ L_V, ∀ y₂ ∈ L_V, ⁅y₁, y₂⁆ ∈ L_V := by
    intro y₁ hy₁ y₂ hy₂ m hm
    rw [lie_lie]
    exact M.sub_mem (hy₁ _ (hy₂ m hm)) (hy₂ _ (hy₁ m hm))
  -- (2a) `𝔘_ℤ`-invariance of `L_V` via Lemma 27.2 (`ad_dividedPower_apply_uea`)
  have hLV_inv : Humphreys27_1.IsKostantInvariant H x L_V := by
    let S_inv : Subring (_root_.UniversalEnvelopingAlgebra K L) :=
      { carrier := {u | ∀ y ∈ L_V, ρ_ad u y ∈ L_V}
        one_mem' := fun y hy => by simpa using hy
        mul_mem' := fun {u₁ u₂} hu₁ hu₂ y hy => by
          rw [map_mul, mul_apply_eq_comp]
          exact hu₁ _ (hu₂ y hy)
        zero_mem' := fun y _ => by simp [L_V.zero_mem]
        add_mem' := fun {u₁ u₂} hu₁ hu₂ y hy => by
          rw [map_add, LinearMap.add_apply]
          exact L_V.add_mem (hu₁ y hy) (hu₂ y hy)
        neg_mem' := fun {u} hu y hy => by
          rw [map_neg, LinearMap.neg_apply]
          exact L_V.neg_mem (hu y hy) }
    have hle : Humphreys26_4.kostantSubring H x ≤ S_inv := by
      rw [Humphreys26_4.kostantSubring, Subring.closure_le]
      rintro _ ⟨⟨α, n⟩, rfl⟩ y hy m hm
      let x_α := x (α : Weight K H L)
      have hρ_ad_pow : ∀ (k : ℕ) (z : L),
          ((ρ_ad (ι x_α)) ^ k) z = ((LieAlgebra.ad K L x_α) ^ k) z := by
        intro k
        induction k with
        | zero => intro z; simp
        | succ k ih =>
          intro z
          rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ih,
            TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply]
          rfl
      have hρ_ad_dp : ρ_ad (dividedPower n (ι x_α)) y =
          (n.factorial : K)⁻¹ • (((LieAlgebra.ad K L x_α) ^ n) y) := by
        rw [dividedPower_def, Algebra.smul_def, map_mul, map_pow, mul_apply_eq_comp, hρ_ad_pow]
        have hsc : ρ_ad ((algebraMap ℚ (_root_.UniversalEnvelopingAlgebra K L)) (n.factorial : ℚ)⁻¹) =
            (n.factorial : K)⁻¹ • (1 : Module.End K L) := by
          change ρ_ad (algebraMap K (_root_.UniversalEnvelopingAlgebra K L)
            ((algebraMap ℚ K) (n.factorial : ℚ)⁻¹)) = _
          rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_inv₀, map_natCast]
        rw [hsc, LinearMap.smul_apply, one_apply_eq_self]
      have hι_ad_pow : ∀ (k : ℕ) (z : L),
          ι (((LieAlgebra.ad K L x_α) ^ k) z) =
            ((LieAlgebra.ad K (_root_.UniversalEnvelopingAlgebra K L) (ι x_α)) ^ k) (ι z) := by
        intro k
        induction k with
        | zero => intro z; simp
        | succ k ih =>
          intro z
          rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ← ih]
          exact LieHom.map_lie ι x_α (((LieAlgebra.ad K L x_α) ^ k) z)
      have hι_w : ι (ρ_ad (dividedPower n (ι x_α)) y) =
          ∑ i ∈ Finset.range (n + 1),
            (-1 : ℤ) ^ i • (dividedPower (n - i) (ι x_α) * ι y * dividedPower i (ι x_α)) := by
        rw [hρ_ad_dp, map_smul, hι_ad_pow]
        exact ad_dividedPower_apply_uea x_α (ι y) n
      have hact : ⁅ρ_ad (dividedPower n (ι x_α)) y, m⁆ =
          ρ_V (ι (ρ_ad (dividedPower n (ι x_α)) y)) m := by
        rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply]
      rw [hact, hι_w, map_sum, LinearMap.sum_apply]
      refine M.sum_mem fun i _ => ?_
      rw [map_zsmul, LinearMap.smul_apply]
      refine M.smul_mem ((-1 : ℤ) ^ i) ?_
      rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
      have hm₁ : ρ_V (dividedPower i (ι x_α)) m ∈ M :=
        hM.2 _ (Subring.subset_closure ⟨(α, i), rfl⟩) m hm
      have hm₂ : ρ_V (ι y) (ρ_V (dividedPower i (ι x_α)) m) ∈ M := by
        rw [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply]
        exact hy _ hm₁
      exact hM.2 _ (Subring.subset_closure ⟨(α, n - i), rfl⟩) _ hm₂
    intro u hu y hy
    exact hle hu y hy
  -- Every Chevalley vector `x β` (`β : Weight K H L`) belongs to `L_V`
  have hx_wt_mem_LV : ∀ β : Weight K H L, x β ∈ L_V := by
    intro β m hm
    have h1 : dividedPower 1 (ι (x β)) = ι (x β) := by
      simp [dividedPower_def]
    have hmem_k : ι (x β) ∈ Humphreys26_4.kostantSubring H x := by
      rw [← h1]
      exact Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx β 1
    have hact := hM.2 _ hmem_k m hm
    rwa [TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply] at hact
  obtain ⟨hHV_eq, hHV_full⟩ := cartanStabilizer_eq_weightDual_and_isFullZLattice hx M hM
  obtain ⟨h_rl_le, _⟩ := rootLattice_le_moduleWeightLattice_le_integralWeightLattice (H := H) V
  -- (3) Root-space divisibility exclusion (`2 / n³ ∈ (1/n) ℤ ⟹ n = 1`) proving `L_V ∩ L_α = ℤ x_α`
  have hdiv_excl : ∀ (α : H.root) (n : ℕ), 0 < n →
      L_V ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {(n : K)⁻¹ • x (α : Weight K H L)} → n = 1 := by
    intro α n hn hspan_n
    have hα_nz : (α : Weight K H L).IsNonZero := H.isNonZero_coe_root α
    let e := x (α : Weight K H L)
    let f := x (-(α : Weight K H L))
    let h_α := ((coroot (α : Weight K H L) : H) : L)
    have ht : IsSl2Triple h_α e f := hx.toIsSl2System.isSl2Triple (α : Weight K H L) hα_nz
    have he_nz : e ≠ 0 := hx.toIsSl2System.ne_zero (α : Weight K H L) hα_nz
    have hz_mem : (n : K)⁻¹ • e ∈ L_V :=
      (hspan_n ▸ Submodule.subset_span (Set.mem_singleton ((n : K)⁻¹ • e))).1
    have hdp2_mem : dividedPower 2 (ι f) ∈ Humphreys26_4.kostantSubring H x :=
      Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx (-(α : Weight K H L)) 2
    have had2_e : ρ_ad (dividedPower 2 (ι f)) ((n : K)⁻¹ • e) = -((n : K)⁻¹ • f) := by
      have hf1 : ρ_ad (ι f) e = -h_α := by
        change ⁅f, e⁆ = -h_α
        rw [← lie_skew, ht.lie_e_f]
      have hf2 : ((ρ_ad (ι f)) ^ 2) e = -(2 • f) := by
        rw [sq, mul_apply_eq_comp, hf1, map_neg]
        change -⁅f, h_α⁆ = -(2 • f)
        rw [← lie_skew, neg_neg, ht.lie_h_f_nsmul]
      have hdp2_apply : ρ_ad (dividedPower 2 (ι f)) e = -f := by
        rw [dividedPower_def, Algebra.smul_def, map_mul, map_pow, mul_apply_eq_comp, hf2]
        have hsc : ρ_ad ((algebraMap ℚ (_root_.UniversalEnvelopingAlgebra K L))
            (((2 : ℕ).factorial : ℚ)⁻¹)) =
            (2 : K)⁻¹ • (1 : Module.End K L) := by
          change ρ_ad (algebraMap K (_root_.UniversalEnvelopingAlgebra K L)
            ((algebraMap ℚ K) (((2 : ℕ).factorial : ℚ)⁻¹))) = _
          rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_inv₀, map_natCast]
          rfl
        rw [hsc, LinearMap.smul_apply, one_apply_eq_self, smul_neg, ← Nat.cast_smul_eq_nsmul K 2 f,
          smul_smul, Nat.cast_two, inv_mul_cancel₀ (two_ne_zero' K), one_smul]
      rw [map_smul, hdp2_apply, smul_neg]
    have hf_mem : (n : K)⁻¹ • f ∈ L_V := by
      have hneg_mem : -((n : K)⁻¹ • f) ∈ L_V := had2_e ▸ hLV_inv _ hdp2_mem _ hz_mem
      simpa only [neg_neg] using L_V.neg_mem hneg_mem
    have hh_mem : ((n : K)⁻¹ * (n : K)⁻¹) • h_α ∈ L_V := by
      have hb1 := hbracket _ hz_mem _ hf_mem
      rwa [smul_lie, lie_smul, ht.lie_e_f, smul_smul] at hb1
    have hcube_mem_LV : (((n : K)⁻¹ * (n : K)⁻¹ * (n : K)⁻¹) * 2) • e ∈ L_V := by
      have hb2 := hbracket _ hh_mem _ hz_mem
      rw [smul_lie, lie_smul, ht.lie_h_e_nsmul, ← Nat.cast_smul_eq_nsmul K 2 e,
        Nat.cast_two, smul_smul, smul_smul] at hb2
      convert hb2 using 2
    have hcube_mem_inter : (((n : K)⁻¹ * (n : K)⁻¹ * (n : K)⁻¹) * 2) • e ∈
        L_V ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ := by
      refine ⟨hcube_mem_LV, ?_⟩
      exact (rootSpace H (α : H → K)).toSubmodule.smul_mem _
        (hx.toIsSl2System.mem_rootSpace (α : Weight K H L))
    rw [hspan_n, Submodule.mem_span_singleton] at hcube_mem_inter
    obtain ⟨k, hk⟩ := hcube_mem_inter
    rw [← Int.cast_smul_eq_zsmul K k, smul_smul] at hk
    have hcoeff_eq : (k : K) * (n : K)⁻¹ = ((n : K)⁻¹ * (n : K)⁻¹ * (n : K)⁻¹) * 2 := by
      have hsub0 : ((k : K) * (n : K)⁻¹ - ((n : K)⁻¹ * (n : K)⁻¹ * (n : K)⁻¹) * 2) • e = 0 := by
        rw [sub_smul, hk, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub0).resolve_right he_nz)
    have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
    have hmulK : (k : K) * (n : K) ^ 2 = 2 := by
      calc
        (k : K) * (n : K) ^ 2
          = ((k : K) * (n : K)⁻¹) * ((n : K) * (n : K) * (n : K)) := by
            field_simp [hnK]
        _ = (((n : K)⁻¹ * (n : K)⁻¹ * (n : K)⁻¹) * 2) * ((n : K) * (n : K) * (n : K)) := by
            rw [hcoeff_eq]
        _ = 2 := by
            field_simp [hnK]
    have hmulZ : k * (n : ℤ) ^ 2 = 2 := by
      apply Int.cast_injective (α := K)
      push_cast
      exact hmulK
    by_contra hne1
    have hn2 : 2 ≤ (n : ℤ) := by omega
    have hsq : 4 ≤ (n : ℤ) ^ 2 := by nlinarith
    rcases le_or_gt k 0 with hk0 | hk1 <;> nlinarith
  have hroot_inter : ∀ α : H.root,
      L_V ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {x (α : Weight K H L)} := by
    intro α
    have hα_nz : (α : Weight K H L).IsNonZero := H.isNonZero_coe_root α
    let e := x (α : Weight K H L)
    let f := x (-(α : Weight K H L))
    let I_α := L_V ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ
    have he_mem_R : e ∈ rootSpace H (α : H → K) := hx.toIsSl2System.mem_rootSpace _
    have he_nz_sub : (⟨e, he_mem_R⟩ : rootSpace H (α : H → K)) ≠ 0 := by
      intro h0
      exact hx.toIsSl2System.ne_zero (α : Weight K H L) hα_nz (congrArg Subtype.val h0)
    have hone : Module.finrank K (rootSpace H (α : H → K)) = 1 :=
      IsKilling.finrank_rootSpace_eq_one (α : Weight K H L) hα_nz
    have hspan_le : Submodule.span ℤ {e} ≤ I_α := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hx_wt_mem_LV (α : Weight K H L), he_mem_R⟩
    have hhalf_int : ∀ y ∈ I_α, ∃ k : ℤ, y = ((k : K) * (2 : K)⁻¹) • e := by
      intro y hy
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ he_nz_sub).mp hone ⟨y, hy.2⟩
      have hy_eq : y = c • e := (congrArg Subtype.val hc).symm
      have hbr_mem : ⁅y, f⁆ ∈ L_V := hbracket y hy.1 f (hx_wt_mem_LV (-(α : Weight K H L)))
      have ht : IsSl2Triple ((coroot (α : Weight K H L) : H) : L) e f :=
        hx.toIsSl2System.isSl2Triple (α : Weight K H L) hα_nz
      have hbr_eq : ⁅y, f⁆ = ((c • coroot (α : Weight K H L) : H) : L) := by
        rw [hy_eq, smul_lie, ht.lie_e_f]
        rfl
      have hc_inter : ((c • coroot (α : Weight K H L) : H) : L) ∈
          L_V ⊓ H.toSubmodule.restrictScalars ℤ :=
        ⟨hbr_eq ▸ hbr_mem, (c • coroot (α : Weight K H L)).2⟩
      rw [hHV_eq] at hc_inter
      obtain ⟨h', hh', hh'_eq⟩ := hc_inter
      have hh'_val : h' = c • coroot (α : Weight K H L) := Subtype.ext hh'_eq
      rw [hh'_val] at hh'
      obtain ⟨k, hk⟩ := (mem_cartanWeightDualSubmodule_iff _).mp hh'
        ((rootSystem H).root α) (h_rl_le (Submodule.subset_span ⟨α, rfl⟩))
      rw [map_smul, rootSystem_root_apply, Weight.toLinear_apply,
        IsKilling.root_apply_coroot hα_nz, smul_eq_mul] at hk
      have hc_val : c = (k : K) * (2 : K)⁻¹ := by
        have h2 : (2 : K) ≠ 0 := two_ne_zero' K
        calc
          c = (c * 2) * (2 : K)⁻¹ := by field_simp [h2]
          _ = (k : K) * (2 : K)⁻¹ := by rw [← hk]
      exact ⟨k, hy_eq.trans (by rw [hc_val])⟩
    by_cases hle_one : I_α ≤ Submodule.span ℤ {e}
    · exact le_antisymm hle_one hspan_le
    · exfalso
      have hex_not : ∃ y₀ ∈ I_α, y₀ ∉ Submodule.span ℤ {e} := by
        by_contra hall
        push Not at hall
        exact hle_one hall
      obtain ⟨y₀, hy₀_I, hy₀_not⟩ := hex_not
      obtain ⟨k₀, hk₀⟩ := hhalf_int y₀ hy₀_I
      have hk₀_odd : k₀ % 2 = 1 := by
        have hmod := Int.emod_two_eq_zero_or_one k₀
        rcases hmod with h0 | h1
        · exfalso
          apply hy₀_not
          let q : ℤ := k₀ / 2
          have hk_eq : k₀ = 2 * q := by omega
          have hy_q : y₀ = q • e := by
            rw [hk₀, hk_eq]
            push_cast
            have h2 : (2 : K) ≠ 0 := two_ne_zero' K
            have hsimp : 2 * (q : K) * (2 : K)⁻¹ = (q : K) := by field_simp [h2]
            rw [hsimp, Int.cast_smul_eq_zsmul]
          rw [hy_q, Submodule.mem_span_singleton]
          exact ⟨q, rfl⟩
        · exact h1
      let q₀ : ℤ := k₀ / 2
      have hk₀_decomp : k₀ = 2 * q₀ + 1 := by omega
      have hhalf_mem : ((2 : ℕ) : K)⁻¹ • e ∈ I_α := by
        have hqe_mem : q₀ • e ∈ I_α := hspan_le (Submodule.mem_span_singleton.mpr ⟨q₀, rfl⟩)
        have hdiff_mem : y₀ - q₀ • e ∈ I_α := I_α.sub_mem hy₀_I hqe_mem
        have hdiff_eq : y₀ - q₀ • e = ((2 : ℕ) : K)⁻¹ • e := by
          rw [hk₀, hk₀_decomp, ← Int.cast_smul_eq_zsmul K q₀, ← sub_smul]
          congr 1
          push_cast
          have h2 : (2 : K) ≠ 0 := two_ne_zero' K
          field_simp [h2]
          ring
        rwa [← hdiff_eq]
      have hspan_two : I_α = Submodule.span ℤ {((2 : ℕ) : K)⁻¹ • e} := by
        apply le_antisymm
        · intro y hy
          obtain ⟨k, hk⟩ := hhalf_int y hy
          rw [hk, Submodule.mem_span_singleton]
          refine ⟨k, ?_⟩
          rw [← Int.cast_smul_eq_zsmul K k, smul_smul, Nat.cast_two]
        · rw [Submodule.span_singleton_le_iff_mem]
          exact hhalf_mem
      have h2_eq_1 : (2 : ℕ) = 1 := hdiv_excl α 2 (by omega) hspan_two
      omega
  -- (4) Decomposition `L_V = (L_V ⊓ H) ⊔ ⨆ α, ℤ x_α`, disjointness, and independence
  have hLV_decomp_wt :=
    (Humphreys27_1.weightSpace_inter_directSum_of_isKostantInvariant hx L_V.toAddSubgroup hLV_inv).1
  have hLV_eq_sup : L_V =
      (L_V ⊓ H.toSubmodule.restrictScalars ℤ) ⊔
        (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ (⨆ χ : Weight K H L,
          L_V.toAddSubgroup ⊓ (LieModule.weightSpace L (χ : H → K)).toSubmodule.toAddSubgroup) :=
        hLV_decomp_wt.symm ▸ hy
      let R_rhs : Submodule ℤ L :=
        (L_V ⊓ H.toSubmodule.restrictScalars ℤ) ⊔
          (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)})
      have hle_rhs : (⨆ χ : Weight K H L,
          L_V.toAddSubgroup ⊓ (LieModule.weightSpace L (χ : H → K)).toSubmodule.toAddSubgroup) ≤
          R_rhs.toAddSubgroup := by
        refine iSup_le fun χ z hz => ?_
        by_cases hχ : χ.IsNonZero
        · let α : H.root := ⟨χ, by simpa using hχ⟩
          have hz_root : z ∈ L_V ⊓ (rootSpace H (α : H → K)).toSubmodule.restrictScalars ℤ := by
            refine ⟨hz.1, ?_⟩
            change z ∈ LieModule.genWeightSpace L (χ : H → K)
            rw [TauCeti.genWeightSpace_eq_weightSpace]
            exact hz.2
          rw [hroot_inter α] at hz_root
          exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem α hz_root)
        · have hχ0 : (χ : H → K) = 0 := not_not.mp hχ
          have hz_H : z ∈ H := by
            have hz_gen : z ∈ LieModule.genWeightSpace L (χ : H → K) := by
              rw [TauCeti.genWeightSpace_eq_weightSpace]
              exact hz.2
            rw [hχ0] at hz_gen
            have hz_r0 : z ∈ rootSpace H 0 := hz_gen
            rwa [LieAlgebra.rootSpace_zero_eq K L H, LieSubalgebra.mem_toLieSubmodule] at hz_r0
          exact Submodule.mem_sup_left ⟨hz.1, hz_H⟩
      exact hle_rhs hy'
    · refine sup_le inf_le_left (iSup_le fun α => ?_)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hx_wt_mem_LV (α : Weight K H L)
  have hK_indep : iSupIndep (fun μ : H → K => (LieModule.genWeightSpace L μ).toSubmodule) :=
    LieSubmodule.iSupIndep_toSubmodule.mpr (LieModule.iSupIndep_genWeightSpace K H L)
  have hdisj : Disjoint
      (L_V ⊓ H.toSubmodule.restrictScalars ℤ)
      (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) := by
    rw [Submodule.disjoint_def]
    intro y hyH hyR
    have hy0 : y ∈ (LieModule.genWeightSpace L (0 : H → K)).toSubmodule := by
      have hy_sub : y ∈ H := hyH.2
      rw [← LieSubalgebra.mem_toLieSubmodule, ← LieAlgebra.rootSpace_zero_eq K L H] at hy_sub
      exact hy_sub
    have hy_other : y ∈ ⨆ μ : H → K, ⨆ (_ : μ ≠ 0), (LieModule.genWeightSpace L μ).toSubmodule := by
      have hle : (⨆ α : H.root, Submodule.span ℤ {x (α : Weight K H L)}) ≤
          (⨆ μ : H → K, ⨆ (_ : μ ≠ 0),
            (LieModule.genWeightSpace L μ).toSubmodule).restrictScalars ℤ := by
        refine iSup_le fun α => ?_
        rw [Submodule.span_singleton_le_iff_mem]
        exact Submodule.mem_iSup_of_mem ((α : Weight K H L) : H → K)
          (Submodule.mem_iSup_of_mem (H.isNonZero_coe_root α)
            (hx.toIsSl2System.mem_rootSpace (α : Weight K H L)))
      exact hle hyR
    exact Submodule.disjoint_def.mp (hK_indep 0) y hy0 hy_other
  have hindep_roots : iSupIndep (fun α : H.root => Submodule.span ℤ {x (α : Weight K H L)}) := by
    intro α
    rw [Submodule.disjoint_def]
    intro y hyα hy_other
    have hy_gen_α : y ∈ (LieModule.genWeightSpace L ((α : Weight K H L) : H → K)).toSubmodule := by
      have hle : Submodule.span ℤ {x (α : Weight K H L)} ≤
          ((LieModule.genWeightSpace L ((α : Weight K H L) : H → K)).toSubmodule).restrictScalars ℤ := by
        rw [Submodule.span_singleton_le_iff_mem]
        exact hx.toIsSl2System.mem_rootSpace (α : Weight K H L)
      exact hle hyα
    have hy_gen_other : y ∈ ⨆ μ : H → K, ⨆ (_ : μ ≠ ((α : Weight K H L) : H → K)),
        (LieModule.genWeightSpace L μ).toSubmodule := by
      have hle : (⨆ β : H.root, ⨆ (_ : β ≠ α), Submodule.span ℤ {x (β : Weight K H L)}) ≤
          (⨆ μ : H → K, ⨆ (_ : μ ≠ ((α : Weight K H L) : H → K)),
            (LieModule.genWeightSpace L μ).toSubmodule).restrictScalars ℤ := by
        refine iSup_le fun β => iSup_le fun hβα => ?_
        rw [Submodule.span_singleton_le_iff_mem]
        have hfn_ne : ((β : Weight K H L) : H → K) ≠ ((α : Weight K H L) : H → K) := by
          intro hfn
          apply hβα
          apply Subtype.ext
          apply Weight.ext
          intro h
          exact congrFun hfn h
        exact Submodule.mem_iSup_of_mem ((β : Weight K H L) : H → K)
          (Submodule.mem_iSup_of_mem hfn_ne (hx.toIsSl2System.mem_rootSpace (β : Weight K H L)))
      exact hle hy_other
    exact Submodule.disjoint_def.mp (hK_indep ((α : Weight K H L) : H → K)) y hy_gen_α hy_gen_other
  -- (2b) `IsFullZLattice K L_V`
  have hLV_full : Humphreys27_1.IsFullZLattice K L_V := by
    obtain ⟨bH, hbH⟩ := hHV_full
    obtain ⟨b⟩ := (rootSystem H).nonempty_base
    let vL : H.root ⊕ Fin (Module.finrank K H) → L :=
      Sum.elim (fun α => x (α : Weight K H L)) (fun i => (bH i : L))
    have hrange_vL : Set.range vL =
        (Set.range fun α : H.root => x (α : Weight K H L)) ∪
          (H.toSubmodule.subtype '' Set.range bH) := by
      ext y
      simp only [vL, Set.mem_range, Set.mem_union, Set.mem_image, Sum.exists, Sum.elim_inl,
        Sum.elim_inr, Submodule.coe_subtype]
      constructor
      · rintro (⟨α, rfl⟩ | ⟨i, rfl⟩)
        · exact Or.inl ⟨α, rfl⟩
        · exact Or.inr ⟨bH i, ⟨i, rfl⟩, rfl⟩
      · rintro (⟨α, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩)
        · exact Or.inl ⟨α, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
    have hspan_vL_Z : Submodule.span ℤ (Set.range vL) = L_V := by
      rw [hrange_vL, Submodule.span_union, Submodule.span_range_eq_iSup]
      have hmap_H : Submodule.span ℤ ((H.toSubmodule.subtype : H → L) '' Set.range bH) =
          L_V ⊓ H.toSubmodule.restrictScalars ℤ := by
        have hm := Submodule.map_span (H.toSubmodule.restrictScalars ℤ).subtype (Set.range bH)
        have hm' : Submodule.map (H.toSubmodule.restrictScalars ℤ).subtype
            (cartanWeightDualSubmodule H V) =
            Submodule.span ℤ ((H.toSubmodule.subtype : H → L) '' Set.range bH) := by
          rw [hbH]
          exact hm
        exact hm'.symm.trans hHV_eq.symm
      rw [hmap_H, sup_comm, ← hLV_eq_sup]
    have hspan_vL_K : Submodule.span K (Set.range vL) = ⊤ := by
      rw [← top_le_iff, ← (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).span_eq,
        Submodule.span_le]
      rintro _ ⟨s, rfl⟩
      rcases s with α | i
      · rw [Humphreys26_4.GapB.chevalleyAmbientBasis_inl]
        exact Submodule.subset_span ⟨Sum.inl α, rfl⟩
      · rw [Humphreys26_4.GapB.chevalleyAmbientBasis_inr]
        have hc_top : (rootSystem H).coroot i.1 ∈ Submodule.span K (Set.range bH) := by
          rw [bH.span_eq]; trivial
        have hmap_K := Submodule.mem_map_of_mem (f := H.toSubmodule.subtype) hc_top
        rw [Submodule.map_span] at hmap_K
        refine Submodule.span_mono ?_ hmap_K
        rw [hrange_vL]
        exact Set.subset_union_right
    have hcoroot_li : LinearIndependent K (fun i : ↥b.support => (rootSystem H).coroot i.1) := by
      refine LinearIndependent.of_comp H.toSubmodule.subtype ?_
      have hcomp : (H.toSubmodule.subtype ∘ fun i : ↥b.support => (rootSystem H).coroot i.1) =
          (Humphreys26_4.GapB.chevalleyAmbientBasis hx b) ∘ Sum.inr := by
        funext i
        simp [Humphreys26_4.GapB.chevalleyAmbientBasis_inr]
      rw [hcomp]
      exact (Humphreys26_4.GapB.chevalleyAmbientBasis hx b).linearIndependent.comp
        Sum.inr Sum.inr_injective
    have hcoroot_span : ⊤ ≤ Submodule.span K (Set.range fun i : ↥b.support =>
        (rootSystem H).coroot i.1) := by
      rw [← RootPairing.IsRootSystem.span_coroot_eq_top (P := rootSystem H), Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      have hmem_Z := b.coroot_mem_span_int α
      refine Submodule.span_induction ?_ (Submodule.zero_mem _)
        (fun _ _ _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂)
        (fun z _ _ h₁ => Submodule.smul_mem _ (z : K) h₁ |> fun hm => by
          rwa [Int.cast_smul_eq_zsmul] at hm) hmem_Z
      rintro _ ⟨r, hr, rfl⟩
      exact Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩
    let bSuppH : Module.Basis ↥b.support K H := Module.Basis.mk hcoroot_li hcoroot_span
    have hcard_H : Fintype.card ↥b.support = Module.finrank K H :=
      (Module.finrank_eq_card_basis bSuppH).symm
    have hcard_L : Fintype.card (H.root ⊕ ↥b.support) = Module.finrank K L :=
      (Module.finrank_eq_card_basis (Humphreys26_4.GapB.chevalleyAmbientBasis hx b)).symm
    have hcard_vL : Fintype.card (H.root ⊕ Fin (Module.finrank K H)) = Module.finrank K L := by
      rw [Fintype.card_sum, Fintype.card_fin, ← hcard_H, ← Fintype.card_sum, hcard_L]
    have hli_vL : LinearIndependent K vL :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan_vL_K.ge hcard_vL
    let eIdx : (H.root ⊕ Fin (Module.finrank K H)) ≃ Fin (Module.finrank K L) :=
      Fintype.equivOfCardEq (hcard_vL.trans (Fintype.card_fin _).symm)
    let bL : Module.Basis (Fin (Module.finrank K L)) K L :=
      (Module.Basis.mk hli_vL hspan_vL_K.ge).reindex eIdx
    refine ⟨bL, ?_⟩
    have hr_bL : Set.range bL = Set.range vL := by
      ext y
      simp [bL]
    rw [hr_bL, hspan_vL_Z]
  exact ⟨hbracket, ⟨hLV_full, hLV_inv⟩, hroot_inter, hLV_eq_sup, hdisj, hindep_roots⟩

/-- **Humphreys, Proposition 27.2 — Independence of `M` and dependence only on `Λ(V)` (p. 160):**
If two faithful finite-dimensional `L`-modules `V₁`, `V₂` have the same weight lattice
`Λ(V₁) = Λ(V₂)`, then for any admissible lattices `M₁ ⊂ V₁` and `M₂ ⊂ V₂`,
`stabilizerLattice M₁ = stabilizerLattice M₂` (in particular, for `V₁ = V₂ = V`, `L_V` does
not depend on the choice of admissible lattice `M`). -/
theorem stabilizerLattice_eq_of_moduleWeightLattice_eq
    {V₁ : Type w} [AddCommGroup V₁] [Module K V₁] [LieRingModule L V₁] [LieModule K L V₁]
    [FiniteDimensional K V₁] [LieModule.IsFaithful K L V₁]
    {V₂ : Type w'} [AddCommGroup V₂] [Module K V₂] [LieRingModule L V₂] [LieModule K L V₂]
    [FiniteDimensional K V₂] [LieModule.IsFaithful K L V₂]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M₁ : Submodule ℤ V₁) (hM₁ : Humphreys27_1.IsAdmissibleLattice H x M₁)
    (M₂ : Submodule ℤ V₂) (hM₂ : Humphreys27_1.IsAdmissibleLattice H x M₂)
    (hΛ : moduleWeightLattice H V₁ = moduleWeightLattice H V₂) :
    stabilizerLattice L M₁ = stabilizerLattice L M₂ := by
  have hdual_eq : cartanWeightDualSubmodule H V₁ = cartanWeightDualSubmodule H V₂ := by
    ext h
    rw [mem_cartanWeightDualSubmodule_iff, mem_cartanWeightDualSubmodule_iff, hΛ]
  have hH₁ := (cartanStabilizer_eq_weightDual_and_isFullZLattice hx M₁ hM₁).1
  have hH₂ := (cartanStabilizer_eq_weightDual_and_isFullZLattice hx M₂ hM₂).1
  have hD₁ := (isAdmissibleLattice_stabilizerLattice_and_decomposition hx M₁ hM₁).2.2.2.1
  have hD₂ := (isAdmissibleLattice_stabilizerLattice_and_decomposition hx M₂ hM₂).2.2.2.1
  rw [hD₁, hD₂, hH₁, hH₂, hdual_eq]

end StabilizerLattice

end Humphreys27_2
