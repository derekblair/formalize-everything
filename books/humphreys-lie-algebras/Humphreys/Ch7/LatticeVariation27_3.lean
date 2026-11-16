import TauCeti.Algebra.Lie.Dual
import TauCeti.Algebra.Lie.HighestWeight.Dual
import TauCeti.Algebra.Lie.HighestWeight.LowestWeight
import TauCeti.Algebra.Lie.UniversalEnveloping.Dual
import TauCeti.LinearAlgebra.Dual.Lattice
import Humphreys.Ch7.AdmissibleLattice27_1

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti

universe u v w

namespace Humphreys27_3

variable {K : Type u} {L : Type v} {V : Type w}
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Humphreys Exercise 21.6 (p. 116) as invoked in §27.3 (p. 161):**
For any dominant integral weight `lam ∈ Λ⁺`, the contragredient module `V(lam)*` is isomorphic
as an `L`-module to `V(-w₀ lam)`, where `w₀ = TauCeti.longestElement (rootSystem H) b` is the
unique Weyl group element sending `Δ` to `-Δ`. -/
theorem nonempty_lieModuleEquiv_dual_irreducibleQuotient
    (b : (rootSystem H).Base) {lam : Module.Dual K H}
    (hlam : TauCeti.IsDominantIntegral b lam) :
    Nonempty
      (Module.Dual K (TauCeti.irreducibleQuotient b lam) ≃ₗ⁅K,L⁆
        TauCeti.irreducibleQuotient b
          (-(TauCeti.longestElement (rootSystem H) b • lam))) := by
  have : FiniteDimensional K (TauCeti.irreducibleQuotient b lam) :=
    TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  have hv := TauCeti.isHighestWeightVector_irreducibleQuotientGenerator b lam
  obtain ⟨f, hf⟩ := TauCeti.exists_isHighestWeightVector_dual hv
  have := TauCeti.LieModule.isIrreducible_dual (K := K) (L := L)
    (M := TauCeti.irreducibleQuotient b lam)
  exact TauCeti.nonempty_lieModuleEquiv_of_isHighestWeightVector hf
    (TauCeti.isHighestWeightVector_irreducibleQuotientGenerator b
      (-(TauCeti.longestElement (rootSystem H) b • lam)))

/-- **Pre-dual (bidual pullback) lattice `{v ∈ V | ∀ φ ∈ N, φ(v) ∈ ℤ}` (`D27.3`, H pp. 161–162):**
pulls a `ℤ`-submodule `N` of `V* = Module.Dual K V` back to `V` along canonical evaluation,
realizing `((M^*)_min)^*` directly inside `V`. -/
def preDualLattice (K : Type u) {W : Type w} [Field K] [AddCommGroup W] [Module K W]
    (N : Submodule ℤ (Module.Dual K W)) : Submodule ℤ W :=
  ⨅ φ : N, (1 : Submodule ℤ K).comap ((φ.1 : Module.Dual K W).restrictScalars ℤ)

omit [CharZero K] in
private theorem mem_preDualLattice {W : Type w} [AddCommGroup W] [Module K W]
    (N : Submodule ℤ (Module.Dual K W)) (y : W) :
    y ∈ preDualLattice K N ↔ ∀ φ ∈ N, (φ : Module.Dual K W) y ∈ (1 : Submodule ℤ K) := by
  simp [preDualLattice]

omit [CharZero K] in
private theorem preDualLattice_antitone {W : Type w} [AddCommGroup W] [Module K W] :
    Antitone (preDualLattice K (W := W)) := by
  intro N₁ N₂ h y hy
  exact (mem_preDualLattice N₁ y).mpr fun φ hφ => (mem_preDualLattice N₂ y).mp hy φ (h hφ)

omit [CharZero K] in
private theorem isFullZLattice_dualLattice_and_preDualLattice_eq
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {M : Submodule ℤ W} (hM : Humphreys27_1.IsFullZLattice K M) :
    Humphreys27_1.IsFullZLattice K (M.dualLattice K) ∧
      preDualLattice K (M.dualLattice K) = M := by
  obtain ⟨bW, rfl⟩ := hM
  have hdual : (Submodule.span ℤ (Set.range bW)).dualLattice K =
      Submodule.span ℤ (Set.range bW.dualBasis) := bW.dualLattice_span
  refine ⟨?_, ?_⟩
  · let bDual : Module.Basis (Fin (Module.finrank K (Module.Dual K W))) K (Module.Dual K W) :=
      bW.dualBasis.reindex (finCongr Subspace.dual_finrank_eq.symm)
    refine ⟨bDual, ?_⟩
    rw [hdual]
    have hrange : Set.range bDual = Set.range bW.dualBasis := by
      ext φ
      simp [bDual]
    rw [hrange]
  · apply le_antisymm
    · intro y hy
      rw [← bW.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hφ_mem : bW.dualBasis i ∈ (Submodule.span ℤ (Set.range bW)).dualLattice K := by
        rw [hdual]
        exact Submodule.subset_span ⟨i, rfl⟩
      have hint : bW.dualBasis i y ∈ (1 : Submodule ℤ K) :=
        (mem_preDualLattice _ y).mp hy _ hφ_mem
      obtain ⟨z, hz⟩ := Submodule.mem_one.mp hint
      have hrepr : bW.repr y i = algebraMap ℤ K z := by
        rw [← bW.dualBasis_apply, hz]
      rw [hrepr, algebraMap_smul]
      exact Submodule.smul_mem _ z (Submodule.subset_span ⟨i, rfl⟩)
    · intro y hy
      exact (mem_preDualLattice _ y).mpr fun φ hφ =>
        (Submodule.mem_dualLattice _ φ).mp hφ y hy

omit [CharZero K] in
private theorem isFullZLattice_preDualLattice_and_dualLattice_eq
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {N : Submodule ℤ (Module.Dual K W)} (hN : Humphreys27_1.IsFullZLattice K N) :
    Humphreys27_1.IsFullZLattice K (preDualLattice K N) ∧
      (preDualLattice K N).dualLattice K = N := by
  obtain ⟨bN, rfl⟩ := hN
  let bN' : Module.Basis (Fin (Module.finrank K W)) K (Module.Dual K W) :=
    bN.reindex (finCongr Subspace.dual_finrank_eq)
  have hrange_bN' : Set.range bN' = Set.range bN := by
    ext φ
    simp [bN']
  let bW : Module.Basis (Fin (Module.finrank K W)) K W :=
    bN'.dualBasis.map (Module.evalEquiv K W).symm
  have hbW_dual : bW.dualBasis = bN' := by
    ext j : 1
    refine bW.ext fun i => ?_
    rw [bW.dualBasis_apply_self]
    have hval : bN' j (bW i) = bN'.dualBasis i (bN' j) := by
      dsimp [bW]
      exact Module.apply_evalEquiv_symm_apply (R := K) (M := W) (bN' j) (bN'.dualBasis i)
    rw [hval, bN'.dualBasis_apply_self]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  let M₀ : Submodule ℤ W := Submodule.span ℤ (Set.range bW)
  have hM₀_full : Humphreys27_1.IsFullZLattice K M₀ := ⟨bW, rfl⟩
  have hM₀_dual : M₀.dualLattice K = Submodule.span ℤ (Set.range bN) := by
    dsimp [M₀]
    rw [bW.dualLattice_span, hbW_dual, hrange_bN']
  have hpre : preDualLattice K (Submodule.span ℤ (Set.range bN)) = M₀ := by
    rw [← hM₀_dual]
    exact (isFullZLattice_dualLattice_and_preDualLattice_eq hM₀_full).2
  rw [hpre]
  exact ⟨hM₀_full, hM₀_dual⟩

private noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat

omit [LieAlgebra.IsKilling K L] in
private theorem antipode_mem_kostantSubring (x : Weight K H L → L)
    {u : _root_.UniversalEnvelopingAlgebra K L}
    (hu : u ∈ Humphreys26_4.kostantSubring H x) :
    _root_.UniversalEnvelopingAlgebra.antipode K u ∈ Humphreys26_4.kostantSubring H x := by
  have hle : Humphreys26_4.kostantSubring H x ≤
      _root_.UniversalEnvelopingAlgebra.antipodeComap K (Humphreys26_4.kostantSubring H x) := by
    rw [Humphreys26_4.kostantSubring, Subring.closure_le]
    rintro _ ⟨⟨α, t⟩, rfl⟩
    rw [SetLike.mem_coe, _root_.UniversalEnvelopingAlgebra.mem_antipodeComap]
    let a : _root_.UniversalEnvelopingAlgebra K L :=
      _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))
    have hdp_eq : ∀ y : _root_.UniversalEnvelopingAlgebra K L,
        TauCeti.Associative.dividedPower t y =
          (algebraMap ℚ K (t.factorial : ℚ)⁻¹) • y ^ t := by
      intro y
      rw [TauCeti.Associative.dividedPower_def, Algebra.smul_def, Algebra.smul_def]
      rfl
    have hneg_pow : ∀ k : ℕ, (-a) ^ k = (-1 : ℤ) ^ k • a ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', pow_succ', pow_succ', ih, neg_one_mul, neg_zsmul,
          mul_smul_comm, neg_mul, smul_neg]
    have hant : _root_.UniversalEnvelopingAlgebra.antipode K
        (TauCeti.Associative.dividedPower t a) =
        (-1 : ℤ) ^ t • TauCeti.Associative.dividedPower t a := by
      rw [hdp_eq a, LinearMap.map_smul, _root_.UniversalEnvelopingAlgebra.antipode_pow,
        _root_.UniversalEnvelopingAlgebra.antipode_ι, hneg_pow t, smul_comm]
    rw [hant]
    have hmem_gen : TauCeti.Associative.dividedPower t a ∈ Humphreys26_4.kostantSubring H x :=
      Subring.subset_closure ⟨(α, t), rfl⟩
    exact zsmul_mem hmem_gen _
  exact hle hu

variable [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

omit [LieAlgebra.IsKilling K L] in
private theorem isKostantInvariant_dualLattice (x : Weight K H L → L)
    {M : Submodule ℤ V} (hM : Humphreys27_1.IsKostantInvariant H x M) :
    Humphreys27_1.IsKostantInvariant H x (M.dualLattice K) := by
  intro u hu φ hφ
  refine (Submodule.mem_dualLattice M _).mpr fun m hm => ?_
  rw [_root_.UniversalEnvelopingAlgebra.representation_dual_apply]
  exact (Submodule.mem_dualLattice M φ).mp hφ _
    (hM _ (antipode_mem_kostantSubring x hu) m hm)

omit [LieAlgebra.IsKilling K L] in
private theorem isKostantInvariant_preDualLattice (x : Weight K H L → L)
    {N : Submodule ℤ (Module.Dual K V)} (hN : Humphreys27_1.IsKostantInvariant H x N) :
    Humphreys27_1.IsKostantInvariant H x (preDualLattice K N) := by
  intro u hu m hm
  refine (mem_preDualLattice N _).mpr fun φ hφ => ?_
  have hφ' : TauCeti.UniversalEnvelopingAlgebra.representation K L (Module.Dual K V)
      (_root_.UniversalEnvelopingAlgebra.antipode K u) φ ∈ N :=
    hN _ (antipode_mem_kostantSubring x hu) φ hφ
  have heval := (mem_preDualLattice N m).mp hm _ hφ'
  rw [_root_.UniversalEnvelopingAlgebra.representation_dual_apply] at heval
  have hant : HopfAlgebra.antipode K (_root_.UniversalEnvelopingAlgebra.antipode K u) = u := by
    change _root_.UniversalEnvelopingAlgebra.antipode K
      (_root_.UniversalEnvelopingAlgebra.antipode K u) = u
    exact _root_.UniversalEnvelopingAlgebra.antipode_antipode K u
  rwa [hant] at heval

/-- **Humphreys §27.3 dual-lattice admissibility & biduality (p. 161):**
If `M` is an admissible lattice in a finite-dimensional `L`-module `V`, then its integral dual
`M.dualLattice K = {f ∈ V* | f(M) ⊆ ℤ}` is an admissible lattice in the contragredient module
`Module.Dual K V`, and `preDualLattice K (M.dualLattice K) = M`. -/
theorem isAdmissibleLattice_dualLattice_and_preDual
    [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M) :
    Humphreys27_1.IsAdmissibleLattice H x (M.dualLattice K) ∧
      preDualLattice K (M.dualLattice K) = M := by
  let _ := hx
  obtain ⟨hfull, hpre⟩ := isFullZLattice_dualLattice_and_preDualLattice_eq hM.1
  exact ⟨⟨hfull, isKostantInvariant_dualLattice x hM.2⟩, hpre⟩

/-- **Minimal admissible lattice `(M*)_min ⊂ V*` (`D27.3`, H pp. 161–162):**
canonical `𝔘_ℤ`-orbit in `Module.Dual K V` of the rank-1 dual highest-weight intersection
`(M_min)* ∩ (V*)_{-w₀ λ} = ℤ f⁺` (independent of the `±1` sign choice of `f⁺`). -/
noncomputable def dualMinAdmissibleLattice
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (b : (rootSystem H).Base) (x : Weight K H L → L)
    (lam : Module.Dual K H) (v : V) : Submodule ℤ (Module.Dual K V) :=
  Subring.orbitOfRep (Humphreys26_4.kostantSubring H x)
    (TauCeti.UniversalEnvelopingAlgebra.representation K L (Module.Dual K V))
    (((Humphreys27_1.minAdmissibleLattice H x v).dualLattice K ⊓
      (LieModule.weightSpace (Module.Dual K V)
        ((-(TauCeti.longestElement (rootSystem H) b • lam) : Module.Dual K H) :
          H → K)).toSubmodule.restrictScalars ℤ) : Set (Module.Dual K V))

/-- **Maximal admissible lattice `M_max = ((M*)_min)* ⊂ V` (`D27.3`, H pp. 161–162):**
the lattice in `V` dual to `(M*)_min` in `V*`. -/
noncomputable def maxAdmissibleLattice
    (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
    (b : (rootSystem H).Base) (x : Weight K H L → L)
    (lam : Module.Dual K H) (v : V) : Submodule ℤ V :=
  preDualLattice K (dualMinAdmissibleLattice H b x lam v)

private noncomputable local instance instAlgebraRatEnd {W : Type*} [AddCommGroup W] [Module K W] :
    Algebra ℚ (Module.End K W) :=
  Algebra.compHom (Module.End K W) (algebraMap ℚ K)

private noncomputable def simpleWeylUnit [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (i : H.root) : (Module.End K V)ˣ :=
  let α_wt : Weight K H L := (i : Weight K H L)
  have hα_ne : (α_wt : H → K) ≠ 0 := H.isNonZero_coe_root i
  have hneg_ne : ((-α_wt : Weight K H L) : H → K) ≠ 0 := by
    rw [Weight.coe_neg]
    exact neg_ne_zero.mpr hα_ne
  TauCeti.weylUnit
    (LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hα_ne (hx.toIsSl2System.mem_rootSpace α_wt))
    (LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hneg_ne
      (hx.toIsSl2System.mem_rootSpace (-α_wt)))

private theorem dividedPower_toEnd_smul_mem_of_isKostantInvariant
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {M : Submodule ℤ V} (hM : Humphreys27_1.IsKostantInvariant H x M)
    (β : Weight K H L) (n : ℕ) {m : V} (hm : m ∈ M) :
    TauCeti.Associative.dividedPower n (LieModule.toEnd K L V (x β)) • m ∈ M := by
  let ρ := TauCeti.UniversalEnvelopingAlgebra.representation K L V
  have htoEnd : LieModule.toEnd K L V (x β) =
      ρ (_root_.UniversalEnvelopingAlgebra.ι K (x β)) := by
    ext y
    exact (TauCeti.UniversalEnvelopingAlgebra.representation_ι_apply K L V (x β) y).symm
  have hdp : TauCeti.Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι K (x β))) =
      ρ (TauCeti.Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x β))) := by
    rw [TauCeti.Associative.dividedPower_def, TauCeti.Associative.dividedPower_def,
      Algebra.smul_def, Algebra.smul_def, map_mul, map_pow]
    have hc : ρ ((algebraMap ℚ (_root_.UniversalEnvelopingAlgebra K L)) (n.factorial : ℚ)⁻¹) =
        (algebraMap ℚ (Module.End K V)) (n.factorial : ℚ)⁻¹ := by
      change ρ (algebraMap K (_root_.UniversalEnvelopingAlgebra K L)
        ((algebraMap ℚ K) (n.factorial : ℚ)⁻¹)) =
        algebraMap K (Module.End K V) ((algebraMap ℚ K) (n.factorial : ℚ)⁻¹)
      exact AlgHom.commutes ρ _
    rw [hc]
  rw [htoEnd, hdp]
  exact hM _ (Humphreys26_4.GapA.dividedPower_weight_mem_rootSubring hx β n) m hm

private theorem simpleWeylUnit_mem_and_inv_mem [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {M : Submodule ℤ V} (hM : Humphreys27_1.IsKostantInvariant H x M)
    (i : H.root) {m : V} (hm : m ∈ M) :
    ((simpleWeylUnit (V := V) hx i : (Module.End K V)ˣ) : Module.End K V) m ∈ M ∧
      (((simpleWeylUnit (V := V) hx i)⁻¹ : (Module.End K V)ˣ) : Module.End K V) m ∈ M := by
  let α_wt : Weight K H L := (i : Weight K H L)
  have hα_ne : (α_wt : H → K) ≠ 0 := H.isNonZero_coe_root i
  have hneg_ne : ((-α_wt : Weight K H L) : H → K) ≠ 0 := by
    rw [Weight.coe_neg]
    exact neg_ne_zero.mpr hα_ne
  have he_nil : _root_.IsNilpotent (LieModule.toEnd K L V (x α_wt)) :=
    LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hα_ne (hx.toIsSl2System.mem_rootSpace α_wt)
  have hf_nil : _root_.IsNilpotent (LieModule.toEnd K L V (x (-α_wt))) :=
    LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hneg_ne
      (hx.toIsSl2System.mem_rootSpace (-α_wt))
  have hE_dp : ∀ n, ∀ y ∈ M,
      TauCeti.Associative.dividedPower n (LieModule.toEnd K L V (x α_wt)) • y ∈ M :=
    fun n _ hy => dividedPower_toEnd_smul_mem_of_isKostantInvariant hx hM α_wt n hy
  have hF_dp : ∀ n, ∀ y ∈ M,
      TauCeti.Associative.dividedPower n (LieModule.toEnd K L V (x (-α_wt))) • y ∈ M :=
    fun n _ hy => dividedPower_toEnd_smul_mem_of_isKostantInvariant hx hM (-α_wt) n hy
  constructor
  · dsimp only [simpleWeylUnit]
    rw [TauCeti.coe_weylUnit, mul_apply_eq_comp, mul_apply_eq_comp]
    have h1 : IsNilpotent.exp (LieModule.toEnd K L V (x α_wt)) m ∈ M := by
      simpa only [one_zsmul, Module.End.smul_def] using
        TauCeti.exp_zsmul_smul_mem he_nil hE_dp 1 hm
    have h2 : IsNilpotent.exp (-LieModule.toEnd K L V (x (-α_wt)))
        (IsNilpotent.exp (LieModule.toEnd K L V (x α_wt)) m) ∈ M := by
      simpa only [neg_one_zsmul, Module.End.smul_def] using
        TauCeti.exp_zsmul_smul_mem hf_nil hF_dp (-1) h1
    simpa only [one_zsmul, Module.End.smul_def, α_wt] using
      TauCeti.exp_zsmul_smul_mem he_nil hE_dp 1 h2
  · dsimp only [simpleWeylUnit]
    rw [TauCeti.coe_inv_weylUnit, mul_apply_eq_comp, mul_apply_eq_comp]
    have h1 : IsNilpotent.exp (-LieModule.toEnd K L V (x α_wt)) m ∈ M := by
      simpa only [neg_one_zsmul, Module.End.smul_def] using
        TauCeti.exp_zsmul_smul_mem he_nil hE_dp (-1) hm
    have h2 : IsNilpotent.exp (LieModule.toEnd K L V (x (-α_wt)))
        (IsNilpotent.exp (-LieModule.toEnd K L V (x α_wt)) m) ∈ M := by
      simpa only [one_zsmul, Module.End.smul_def] using
        TauCeti.exp_zsmul_smul_mem hf_nil hF_dp 1 h1
    simpa only [neg_one_zsmul, Module.End.smul_def, α_wt] using
      TauCeti.exp_zsmul_smul_mem he_nil hE_dp (-1) h2

private theorem simpleWeylUnit_mem_weightSpace [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (i : H.root) {χ : Module.Dual K H} {z : V}
    (hz : z ∈ LieModule.weightSpace V (χ : H → K)) :
    ((simpleWeylUnit (V := V) hx i : (Module.End K V)ˣ) : Module.End K V) z ∈
        LieModule.weightSpace V ⇑((rootSystem H).reflection i χ) ∧
      (((simpleWeylUnit (V := V) hx i)⁻¹ : (Module.End K V)ˣ) : Module.End K V) z ∈
        LieModule.weightSpace V ⇑((rootSystem H).reflection i χ) := by
  let _ : LieAlgebra ℚ L := TauCeti.ratLieAlgebra K L
  let _ : LieRing (Module.End K V) := LieRing.ofAssociativeRing
  let _ : LieAlgebra K (Module.End K V) := LieAlgebra.ofAssociativeAlgebra
  let α_wt : Weight K H L := (i : Weight K H L)
  have hα : α_wt.IsNonZero := H.isNonZero_coe_root i
  have he_root : x α_wt ∈ rootSpace H α_wt := hx.toIsSl2System.mem_rootSpace α_wt
  have hf_root : x (-α_wt) ∈ rootSpace H (-α_wt) := hx.toIsSl2System.mem_rootSpace (-α_wt)
  have ht : IsSl2Triple ((coroot α_wt : H) : L) (x α_wt) (x (-α_wt)) :=
    hx.toIsSl2System.isSl2Triple α_wt hα
  have he_ad := (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (χ := ⇑α_wt) hα
    he_root).exists_pow_apply_eq_zero
  have hf_ad := (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (χ := ⇑(-α_wt)) hα.neg
    hf_root).exists_pow_apply_eq_zero
  have hneg_ne : ((-α_wt : Weight K H L) : H → K) ≠ 0 := by
    rw [Weight.coe_neg]
    exact neg_ne_zero.mpr hα
  have he_nil : _root_.IsNilpotent (LieModule.toEnd K L V (x α_wt)) :=
    LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hα he_root
  have hf_nil : _root_.IsNilpotent (LieModule.toEnd K L V (x (-α_wt))) :=
    LieModule.isNilpotent_toEnd_of_mem_rootSpace V H hneg_ne hf_root
  let φ : L →ₗ⁅K⁆ Module.End K V := LieModule.toEnd K L V
  let u : (Module.End K V)ˣ := simpleWeylUnit (V := V) hx i
  have hu_eq : u = TauCeti.weylUnit he_nil hf_nil := rfl
  have hz_lie : ∀ y : H, φ (y : L) z = χ y • z := by
    intro y
    have hmem := (LieModule.mem_weightSpace (χ : H → K) z).mp hz y
    simpa only [φ, LieModule.toEnd_apply_apply, H.coe_bracket_of_module] using hmem
  have hy'_act : ∀ y : H,
      φ ((y : L) - α_wt y • ((coroot α_wt : H) : L)) z =
        (((rootSystem H).reflection i χ) y) • z := by
    intro y
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hz_lie y,
      hz_lie (coroot α_wt), smul_smul, ← sub_smul, TauCeti.coe_rootSystem_reflection_apply]
    dsimp only [α_wt]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  constructor
  · refine (LieModule.mem_weightSpace _ _).mpr fun y => ?_
    have hye : ⁅(y : L), x α_wt⁆ = α_wt y • x α_wt := lie_eq_smul_of_mem_rootSpace he_root y
    have hyf : ⁅(y : L), x (-α_wt)⁆ = -(α_wt y • x (-α_wt)) := by
      simpa using lie_eq_smul_of_mem_rootSpace hf_root y
    have hconj := φ.map_weylAut_eq_weylUnit_conj ht he_ad hf_ad he_nil hf_nil
      ((y : L) - α_wt y • ((coroot α_wt : H) : L))
    rw [TauCeti.weylAut_apply_sub_smul he_ad hf_ad ht hye hyf, ← hu_eq] at hconj
    have happ := congrArg (fun f : Module.End K V => f ((u : Module.End K V) z)) hconj
    simp only [mul_apply_eq_comp] at happ
    have hcancel : ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((u : Module.End K V) z) = z := by
      rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq_self]
    rw [hcancel, hy'_act y, map_smul] at happ
    simpa only [φ, LieModule.toEnd_apply_apply, H.coe_bracket_of_module, u] using happ
  · refine (LieModule.mem_weightSpace _ _).mpr fun y => ?_
    have hye : ⁅(y : L), x α_wt⁆ = α_wt y • x α_wt := lie_eq_smul_of_mem_rootSpace he_root y
    have hyf : ⁅(y : L), x (-α_wt)⁆ = -(α_wt y • x (-α_wt)) := by
      simpa using lie_eq_smul_of_mem_rootSpace hf_root y
    have hconj := φ.map_weylAut_eq_weylUnit_conj ht he_ad hf_ad he_nil hf_nil (y : L)
    rw [TauCeti.weylAut_apply_of_lie_eq_smul he_ad hf_ad ht hye hyf, ← hu_eq] at hconj
    have happ := congrArg (fun f : Module.End K V =>
      ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) (f z)) hconj
    simp only [mul_apply_eq_comp] at happ
    have hcancel : ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V)
        ((u : Module.End K V) (φ (y : L) (((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) z))) =
        φ (y : L) (((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) z) := by
      rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq_self]
    rw [hy'_act y, map_smul, hcancel] at happ
    simpa only [φ, LieModule.toEnd_apply_apply, H.coe_bracket_of_module, u] using happ.symm

private noncomputable def wordWeylUnit [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {b : (rootSystem H).Base} (l : List b.support) : (Module.End K V)ˣ :=
  (l.map fun i : b.support => simpleWeylUnit (V := V) hx i.1).prod

private theorem wordWeylUnit_mem_and_inv_mem [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {M : Submodule ℤ V} (hM : Humphreys27_1.IsKostantInvariant H x M)
    {b : (rootSystem H).Base} (l : List b.support) :
    (∀ m ∈ M, ((wordWeylUnit (V := V) hx l : (Module.End K V)ˣ) : Module.End K V) m ∈ M) ∧
      (∀ m ∈ M, (((wordWeylUnit (V := V) hx l)⁻¹ : (Module.End K V)ˣ) : Module.End K V) m ∈ M) := by
  induction l with
  | nil =>
    simp [wordWeylUnit]
  | cons i tl ih =>
    constructor
    · intro m hm
      simp only [wordWeylUnit, List.map_cons, List.prod_cons, Units.val_mul, mul_apply_eq_comp]
      exact (simpleWeylUnit_mem_and_inv_mem hx hM i.1 (ih.1 m hm)).1
    · intro m hm
      simp only [wordWeylUnit, List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul,
        mul_apply_eq_comp]
      exact ih.2 _ (simpleWeylUnit_mem_and_inv_mem hx hM i.1 hm).2

private theorem wordWeylUnit_mem_weightSpace [FiniteDimensional K V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {b : (rootSystem H).Base} (l : List b.support) :
    (∀ (χ : Module.Dual K H) {z : V}, z ∈ LieModule.weightSpace V (χ : H → K) →
      ((wordWeylUnit (V := V) hx l : (Module.End K V)ˣ) : Module.End K V) z ∈
        LieModule.weightSpace V ⇑(TauCeti.wordProd (rootSystem H) b l • χ)) ∧
    (∀ (χ : Module.Dual K H) {z : V}, z ∈ LieModule.weightSpace V (χ : H → K) →
      (((wordWeylUnit (V := V) hx l)⁻¹ : (Module.End K V)ˣ) : Module.End K V) z ∈
        LieModule.weightSpace V ⇑((TauCeti.wordProd (rootSystem H) b l)⁻¹ • χ)) := by
  induction l with
  | nil =>
    simp [wordWeylUnit]
  | cons i tl ih =>
    constructor
    · intro χ z hz
      simp only [wordWeylUnit, List.map_cons, List.prod_cons, Units.val_mul, mul_apply_eq_comp,
        TauCeti.wordProd_cons, mul_smul, RootPairing.weylGroup.ofIdx_smul,
        RootPairing.Equiv.reflection_smul]
      exact (simpleWeylUnit_mem_weightSpace hx i.1 (ih.1 χ hz)).1
    · intro χ z hz
      simp only [wordWeylUnit, List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul,
        mul_apply_eq_comp, TauCeti.wordProd_cons, mul_smul, RootPairing.weylGroup.ofIdx_inv_eq]
      have hz' : (((simpleWeylUnit (V := V) hx i.1)⁻¹ : (Module.End K V)ˣ) : Module.End K V) z ∈
          LieModule.weightSpace V ⇑(RootPairing.weylGroup.ofIdx (rootSystem H) i.1 • χ) := by
        rw [RootPairing.weylGroup.ofIdx_smul, RootPairing.Equiv.reflection_smul]
        exact (simpleWeylUnit_mem_weightSpace hx i.1 hz).2
      exact ih.2 _ hz'

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L] in
private theorem dual_weightSpace_eval_eq_zero
    {η ξ : H → K} (hne : η ≠ -ξ) {ψ : Module.Dual K V}
    (hψ : ψ ∈ LieModule.weightSpace (Module.Dual K V) η)
    {m : V} (hm : m ∈ LieModule.weightSpace V ξ) :
    ψ m = 0 := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  have hψ_lie : ⁅(y : L), ψ⁆ = η y • ψ := by
    have hmem := (LieModule.mem_weightSpace η ψ).mp hψ y
    simpa only [LieModule.toEnd_apply_apply, H.coe_bracket_of_module] using hmem
  have hm_lie : ⁅(y : L), m⁆ = ξ y • m := by
    have hmem := (LieModule.mem_weightSpace ξ m).mp hm y
    simpa only [LieModule.toEnd_apply_apply, H.coe_bracket_of_module] using hmem
  have h1 : ⁅(y : L), ψ⁆ m = η y * ψ m := by
    rw [hψ_lie, LinearMap.smul_apply, smul_eq_mul]
  have h2 : ⁅(y : L), ψ⁆ m = -(ξ y * ψ m) := by
    rw [Module.Dual.lie_apply, hm_lie, map_smul, smul_eq_mul]
  have heq : η y * ψ m = -(ξ y * ψ m) := h1.symm.trans h2
  have hsum : (η y + ξ y) * ψ m = 0 := by
    linear_combination heq
  have hsc_ne : η y + ξ y ≠ 0 := by
    intro h0
    apply hy
    simp only [Pi.neg_apply]
    linear_combination h0
  exact (mul_eq_zero.mp hsum).resolve_left hsc_ne

private theorem exists_dualHighestWeightGenerator_master
    [FiniteDimensional K V] [LieModule.IsIrreducible K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H} {v : V}
    (hv : TauCeti.IsHighestWeightVector b lam v) :
    ∃ fPlus : Module.Dual K V,
      TauCeti.IsHighestWeightVector b
        (-(TauCeti.longestElement (rootSystem H) b • lam)) fPlus ∧
      (∀ M : Submodule ℤ V, Humphreys27_1.IsAdmissibleLattice H x M →
        (M ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
            Submodule.span ℤ {v} ↔
          M.dualLattice K ⊓
              (LieModule.weightSpace (Module.Dual K V)
                ((-(TauCeti.longestElement (rootSystem H) b • lam) : Module.Dual K H) :
                  H → K)).toSubmodule.restrictScalars ℤ =
            Submodule.span ℤ {fPlus})) ∧
      dualMinAdmissibleLattice H b x lam v =
        Humphreys27_1.minAdmissibleLattice H x fPlus := by
  classical
  let w₀ := TauCeti.longestElement (rootSystem H) b
  let μ : Module.Dual K H := w₀ • lam
  obtain ⟨l, hl⟩ := TauCeti.exists_wordProd_eq (rootSystem H) b w₀
  let σ : (Module.End K V)ˣ := wordWeylUnit (V := V) hx l
  have hv_wt : v ∈ LieModule.weightSpace V (lam : H → K) := by
    rw [← TauCeti.genWeightSpace_eq_weightSpace]
    exact hv.mem_genWeightSpace
  have hV_lam_span : (LieModule.weightSpace V (lam : H → K)).toSubmodule =
      Submodule.span K {v} := by
    rw [← TauCeti.genWeightSpace_eq_weightSpace]
    exact TauCeti.genWeightSpace_eq_span_singleton_of_isHighestWeightVector_of_lieSpan_eq_top hv
      (TauCeti.lieSpan_singleton_eq_top_of_ne_zero hv.ne_zero)
  let w : V := (σ : Module.End K V) v
  have hσ_cancel : ∀ y : V, (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V)
      ((σ : Module.End K V) y)) = y := by
    intro y
    rw [← mul_apply_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq_self]
  have hσ_cancel' : ∀ y : V, ((σ : Module.End K V)
      (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y)) = y := by
    intro y
    rw [← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq_self]
  have hw_ne : w ≠ 0 := by
    intro hw0
    apply hv.ne_zero
    have h0 := congrArg (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V)) hw0
    rw [map_zero, hσ_cancel v] at h0
    exact h0
  have hw_wt : w ∈ LieModule.weightSpace V (μ : H → K) := by
    have h := (wordWeylUnit_mem_weightSpace hx l).1 lam hv_wt
    rwa [hl] at h
  have hV_μ_span : (LieModule.weightSpace V (μ : H → K)).toSubmodule = Submodule.span K {w} := by
    apply le_antisymm
    · intro y hy
      have hy' := (wordWeylUnit_mem_weightSpace hx l).2 μ hy
      rw [hl, inv_smul_smul] at hy'
      have hy_span : (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) ∈ Submodule.span K {v} := by
        rw [← hV_lam_span]
        exact hy'
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_span
      have hy_eq : c • w = y := by
        calc
          c • w = (σ : Module.End K V) (c • v) := (map_smul _ c v).symm
          _ = (σ : Module.End K V) (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) := by rw [hc]
          _ = y := hσ_cancel' y
      exact Submodule.mem_span_singleton.mpr ⟨c, hy_eq⟩
    · rw [Submodule.span_singleton_le_iff_mem]
      exact hw_wt
  let W_K : Weight K H V → Submodule K V :=
    fun χ => (LieModule.weightSpace V (χ : H → K)).toSubmodule
  let eW := LinearEquiv.ofBijective (DirectSum.coeLinearMap W_K)
    (TauCeti.isInternal_weightSpace K H V)
  have hμ_ne_bot : LieModule.genWeightSpace V (μ : H → K) ≠ ⊥ := by
    rw [TauCeti.genWeightSpace_eq_weightSpace]
    intro hbot
    rw [hbot] at hw_wt
    exact hw_ne hw_wt
  let χ_μ : Weight K H V := ⟨(μ : H → K), hμ_ne_bot⟩
  let w_sub : W_K χ_μ := ⟨w, hw_wt⟩
  have hli_low : LinearIndependent K (fun _ : Unit => w_sub) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ⟨⟩
    have hval := congrArg Subtype.val hg
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton,
      SetLike.val_smul, ZeroMemClass.coe_zero, w_sub] at hval
    exact (smul_eq_zero.mp hval).resolve_right hw_ne
  have hspan_low : ⊤ ≤ Submodule.span K (Set.range fun _ : Unit => w_sub) := by
    rintro ⟨y, hy⟩ -
    have hy_span : y ∈ Submodule.span K {w} := by
      rw [← hV_μ_span]
      exact hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_span
    have hsub : (⟨y, hy⟩ : W_K χ_μ) = c • w_sub := Subtype.ext hc.symm
    rw [hsub]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(), rfl⟩)
  let b_low : Module.Basis Unit K (W_K χ_μ) := Module.Basis.mk hli_low hspan_low
  let proj_μ : V →ₗ[K] W_K χ_μ :=
    { toFun := fun m => eW.symm m χ_μ
      map_add' := fun m₁ m₂ => by rw [map_add, DFinsupp.add_apply]
      map_smul' := fun c m => by rw [map_smul, DFinsupp.smul_apply]; rfl }
  have hproj_apply : ∀ m : V, proj_μ m = eW.symm m χ_μ := fun _ => rfl
  let fPlus : Module.Dual K V := (b_low.coord ()).comp proj_μ
  have hfPlus_w : fPlus w = 1 := by
    have heW_w : eW (DirectSum.of (fun χ => ↥(W_K χ)) χ_μ w_sub) = w :=
      DirectSum.coeLinearMap_of W_K χ_μ w_sub
    have hsymm_w : eW.symm w = DirectSum.of (fun χ => ↥(W_K χ)) χ_μ w_sub :=
      eW.symm_apply_eq.mpr heW_w.symm
    have hbw : b_low () = w_sub := Module.Basis.mk_apply hli_low hspan_low ()
    change (b_low.coord ()) (proj_μ w) = 1
    rw [hproj_apply, hsymm_w,
      DirectSum.of_eq_same, ← hbw, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same]
  have hfPlus_kill : ∀ η : H → K, η ≠ (μ : H → K) →
      ∀ m ∈ LieModule.weightSpace V η, fPlus m = 0 := by
    intro η hη m hm
    by_cases hm0 : m = 0
    · rw [hm0, map_zero]
    · have hη_ne_bot : LieModule.genWeightSpace V η ≠ ⊥ := by
        rw [TauCeti.genWeightSpace_eq_weightSpace]
        intro hbot
        rw [hbot] at hm
        exact hm0 hm
      let χ' : Weight K H V := ⟨η, hη_ne_bot⟩
      have hχ'_ne : χ' ≠ χ_μ := fun heq => hη (congrArg (fun χ : Weight K H V => (χ : H → K)) heq)
      have heW_m : eW (DirectSum.of (fun χ => ↥(W_K χ)) χ' ⟨m, hm⟩) = m :=
        DirectSum.coeLinearMap_of W_K χ' ⟨m, hm⟩
      have hsymm_m : eW.symm m = DirectSum.of (fun χ => ↥(W_K χ)) χ' ⟨m, hm⟩ :=
        eW.symm_apply_eq.mpr heW_m.symm
      change (b_low.coord ()) (proj_μ m) = 0
      rw [hproj_apply, hsymm_m,
        DirectSum.of_eq_of_ne _ _ _ hχ'_ne.symm, map_zero]
  have hfPlus_ne : fPlus ≠ 0 := by
    intro h0
    have h1 := hfPlus_w
    rw [h0, LinearMap.zero_apply] at h1
    exact zero_ne_one h1
  have hlam_dom : TauCeti.IsDominantIntegral b lam := hv.isDominantIntegral
  have hfPlus_hw : TauCeti.IsHighestWeightVector b (-μ) fPlus := by
    refine TauCeti.isHighestWeightVector_of_forall_rootSpace hfPlus_ne (fun y => ?_)
      (fun α hα y hy => ?_)
    · refine sub_eq_zero.mp (TauCeti.eq_zero_of_forall_genWeightSpace (L := H) fun η m hm => ?_)
      have hlie : ⁅(y : L), m⁆ = η y • m :=
        TauCeti.mem_genWeightSpace_iff_forall_lie_eq_smul.mp hm y
      have hm_wt : m ∈ LieModule.weightSpace V η := by
        rwa [← TauCeti.genWeightSpace_eq_weightSpace]
      rcases eq_or_ne η (μ : H → K) with rfl | hη
      · simp [Module.Dual.lie_apply, hlie]
      · simp [Module.Dual.lie_apply, hlie, hfPlus_kill η hη m hm_wt]
    · refine TauCeti.eq_zero_of_forall_genWeightSpace (L := H) fun η m hm => ?_
      rw [Module.Dual.lie_apply, neg_eq_zero]
      rcases eq_or_ne ((α : H → K) + η) (μ : H → K) with hsum | hsum
      · have hη_eq : η = (μ : H → K) - (α : H → K) := eq_sub_of_add_eq' hsum
        rw [hη_eq] at hm
        rw [TauCeti.genWeightSpace_longestElement_smul_sub_root_eq_bot hv hlam_dom hα] at hm
        rw [(_root_.LieSubmodule.mem_bot _).mp hm, lie_zero, map_zero]
      · have hmem := LieAlgebra.lie_mem_genWeightSpace_of_mem_genWeightSpace hy hm
        rw [TauCeti.genWeightSpace_eq_weightSpace] at hmem
        exact hfPlus_kill _ hsum _ hmem
  have hfPlus_wt : fPlus ∈ LieModule.weightSpace (Module.Dual K V) ((-μ : Module.Dual K H) : H → K) := by
    rw [← TauCeti.genWeightSpace_eq_weightSpace]
    exact hfPlus_hw.mem_genWeightSpace
  have hiff : ∀ M : Submodule ℤ V, Humphreys27_1.IsAdmissibleLattice H x M →
      (M ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {v} ↔
        M.dualLattice K ⊓
            (LieModule.weightSpace (Module.Dual K V)
              ((-μ : Module.Dual K H) : H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {fPlus}) := by
    intro M hM
    have hE1 : M ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {v} ↔
        M ⊓ (LieModule.weightSpace V (μ : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {w} := by
      have hσ_mem := wordWeylUnit_mem_and_inv_mem hx hM.2 l
      constructor
      · intro hinter
        apply le_antisymm
        · intro y hy
          have hy_inv_M : (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) ∈ M :=
            hσ_mem.2 y hy.1
          have hy_inv_wt : (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) ∈
              LieModule.weightSpace V (lam : H → K) := by
            have h := (wordWeylUnit_mem_weightSpace hx l).2 μ hy.2
            rwa [hl, inv_smul_smul] at h
          have hy_span : (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) ∈
              Submodule.span ℤ {v} := by
            rw [← hinter]
            exact ⟨hy_inv_M, hy_inv_wt⟩
          obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hy_span
          have hy_eq : z • w = y := by
            calc
              z • w = (σ : Module.End K V) (z • v) := (map_zsmul _ z v).symm
              _ = (σ : Module.End K V) (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) y) := by
                rw [hz]
              _ = y := hσ_cancel' y
          exact Submodule.mem_span_singleton.mpr ⟨z, hy_eq⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          have hv_M : v ∈ M := by
            have hv_both : v ∈ Submodule.span ℤ {v} :=
              Submodule.subset_span (Set.mem_singleton v)
            rw [← hinter] at hv_both
            exact hv_both.1
          exact ⟨hσ_mem.1 v hv_M, hw_wt⟩
      · intro hinter_w
        apply le_antisymm
        · intro y hy
          have hy_M : ((σ : Module.End K V) y) ∈ M := hσ_mem.1 y hy.1
          have hy_wt : ((σ : Module.End K V) y) ∈ LieModule.weightSpace V (μ : H → K) := by
            have h := (wordWeylUnit_mem_weightSpace hx l).1 lam hy.2
            rwa [hl] at h
          have hy_span : ((σ : Module.End K V) y) ∈ Submodule.span ℤ {w} := by
            rw [← hinter_w]
            exact ⟨hy_M, hy_wt⟩
          obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hy_span
          have hy_eq : z • v = y := by
            calc
              z • v = (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V)
                  ((σ : Module.End K V) (z • v))) := (hσ_cancel (z • v)).symm
              _ = (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) (z • w)) := by rw [map_zsmul]
              _ = (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((σ : Module.End K V) y)) := by
                rw [hz]
              _ = y := hσ_cancel y
          exact Submodule.mem_span_singleton.mpr ⟨z, hy_eq⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          have hw_M : w ∈ M := by
            have hw_both : w ∈ Submodule.span ℤ {w} :=
              Submodule.subset_span (Set.mem_singleton w)
            rw [← hinter_w] at hw_both
            exact hw_both.1
          refine ⟨?_, hv_wt⟩
          have hv_eq : (((σ⁻¹ : (Module.End K V)ˣ) : Module.End K V) w) = v := hσ_cancel v
          rw [← hv_eq]
          exact hσ_mem.2 w hw_M
    refine hE1.trans ⟨?_, ?_⟩
    · intro hinter_w
      apply le_antisymm
      · intro ψ hψ
        have hw_M : w ∈ M := by
          have hw_both : w ∈ Submodule.span ℤ {w} := Submodule.subset_span (Set.mem_singleton w)
          rw [← hinter_w] at hw_both
          exact hw_both.1
        obtain ⟨z, hz⟩ := Submodule.mem_one.mp ((Submodule.mem_dualLattice M ψ).mp hψ.1 w hw_M)
        have hψ_eq : z • fPlus = ψ := by
          have htopW : (⨆ χ : Weight K H V, W_K χ) = ⊤ := by
            dsimp only [W_K]
            simpa only [← LieSubmodule.iSup_toSubmodule, LieSubmodule.toSubmodule_eq_top] using
              TauCeti.iSup_weightSpace_eq_top K H V
          refine _root_.LinearMap.ext_of_iSup_eq_top htopW fun χ m hm => ?_
          rcases eq_or_ne (χ : H → K) (μ : H → K) with hχ | hχ
          · have hm_span : m ∈ Submodule.span K {w} := by
              rw [← hV_μ_span, ← hχ]
              exact hm
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm_span
            have hlhs : (z • fPlus) (c • w) = c * algebraMap ℤ K z := by
              rw [map_smul, LinearMap.smul_apply, hfPlus_w, ← algebraMap_smul K z (1 : K)]
              simp only [smul_eq_mul, mul_one]
            have hrhs : ψ (c • w) = c * algebraMap ℤ K z := by
              rw [map_smul, ← hz, smul_eq_mul]
            exact hlhs.trans hrhs.symm
          · have hne_neg : ((-μ : Module.Dual K H) : H → K) ≠ -(χ : H → K) := by
              intro heq
              apply hχ
              ext y
              have hpt := congrFun heq y
              simp only [LinearMap.neg_apply, Pi.neg_apply] at hpt
              exact neg_injective hpt.symm
            rw [LinearMap.smul_apply, hfPlus_kill (χ : H → K) hχ m hm, smul_zero,
              dual_weightSpace_eval_eq_zero hne_neg hψ.2 hm]
        exact Submodule.mem_span_singleton.mpr ⟨z, hψ_eq⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        refine ⟨?_, hfPlus_wt⟩
        have hdecomp := (Humphreys27_1.weightSpace_inter_directSum_of_isKostantInvariant
          (V := V) hx M.toAddSubgroup hM.2).1
        have hle_comap : M.toAddSubgroup ≤
            ((1 : Submodule ℤ K).comap (fPlus.restrictScalars ℤ)).toAddSubgroup := by
          rw [← hdecomp]
          refine iSup_le fun χ m hm => ?_
          change fPlus m ∈ (1 : Submodule ℤ K)
          rcases eq_or_ne (χ : H → K) (μ : H → K) with hχ | hχ
          · have hm_span : m ∈ Submodule.span ℤ {w} := by
              rw [← hinter_w]
              refine ⟨hm.1, ?_⟩
              change m ∈ LieModule.weightSpace V (μ : H → K)
              rw [← hχ]
              exact hm.2
            obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hm_span
            rw [map_zsmul, hfPlus_w, ← algebraMap_smul K z (1 : K), smul_eq_mul, mul_one]
            exact Submodule.mem_one.mpr ⟨z, rfl⟩
          · rw [hfPlus_kill (χ : H → K) hχ m hm.2]
            exact Submodule.zero_mem _
        exact (Submodule.mem_dualLattice M fPlus).mpr fun m hm => hle_comap hm
    · intro hinter_dual
      apply le_antisymm
      · intro y hy
        have hy_span : y ∈ Submodule.span K {w} := by
          rw [← hV_μ_span]
          exact hy.2
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy_span
        have hfPlus_mem : fPlus ∈ M.dualLattice K := by
          have hmem : fPlus ∈ Submodule.span ℤ {fPlus} :=
            Submodule.subset_span (Set.mem_singleton fPlus)
          rw [← hinter_dual] at hmem
          exact hmem.1
        have hint : fPlus (c • w) ∈ (1 : Submodule ℤ K) :=
          (Submodule.mem_dualLattice M fPlus).mp hfPlus_mem _ hy.1
        rw [map_smul, hfPlus_w, smul_eq_mul, mul_one] at hint
        obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hint
        rw [algebraMap_smul]
        exact Submodule.mem_span_singleton.mpr ⟨z, rfl⟩
      · rw [Submodule.span_singleton_le_iff_mem]
        refine ⟨?_, hw_wt⟩
        obtain ⟨hMdual_adm, hpre_eq⟩ := isAdmissibleLattice_dualLattice_and_preDual hx M hM
        have hw_pre : w ∈ preDualLattice K (M.dualLattice K) := by
          rw [mem_preDualLattice]
          have hdecomp := (Humphreys27_1.weightSpace_inter_directSum_of_isKostantInvariant
            (V := Module.Dual K V) hx (M.dualLattice K).toAddSubgroup hMdual_adm.2).1
          have hle_comap : (M.dualLattice K).toAddSubgroup ≤
              ((1 : Submodule ℤ K).comap
                ((LinearMap.applyₗ (R := K) (M₂ := K) w).restrictScalars ℤ)).toAddSubgroup := by
            rw [← hdecomp]
            refine iSup_le fun η ψ hψ => ?_
            change ψ w ∈ (1 : Submodule ℤ K)
            rcases eq_or_ne (η : H → K) ((-μ : Module.Dual K H) : H → K) with hη | hη
            · have hψ_span : ψ ∈ Submodule.span ℤ {fPlus} := by
                rw [← hinter_dual]
                refine ⟨hψ.1, ?_⟩
                change ψ ∈ LieModule.weightSpace (Module.Dual K V) ((-μ : Module.Dual K H) : H → K)
                rw [← hη]
                exact hψ.2
              obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hψ_span
              rw [LinearMap.smul_apply, hfPlus_w, ← algebraMap_smul K z (1 : K),
                smul_eq_mul, mul_one]
              exact Submodule.mem_one.mpr ⟨z, rfl⟩
            · have hne_neg : (η : H → K) ≠ -(μ : H → K) := by
                intro heq
                apply hη
                ext y
                exact congrFun heq y
              rw [dual_weightSpace_eval_eq_zero hne_neg hψ.2 hw_wt]
              exact Submodule.zero_mem _
          exact fun ψ hψ => hle_comap hψ
        rwa [hpre_eq] at hw_pre
  have hdualMin_eq : dualMinAdmissibleLattice H b x lam v =
      Humphreys27_1.minAdmissibleLattice H x fPlus := by
    have hMmin := Humphreys27_1.isAdmissibleLattice_minAdmissibleLattice hx b hv
    have hinter_min := (hiff (Humphreys27_1.minAdmissibleLattice H x v) hMmin.2.1).mp hMmin.2.2
    have hinter_min' :
        (Humphreys27_1.minAdmissibleLattice H x v).dualLattice K ⊓
          (LieModule.weightSpace (Module.Dual K V)
            ((-(TauCeti.longestElement (rootSystem H) b • lam) : Module.Dual K H) :
              H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {fPlus} := hinter_min
    rw [dualMinAdmissibleLattice, ← Submodule.coe_inf, hinter_min',
      Humphreys27_1.minAdmissibleLattice]
    apply le_antisymm
    · rw [Subring.orbitOfRep_le_iff]
      intro u hu ψ hψ
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hψ
      rw [map_zsmul]
      exact Submodule.smul_mem _ z
        (Subring.apply_mem_orbitOfRep _ _ _ hu (Set.mem_singleton fPlus))
    · rw [Subring.orbitOfRep_le_iff]
      intro u hu ψ hψ
      rw [Set.mem_singleton_iff.mp hψ]
      exact Subring.apply_mem_orbitOfRep _ _ _ hu
        (Submodule.subset_span (Set.mem_singleton fPlus))
  exact ⟨fPlus, hfPlus_hw, hiff, hdualMin_eq⟩

/-- **Humphreys §27.3 construction & sharpness of `M_max` (pp. 161–162):**
For any finite-dimensional irreducible `L`-module `V` with highest-weight vector `v` of weight
`lam`, there exists a highest-weight vector `fPlus` of `V*` of weight `-(w₀ • lam)` such that
`(M_min)* ∩ (V*)_{-(w₀ • lam)} = ℤ · fPlus`, `(M*)_min = 𝔘_ℤ · fPlus`, and `M_max` is itself an
admissible lattice in `V` intersecting `V_lam` in `ℤ · v`. -/
theorem exists_dualHighestWeightGenerator_and_isAdmissibleLattice_maxAdmissibleLattice
    [FiniteDimensional K V] [LieModule.IsIrreducible K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H} {v : V}
    (hv : TauCeti.IsHighestWeightVector b lam v) :
    (∃ fPlus : Module.Dual K V,
        TauCeti.IsHighestWeightVector b
          (-(TauCeti.longestElement (rootSystem H) b • lam)) fPlus ∧
        (Humphreys27_1.minAdmissibleLattice H x v).dualLattice K ⊓
            (LieModule.weightSpace (Module.Dual K V)
              ((-(TauCeti.longestElement (rootSystem H) b • lam) : Module.Dual K H) :
                H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {fPlus} ∧
        dualMinAdmissibleLattice H b x lam v =
          Humphreys27_1.minAdmissibleLattice H x fPlus) ∧
      Humphreys27_1.IsAdmissibleLattice H x (maxAdmissibleLattice H b x lam v) ∧
      maxAdmissibleLattice H b x lam v ⊓
          (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {v} := by
  obtain ⟨fPlus, hfPlus_hw, hiff, hdualMin_eq⟩ :=
    exists_dualHighestWeightGenerator_master hx b hv
  have hMmin := Humphreys27_1.isAdmissibleLattice_minAdmissibleLattice hx b hv
  have hinter_min := (hiff (Humphreys27_1.minAdmissibleLattice H x v) hMmin.2.1).mp hMmin.2.2
  have := TauCeti.LieModule.isIrreducible_dual (K := K) (L := L) (M := V)
  have hNmin := Humphreys27_1.isAdmissibleLattice_minAdmissibleLattice hx b hfPlus_hw
  have hdualMin_adm : Humphreys27_1.IsAdmissibleLattice H x
      (dualMinAdmissibleLattice H b x lam v) := by
    rw [hdualMin_eq]
    exact hNmin.2.1
  obtain ⟨hMmax_full, hMmax_dual⟩ :=
    isFullZLattice_preDualLattice_and_dualLattice_eq hdualMin_adm.1
  have hMmax_adm : Humphreys27_1.IsAdmissibleLattice H x (maxAdmissibleLattice H b x lam v) :=
    ⟨hMmax_full, isKostantInvariant_preDualLattice x hdualMin_adm.2⟩
  have hMmax_inter : maxAdmissibleLattice H b x lam v ⊓
      (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
      Submodule.span ℤ {v} := by
    refine (hiff (maxAdmissibleLattice H b x lam v) hMmax_adm).mpr ?_
    dsimp only [maxAdmissibleLattice]
    rw [hMmax_dual, hdualMin_eq]
    exact hNmin.2.2
  exact ⟨⟨fPlus, hfPlus_hw, hinter_min, hdualMin_eq⟩, hMmax_adm, hMmax_inter⟩

/-- **Humphreys, Proposition 27.3(a)–(b) (p. 162, general irreducible highest-weight form):**
In any finite-dimensional irreducible `L`-module `V` with highest-weight vector `v` of weight
`lam`, every admissible lattice `M ⊂ V` intersecting `V_lam` in `ℤ · v` satisfies
`(a)` `M_min ≤ M` and `(b)` `M ≤ M_max`. -/
theorem minAdmissibleLattice_le_and_le_maxAdmissibleLattice
    [FiniteDimensional K V] [LieModule.IsIrreducible K L V]
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H} {v : V}
    (hv : TauCeti.IsHighestWeightVector b lam v)
    (M : Submodule ℤ V) (hM : Humphreys27_1.IsAdmissibleLattice H x M)
    (hinter : M ⊓ (LieModule.weightSpace V (lam : H → K)).toSubmodule.restrictScalars ℤ =
      Submodule.span ℤ {v}) :
    Humphreys27_1.minAdmissibleLattice H x v ≤ M ∧
      M ≤ maxAdmissibleLattice H b x lam v := by
  obtain ⟨fPlus, _, hiff, hdualMin_eq⟩ := exists_dualHighestWeightGenerator_master hx b hv
  refine ⟨?_, ?_⟩
  · dsimp only [Humphreys27_1.minAdmissibleLattice]
    rw [Subring.orbitOfRep_le_iff]
    intro u hu y hy
    rw [Set.mem_singleton_iff.mp hy]
    have hv_M : v ∈ M := by
      have hmem : v ∈ Submodule.span ℤ {v} := Submodule.subset_span (Set.mem_singleton v)
      rw [← hinter] at hmem
      exact hmem.1
    exact hM.2 u hu v hv_M
  · have hinter_dual := (hiff M hM).mp hinter
    have hfPlus_dual : fPlus ∈ M.dualLattice K := by
      have hmem : fPlus ∈ Submodule.span ℤ {fPlus} :=
        Submodule.subset_span (Set.mem_singleton fPlus)
      rw [← hinter_dual] at hmem
      exact hmem.1
    have hdualMin_le : dualMinAdmissibleLattice H b x lam v ≤ M.dualLattice K := by
      rw [hdualMin_eq]
      dsimp only [Humphreys27_1.minAdmissibleLattice]
      rw [Subring.orbitOfRep_le_iff]
      intro u hu ψ hψ
      rw [Set.mem_singleton_iff.mp hψ]
      exact isKostantInvariant_dualLattice x hM.2 u hu fPlus hfPlus_dual
    have hpre_eq := (isFullZLattice_dualLattice_and_preDualLattice_eq hM.1).2
    rw [← hpre_eq]
    exact preDualLattice_antitone hdualMin_le

/-- **Humphreys, Proposition 27.3(a)–(b) (p. 162, verbatim at `V = V(λ)`):**
Let `V = V(lam) = TauCeti.irreducibleQuotient b lam` with `lam ∈ Λ⁺` (`IsDominantIntegral b lam`)
and maximal vector `v⁺ = TauCeti.irreducibleQuotientGenerator b lam`. Then `M_max` is an
admissible lattice in `V(lam)` intersecting `V(lam)_lam` in `ℤ · v⁺`, and every admissible
lattice `M` in `V(lam)` intersecting `V(lam)_lam` in `ℤ · v⁺` satisfies `(a)` `M_min ≤ M` and
`(b)` `M ≤ M_max`. -/
theorem minAdmissibleLattice_le_and_le_maxAdmissibleLattice_irreducibleQuotient
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (b : (rootSystem H).Base) {lam : Module.Dual K H}
    (hlam : TauCeti.IsDominantIntegral b lam) :
    letI : FiniteDimensional K (TauCeti.irreducibleQuotient b lam) :=
      TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    let v := TauCeti.irreducibleQuotientGenerator b lam
    Humphreys27_1.IsAdmissibleLattice H x (maxAdmissibleLattice H b x lam v) ∧
      maxAdmissibleLattice H b x lam v ⊓
          (LieModule.weightSpace (TauCeti.irreducibleQuotient b lam)
            (lam : H → K)).toSubmodule.restrictScalars ℤ =
        Submodule.span ℤ {v} ∧
      ∀ M : Submodule ℤ (TauCeti.irreducibleQuotient b lam),
        Humphreys27_1.IsAdmissibleLattice H x M →
        M ⊓ (LieModule.weightSpace (TauCeti.irreducibleQuotient b lam)
            (lam : H → K)).toSubmodule.restrictScalars ℤ =
          Submodule.span ℤ {v} →
        Humphreys27_1.minAdmissibleLattice H x v ≤ M ∧
          M ≤ maxAdmissibleLattice H b x lam v := by
  dsimp only
  have : FiniteDimensional K (TauCeti.irreducibleQuotient b lam) :=
    TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  have hv := TauCeti.isHighestWeightVector_irreducibleQuotientGenerator b lam
  obtain ⟨_, hMmax_adm, hMmax_inter⟩ :=
    exists_dualHighestWeightGenerator_and_isAdmissibleLattice_maxAdmissibleLattice hx b hv
  exact ⟨hMmax_adm, hMmax_inter,
    fun M hM hinter => minAdmissibleLattice_le_and_le_maxAdmissibleLattice hx b hv M hM hinter⟩

end Humphreys27_3
