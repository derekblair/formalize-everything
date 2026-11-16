import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.RootSystem
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Lie.Weights.Root.String
import TauCeti.Algebra.Lie.Weights.StructureConstant.DividedPower
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.DividedPowers.Associative
import TauCeti.RingTheory.DividedPowers.NormalOrdering
import TauCeti.RingTheory.DividedPowers.RootString.Signed
import TauCeti.RingTheory.DividedPowers.RootString.G2.Signed
import TauCeti.RingTheory.DividedPowers.RootString.G2.ShortPair
import Humphreys.Ch7.Kostant.GapCRootPlane

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative
open Humphreys26_4.GapCRootPlane

universe u v

namespace Humphreys26_4.GapC

section GeneralCharZeroField

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

omit [LieAlgebra.IsKilling K L] in
/-- Product in `U_K(L)` of a word of root divided powers `x_{γ₁}^{(k₁)} ⋯ x_{γ_r}^{(k_r)}`. -/
noncomputable def rootWordProd (x : Weight K H L → L) (w : List (H.root × ℕ)) :
    _root_.UniversalEnvelopingAlgebra K L :=
  (w.map fun p =>
    dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L)))).prod

/-- Total divided-power exponent sum `k₁ + ⋯ + k_r` of a root word. -/
def rootWordDeg {α : Type*} (w : List (α × ℕ)) : ℕ :=
  (w.map Prod.snd).sum

omit [LieAlgebra.IsKilling K L] in
/-- `ℤ`-span of root divided-power words of total degree strictly below `d`. -/
noncomputable def lowDegSpan (x : Weight K H L → L) (d : ℕ) :
    Submodule ℤ (_root_.UniversalEnvelopingAlgebra K L) :=
  Submodule.span ℤ
    {u : _root_.UniversalEnvelopingAlgebra K L |
      ∃ w : List (H.root × ℕ), rootWordDeg w < d ∧ rootWordProd x w = u}

omit [LieAlgebra.IsKilling K L] [LieModule.IsTriangularizable K H L] in
theorem rootWordProd_mem_lowDegSpan {x : Weight K H L → L} {w : List (H.root × ℕ)} {d : ℕ}
    (hdeg : rootWordDeg w < d) :
    rootWordProd x w ∈ lowDegSpan x d :=
  Submodule.subset_span ⟨w, hdeg, rfl⟩

private theorem comb_ne_zero_of_lin {α β : H.root}
    (hlin : LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β])
    {a b : ℕ} (hab : 0 < a + b) :
    a • (rootSystem H).root α + b • (rootSystem H).root β ≠ 0 := by
  intro h0
  rw [← Nat.cast_smul_eq_nsmul K, ← Nat.cast_smul_eq_nsmul K] at h0
  obtain ⟨ha, hb⟩ := hlin.eq_zero_of_pair h0
  have ha0 : a = 0 := Nat.cast_eq_zero.mp ha
  have hb0 : b = 0 := Nat.cast_eq_zero.mp hb
  omega

private theorem commute_ι_of_add_not_mem_range
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η : H.root}
    (hne0 : (rootSystem H).root ξ + (rootSystem H).root η ≠ 0)
    (hnot : (rootSystem H).root ξ + (rootSystem H).root η ∉ Set.range (rootSystem H).root) :
    Commute
      (_root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)))
      (_root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L))) := by
  have hbot : rootSpace H (((ξ : Weight K H L) : H → K) + (η : Weight K H L)) = ⊥ := by
    by_contra h_ne_bot
    let w : Weight K H L := ⟨((ξ : Weight K H L) : H → K) + (η : Weight K H L), h_ne_bot⟩
    have hw_nz : w.IsNonZero := by
      intro hw0
      apply hne0
      ext h
      have hpt : (w : H → K) h = 0 := congrFun hw0 h
      simpa [w, rootSystem_root_apply, Weight.toLinear_apply] using hpt
    let rw_idx : H.root := ⟨w, by simpa using hw_nz⟩
    apply hnot
    refine ⟨rw_idx, ?_⟩
    ext h
    simp [rw_idx, w, rootSystem_root_apply, Weight.toLinear_apply]
  have hlie := hx.toIsSl2System.lie_eq_zero_of_rootSpace_add_eq_bot ξ η hbot
  have hmap := (_root_.UniversalEnvelopingAlgebra.ι K).map_lie
    (x (ξ : Weight K H L)) (x (η : Weight K H L))
  rw [hlie, map_zero, LieRing.of_associative_ring_bracket] at hmap
  exact sub_eq_zero.mp hmap.symm

private theorem coe_eq_add_of_root_eq_add {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η) :
    ((τ : Weight K H L) : H → K) = ((ξ : Weight K H L) : H → K) + (η : Weight K H L) := by
  ext h
  simpa [rootSystem_root_apply, Weight.toLinear_apply] using DFunLike.congr_fun hτ h

private theorem mul_eq_mul_add_intStructureConstant
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η) :
    _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) *
        _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) =
      _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) +
        hx.intStructureConstant ξ η τ (H.isNonZero_coe_root τ)
          (coe_eq_add_of_root_eq_add hτ) •
          _root_.UniversalEnvelopingAlgebra.ι K (x (τ : Weight K H L)) := by
  have hlie := hx.lie_eq_intStructureConstant_zsmul ξ η τ (H.isNonZero_coe_root τ)
    (coe_eq_add_of_root_eq_add hτ)
  have hmap := (_root_.UniversalEnvelopingAlgebra.ι K).map_lie
    (x (ξ : Weight K H L)) (x (η : Weight K H L))
  rw [hlie, map_zsmul, LieRing.of_associative_ring_bracket] at hmap
  rw [add_comm]
  exact eq_add_of_sub_eq hmap.symm

private theorem exists_sign_mul_of_chainBotCoeff
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {ξ η τ : H.root}
    (hτ : (rootSystem H).root τ = (rootSystem H).root ξ + (rootSystem H).root η)
    {p : ℕ} (hp : (rootSystem H).chainBotCoeff ξ η = p) :
    ∃ s : ℤ,
      _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) =
        _root_.UniversalEnvelopingAlgebra.ι K (x (η : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (ξ : Weight K H L)) +
          (p + 1) • (s • _root_.UniversalEnvelopingAlgebra.ι K (x (τ : Weight K H L))) := by
  have hlin : LinearIndependent K ![(rootSystem H).root ξ, (rootSystem H).root η] :=
    (rootSystem H).linearIndependent_of_add_mem_range_root' ⟨τ, hτ⟩
  have hab : LinearIndependent K
      ![((ξ : Weight K H L) : Module.Dual K H), ((η : Weight K H L) : Module.Dual K H)] := by
    simpa only [rootSystem_root_apply] using hlin
  have hp_lie : LieModule.chainBotCoeff (ξ : Weight K H L) (η : Weight K H L) = p := by
    have hce := (TauCeti.rootSystem_chainCoeffs_eq hab).2
    have hξ : (⟨(ξ : Weight K H L), _⟩ : H.root) = ξ := Subtype.ext rfl
    have hη : (⟨(η : Weight K H L), _⟩ : H.root) = η := Subtype.ext rfl
    rw [hξ, hη] at hce
    exact hce.symm.trans hp
  have hmul := mul_eq_mul_add_intStructureConstant hx hτ
  rcases hx.intStructureConstant_eq_natCast_or_eq_neg_natCast
      ξ η τ (H.isNonZero_coe_root ξ) (H.isNonZero_coe_root η) (H.isNonZero_coe_root τ)
      (coe_eq_add_of_root_eq_add hτ) with hpos | hneg
  · refine ⟨1, ?_⟩
    rw [hmul, hpos, hp_lie, one_zsmul, Nat.cast_smul_eq_nsmul]
  · refine ⟨-1, ?_⟩
    rw [hmul, hneg, hp_lie, neg_one_zsmul, smul_neg, neg_zsmul, Nat.cast_smul_eq_nsmul]

private theorem exists_chain21_commutators
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {α β γ δ : H.root}
    (hγ : (rootSystem H).root γ = (rootSystem H).root α + (rootSystem H).root β)
    (hδ : (rootSystem H).root δ = (2 : ℕ) • (rootSystem H).root α + (rootSystem H).root β) :
    ∃ c d : ℤ,
      _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) =
        _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) +
          c • _root_.UniversalEnvelopingAlgebra.ι K (x (γ : Weight K H L)) ∧
      _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
          (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
              _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) -
            _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
              _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) =
        (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) -
          _root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L)) *
            _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) *
          _root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L)) +
        (2 * d) • _root_.UniversalEnvelopingAlgebra.ι K (x (δ : Weight K H L)) := by
  have hγ_coe := coe_eq_add_of_root_eq_add hγ
  have hδ_add : (rootSystem H).root δ = (rootSystem H).root α + (rootSystem H).root γ := by
    rw [hδ, hγ]; abel
  have hδ_coe_add := coe_eq_add_of_root_eq_add hδ_add
  have hab : ((α : Weight K H L) : H → K) + (β : Weight K H L) ≠ 0 := by
    rw [← hγ_coe]
    exact H.isNonZero_coe_root γ
  have hγ_str : ((γ : Weight K H L) : H → K) =
      ((β : Weight K H L) : H → K) + ((1 : ℕ) : K) • ((α : Weight K H L) : H → K) := by
    rw [hγ_coe, Nat.cast_one, one_smul, add_comm]
  have hδ_str : ((δ : Weight K H L) : H → K) =
      ((β : Weight K H L) : H → K) + ((1 + 1 : ℕ) : K) • ((α : Weight K H L) : H → K) := by
    rw [hδ_coe_add, hγ_coe]
    ext h
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let c : ℤ := hx.intStructureConstant α β γ (H.isNonZero_coe_root γ) hγ_coe
  let c₂ : ℤ := hx.intStructureConstant α γ δ (H.isNonZero_coe_root δ) hδ_coe_add
  let d : ℤ := hx.intDividedStructureConstant α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab δ 2 hδ_str
  have hrec := hx.succ_mul_intDividedStructureConstant α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ δ 1 hγ_str hδ_str
  have hone := hx.intDividedStructureConstant_one α β
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ hγ_coe
  have h2d : (2 : ℤ) * d = c * c₂ := by
    have hrec' : ((1 + 1 : ℕ) : ℤ) * d =
        hx.intDividedStructureConstant α β
          (H.isNonZero_coe_root α) (H.isNonZero_coe_root β) hab γ 1 hγ_str * c₂ := hrec
    rw [hone] at hrec'
    simpa using hrec'
  refine ⟨c, d, mul_eq_mul_add_intStructureConstant hx hγ, ?_⟩
  let φ := _root_.UniversalEnvelopingAlgebra.ι K (L := L)
  have hlie1 : ⁅x (α : Weight K H L), x (β : Weight K H L)⁆ = c • x (γ : Weight K H L) :=
    hx.lie_eq_intStructureConstant_zsmul α β γ (H.isNonZero_coe_root γ) hγ_coe
  have hlie2 : ⁅x (α : Weight K H L), x (γ : Weight K H L)⁆ = c₂ • x (δ : Weight K H L) :=
    hx.lie_eq_intStructureConstant_zsmul α γ δ (H.isNonZero_coe_root δ) hδ_coe_add
  have hlie_iter :
      ⁅x (α : Weight K H L), ⁅x (α : Weight K H L), x (β : Weight K H L)⁆⁆ =
        (2 * d) • x (δ : Weight K H L) := by
    rw [hlie1, lie_zsmul, hlie2, smul_smul, ← h2d]
  have hmap1 := φ.map_lie (x (α : Weight K H L)) (x (β : Weight K H L))
  rw [LieRing.of_associative_ring_bracket] at hmap1
  have hmap2 := φ.map_lie (x (α : Weight K H L)) ⁅x (α : Weight K H L), x (β : Weight K H L)⁆
  rw [hlie_iter, map_zsmul, LieRing.of_associative_ring_bracket, hmap1] at hmap2
  rw [add_comm]
  exact eq_add_of_sub_eq hmap2.symm

private theorem sub_comm_mem_lowDegSpan_of_orientedCone
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {α β : H.root}
    (hlin : LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β])
    (hcone : OrientedCone (rootSystem H) α β) (m n : ℕ) :
    dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) *
        dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L))) -
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L))) *
        dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) ∈
      lowDegSpan x (m + n) := by
  classical
  let P := rootSystem H
  let E (r : H.root) : _root_.UniversalEnvelopingAlgebra K L :=
    _root_.UniversalEnvelopingAlgebra.ι K (x (r : Weight K H L))
  have comm_of {ξ η : H.root} {a b : ℕ} (hab : 0 < a + b)
      (hsum_eq : P.root ξ + P.root η = a • P.root α + b • P.root β)
      (hnot : a • P.root α + b • P.root β ∉ Set.range P.root) :
      Commute (E ξ) (E η) := by
    apply commute_ι_of_add_not_mem_range hx
    · rw [hsum_eq]; exact comb_ne_zero_of_lin hlin hab
    · rwa [hsum_eq]
  rcases hcone with
    (_ | ⟨γ, hγ, h21, h12⟩ | ⟨γ, δ, hγ, hδ, h31, h22, h12⟩ |
     ⟨γ, δ, ε, hγ, hδ, hε, hp1, hp2, hp3, h31, h22, h13, h32, h23, h33⟩ |
     ⟨γ, δ, ε, ζ, hγ, hδ, hε, hζ, hp1, hp2, hp3, hp4,
      h41, h42, h12, h52, h43, h53, h63⟩)
  · -- Case 1: Empty (`α + β ∉ Φ`)
    rename_i hempty
    have hcomm : Commute (E α) (E β) :=
      comm_of (a := 1) (b := 1) (by decide) (by simp) (by simpa only [one_smul] using hempty)
    have hdp := (commute_dividedPower_dividedPower hcomm m n).eq
    change dividedPower m (E α) * dividedPower n (E β) -
      dividedPower n (E β) * dividedPower m (E α) ∈ lowDegSpan x (m + n)
    rw [hdp, sub_self]
    exact (lowDegSpan x (m + n)).zero_mem
  · -- Case 2: Class-two (`{(1, 1)}`)
    let c : ℤ := hx.intStructureConstant α β γ (H.isNonZero_coe_root γ)
      (coe_eq_add_of_root_eq_add hγ)
    have hxy : E α * E β = E β * E α + c • E γ := mul_eq_mul_add_intStructureConstant hx hγ
    have hxz : Commute (E α) (c • E γ) :=
      (comm_of (a := 2) (b := 1) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h21)).smul_right c
    have hyz : Commute (E β) (c • E γ) :=
      (comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)).smul_right c
    have hstr := dividedPower_mul_dividedPower_of_commutator_eq hxy hxz hyz m n
    have h0mem : (0 : ℕ) ∈ Finset.range (min m n + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        dividedPower (n - 0) (E β) * dividedPower 0 (c • E γ) * dividedPower (m - 0) (E α) =
          dividedPower n (E β) * dividedPower m (E α) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α) * dividedPower n (E β) -
      dividedPower n (E β) * dividedPower m (E α) ∈ lowDegSpan x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (lowDegSpan x (m + n)).sum_mem fun k hk => ?_
    obtain ⟨hk_ne, hk_range⟩ := Finset.mem_erase.mp hk
    have hk_le : k ≤ min m n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
    rw [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc]
    have hw_eq :
        dividedPower (n - k) (E β) * dividedPower k (E γ) * dividedPower (m - k) (E α) =
          rootWordProd x [(β, n - k), (γ, k), (α, m - k)] := by
      simp [rootWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (lowDegSpan x (m + n)).smul_mem (c ^ k)
      (rootWordProd_mem_lowDegSpan (by simp [rootWordDeg]; omega))
  · -- Case 3: Length-2 chain (`{(1, 1), (2, 1)}`)
    obtain ⟨c, d, hxy, hxxy⟩ := exists_chain21_commutators hx hγ hδ
    have hxw : Commute (E α) (E δ) :=
      comm_of (a := 3) (b := 1) (by decide) (by rw [hδ]; abel)
        (by simpa only [one_smul] using h31)
    have hyz : Commute (E β) (E γ) :=
      comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)
    have hstr := dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
      hxy hxxy hxw hyz m n
    have h0mem : ((0, 0) : ℕ × ℕ) ∈ chainLeTwoIndex m n := by
      rw [mem_chainLeTwoIndex]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        (c ^ (0 : ℕ) * d ^ (0 : ℕ)) •
          (dividedPower (n - 0 - 0) (E β) * dividedPower 0 (E γ) *
            dividedPower 0 (E δ) * dividedPower (m - 0 - 2 * 0) (E α)) =
          dividedPower n (E β) * dividedPower m (E α) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α) * dividedPower n (E β) -
      dividedPower n (E β) * dividedPower m (E α) ∈ lowDegSpan x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (lowDegSpan x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2⟩
    obtain ⟨hpn, hpm⟩ := mem_chainLeTwoIndex.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    have hw_eq :
        dividedPower (n - p1 - p2) (E β) * dividedPower p1 (E γ) *
          dividedPower p2 (E δ) * dividedPower (m - p1 - 2 * p2) (E α) =
          rootWordProd x
            [(β, n - p1 - p2), (γ, p1), (δ, p2), (α, m - p1 - 2 * p2)] := by
      simp [rootWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (lowDegSpan x (m + n)).smul_mem (c ^ p1 * d ^ p2)
      (rootWordProd_mem_lowDegSpan (by simp [rootWordDeg]; omega))
  · -- Case 4: `G₂` `120°` short pair (`{(1, 1), (2, 1), (1, 2)}`)
    obtain ⟨c, hc⟩ := exists_sign_mul_of_chainBotCoeff hx hγ hp1
    obtain ⟨c₁, hc₁⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root δ = P.root α + P.root γ by rw [hδ, hγ]; abel) hp2
    obtain ⟨c₂, hc₂⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ε = P.root γ + P.root β by rw [hε, hγ]; abel) hp3
    let z' := (2 * c) • E γ
    let w' := (3 * (c * c₁)) • E δ
    let s' := (3 * (c * c₂)) • E ε
    have hxy : E α * E β = E β * E α + z' := by
      change E α * E β = E β * E α + (2 * c) • E γ
      rw [show E α * E β = E β * E α + (1 + 1) • (c • E γ) from hc,
        ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      rfl
    have hxz : E α * z' = z' * E α + 2 • w' := by
      dsimp only [z', w']
      rw [mul_smul_comm, smul_mul_assoc,
        show E α * E γ = E γ * E α + (2 + 1) • (c₁ • E δ) from hc₁, smul_add]
      simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      congr 2; ring
    have hzy : z' * E β = E β * z' + 2 • s' := by
      dsimp only [z', s']
      rw [smul_mul_assoc, mul_smul_comm,
        show E γ * E β = E β * E γ + (2 + 1) • (c₂ • E ε) from hc₂, smul_add]
      simp only [← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
      congr 2; ring
    have hxw : Commute (E α) w' :=
      (comm_of (a := 3) (b := 1) (by decide) (by rw [hδ]; abel)
        (by simpa only [one_smul] using h31)).smul_right _
    have hxs : Commute (E α) s' :=
      (comm_of (a := 2) (b := 2) (by decide) (by rw [hε]; abel) h22).smul_right _
    have hys : Commute (E β) s' :=
      (comm_of (a := 1) (b := 3) (by decide) (by rw [hε]; abel)
        (by simpa only [one_smul] using h13)).smul_right _
    have hzw : Commute z' w' :=
      ((comm_of (a := 3) (b := 2) (by decide) (by rw [hγ, hδ]; abel)
        h32).smul_left _).smul_right _
    have hzs : Commute z' s' :=
      ((comm_of (a := 2) (b := 3) (by decide) (by rw [hγ, hε]; abel)
        h23).smul_left _).smul_right _
    have hws : Commute w' s' :=
      ((comm_of (a := 3) (b := 3) (by decide) (by rw [hδ, hε]; abel)
        h33).smul_left _).smul_right _
    have hstr := dividedPower_mul_dividedPower_of_g2_short_pair_scaled
      hxy hxz hzy hxw hxs hys hzw hzs hws m n
    have h0mem : ((0, (0, 0)) : ℕ × ℕ × ℕ) ∈ g2ShortPairIndex m n := by
      rw [mem_g2ShortPairIndex]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        dividedPower (n - 0 - 0 - 2 * 0) (E β) * dividedPower 0 z' *
          dividedPower 0 w' * dividedPower 0 s' *
          dividedPower (m - 0 - 2 * 0 - 0) (E α) =
          dividedPower n (E β) * dividedPower m (E α) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α) * dividedPower n (E β) -
      dividedPower n (E β) * dividedPower m (E α) ∈ lowDegSpan x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (lowDegSpan x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2, p3⟩
    obtain ⟨hpn, hpm⟩ := mem_g2ShortPairIndex.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 + p3 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    dsimp only [z', w', s']
    simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc, smul_smul]
    have hw_eq :
        dividedPower (n - p1 - p2 - 2 * p3) (E β) *
          (dividedPower p1 (E γ) *
            (dividedPower p2 (E δ) *
              (dividedPower p3 (E ε) *
                dividedPower (m - p1 - 2 * p2 - p3) (E α)))) =
          rootWordProd x
            [(β, n - p1 - p2 - 2 * p3), (γ, p1), (δ, p2),
             (ε, p3), (α, m - p1 - 2 * p2 - p3)] := by
      simp [rootWordProd, E]
    simp only [mul_assoc]
    rw [hw_eq]
    exact (lowDegSpan x (m + n)).smul_mem _
      (rootWordProd_mem_lowDegSpan (by simp [rootWordDeg]; omega))
  · -- Case 5: `G₂` `150°` simple pair (`{(1, 1), (2, 1), (3, 1), (3, 2)}`)
    obtain ⟨a, ha⟩ := exists_sign_mul_of_chainBotCoeff hx hγ hp1
    obtain ⟨b, hb⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root δ = P.root α + P.root γ by rw [hδ, hγ]; abel) hp2
    obtain ⟨c, hc⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ε = P.root α + P.root δ by rw [hε, hδ]; abel) hp3
    obtain ⟨d, hd⟩ := exists_sign_mul_of_chainBotCoeff hx
      (show P.root ζ = P.root δ + P.root γ by rw [hζ, hδ, hγ]; abel) hp4
    have hxy : E α * E β = E β * E α + a • E γ := by
      rw [show E α * E β = E β * E α + (0 + 1) • (a • E γ) from ha, zero_add, one_smul]
    have hxz : E α * E γ = E γ * E α + 2 • (b • E δ) := hb
    have hxw : E α * E δ = E δ * E α + 3 • (c • E ε) := hc
    have hwz : E δ * E γ = E γ * E δ + 3 • (d • E ζ) := hd
    have hxv : Commute (E α) (E ε) :=
      comm_of (a := 4) (b := 1) (by decide) (by rw [hε]; abel)
        (by simpa only [one_smul] using h41)
    have hxs : Commute (E α) (E ζ) :=
      comm_of (a := 4) (b := 2) (by decide) (by rw [hζ]; abel) h42
    have hyz : Commute (E β) (E γ) :=
      comm_of (a := 1) (b := 2) (by decide) (by rw [hγ]; abel)
        (by simpa only [one_smul] using h12)
    have hwv : Commute (E δ) (E ε) :=
      comm_of (a := 5) (b := 2) (by decide) (by rw [hδ, hε]; abel) h52
    have hzs : Commute (E γ) (E ζ) :=
      comm_of (a := 4) (b := 3) (by decide) (by rw [hγ, hζ]; abel) h43
    have hws : Commute (E δ) (E ζ) :=
      comm_of (a := 5) (b := 3) (by decide) (by rw [hδ, hζ]; abel) h53
    have hvs : Commute (E ε) (E ζ) :=
      comm_of (a := 6) (b := 3) (by decide) (by rw [hε, hζ]; abel) h63
    have hstr := dividedPower_mul_dividedPower_of_g2_zsmul
      a b c d hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs m n
    have h0mem : ((0, (0, (0, 0))) : ℕ × ℕ × ℕ × ℕ) ∈ chainG2Index m n := by
      rw [mem_chainG2Index]; dsimp; omega
    rw [← Finset.add_sum_erase _ _ h0mem] at hstr
    have h0term :
        (a ^ (0 : ℕ) * (a * b) ^ (0 : ℕ) * (a * b * c) ^ (0 : ℕ) *
          (a ^ 2 * b * d) ^ (0 : ℕ)) •
        (dividedPower (n - 0 - 0 - 0 - 2 * 0) (E β) * dividedPower 0 (E γ) *
          dividedPower 0 (E δ) * dividedPower 0 (E ε) * dividedPower 0 (E ζ) *
          dividedPower (m - 0 - 2 * 0 - 3 * 0 - 3 * 0) (E α)) =
          dividedPower n (E β) * dividedPower m (E α) := by
      simp
    rw [h0term] at hstr
    change dividedPower m (E α) * dividedPower n (E β) -
      dividedPower n (E β) * dividedPower m (E α) ∈ lowDegSpan x (m + n)
    rw [hstr, add_sub_cancel_left]
    refine (lowDegSpan x (m + n)).sum_mem fun p hp => ?_
    obtain ⟨hp_ne, hp_mem⟩ := Finset.mem_erase.mp hp
    rcases p with ⟨p1, p2, p3, p4⟩
    obtain ⟨hpn, hpm⟩ := mem_chainG2Index.mp hp_mem
    dsimp only at hpn hpm ⊢
    have hp_pos : 0 < p1 + p2 + p3 + p4 := by
      simp only [ne_eq, Prod.mk.injEq, not_and] at hp_ne
      omega
    have hw_eq :
        dividedPower (n - p1 - p2 - p3 - 2 * p4) (E β) *
          dividedPower p1 (E γ) * dividedPower p2 (E δ) *
          dividedPower p3 (E ε) * dividedPower p4 (E ζ) *
          dividedPower (m - p1 - 2 * p2 - 3 * p3 - 3 * p4) (E α) =
          rootWordProd x
            [(β, n - p1 - p2 - p3 - 2 * p4), (γ, p1), (δ, p2),
             (ε, p3), (ζ, p4),
             (α, m - p1 - 2 * p2 - 3 * p3 - 3 * p4)] := by
      simp [rootWordProd, E, mul_assoc]
    rw [hw_eq]
    exact (lowDegSpan x (m + n)).smul_mem _
      (rootWordProd_mem_lowDegSpan (by simp [rootWordDeg]; omega))

/-- **Humphreys Lemma 26.3C in `U_K(L)` with strict total-degree drop (Gap 26.4-C, Route C2):**
For any linearly independent roots `α, β ∈ Φ` (`α ≠ β`, `α ≠ -β`) and `m, n : ℕ`, the commutator
`x_α^{(m)} x_β^{(n)} - x_β^{(n)} x_α^{(m)}` is a `ℤ`-linear combination of root divided-power
words of strictly smaller total exponent sum `< m + n`. -/
theorem dividedPower_mul_dividedPower_sub_comm_mem_lowDegSpan
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α β : H.root) (hne : α ≠ β)
    (hneg : (rootSystem H).root α ≠ -(rootSystem H).root β)
    (m n : ℕ) :
    dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) *
        dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L))) -
      dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (β : Weight K H L))) *
        dividedPower m (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) ∈
      lowDegSpan x (m + n) := by
  have hlin : LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β] :=
    (IsReduced.linearIndependent_iff (rootSystem H)).mpr ⟨hne, hneg⟩
  rcases orientedCone_or_symm (rootSystem H) hlin with hcone | hcone_symm
  · exact sub_comm_mem_lowDegSpan_of_orientedCone hx hlin hcone m n
  · have hlin' : LinearIndependent K ![(rootSystem H).root β, (rootSystem H).root α] :=
      LinearIndependent.pair_symm_iff.mpr hlin
    have hsym := sub_comm_mem_lowDegSpan_of_orientedCone hx hlin' hcone_symm n m
    rw [Nat.add_comm] at hsym
    simpa only [neg_sub] using (lowDegSpan x (m + n)).neg_mem hsym

end GeneralCharZeroField

end Humphreys26_4.GapC
