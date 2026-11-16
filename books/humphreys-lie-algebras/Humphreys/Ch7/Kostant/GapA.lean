import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Basis.Base
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.Lie.Sl2.Straightening
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Adjoint.Basic
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Module.Rat
import TauCeti.RingTheory.Binomial
import TauCeti.RingTheory.DividedPowers.Associative

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti TauCeti.Associative

universe u v

namespace Humphreys26_4.GapA

section GeneralCharZeroField

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

noncomputable local instance instAlgebraRatUEA :
    Algebra ℚ (_root_.UniversalEnvelopingAlgebra K L) :=
  Algebra.compHom (_root_.UniversalEnvelopingAlgebra K L) (algebraMap ℚ K)

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- Root-divided-power subring identical to `Humphreys26_4.kostantSubring`. -/
noncomputable abbrev rootSubring (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable K H L] (x : Weight K H L → L) :
    Subring (_root_.UniversalEnvelopingAlgebra K L) :=
  Subring.closure
    (Set.range fun p : H.root × ℕ =>
      dividedPower p.2 (_root_.UniversalEnvelopingAlgebra.ι K (x (p.1 : Weight K H L))))

omit [LieAlgebra.IsKilling K L] in
theorem dividedPower_root_mem_rootSubring (x : Weight K H L → L) (α : H.root) (n : ℕ) :
    dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x (α : Weight K H L))) ∈
      rootSubring H x :=
  Subring.subset_closure ⟨(α, n), rfl⟩

theorem dividedPower_weight_mem_rootSubring
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : Weight K H L) (n : ℕ) :
    dividedPower n (_root_.UniversalEnvelopingAlgebra.ι K (x α)) ∈ rootSubring H x := by
  by_cases hα : α.IsNonZero
  · exact dividedPower_root_mem_rootSubring x ⟨α, by simpa using hα⟩ n
  · rw [hx.toIsSl2System.eq_zero_of_isZero α (not_not.mp hα), map_zero]
    cases n with
    | zero => simp
    | succ n => simp

/-- **Humphreys, Corollary 26.2 (p. 153) / `C9` root-only gate:**
Every coroot binomial `Ring.choose (ι K (coroot α)) b` lies in the subring generated solely by
the root-vector divided powers `x_β^t / t!`. -/
theorem ringChoose_coroot_mem_rootSubring
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α : Weight K H L) (b : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι K ((coroot α : H) : L)) b ∈
      rootSubring H x := by
  by_cases hα : α.IsNonZero
  · induction b using Nat.strong_induction_on with
    | ind b ih =>
      let φ : L →ₗ⁅K⁆ _root_.UniversalEnvelopingAlgebra K L :=
        _root_.UniversalEnvelopingAlgebra.ι K
      have ht : IsSl2Triple ((coroot α : H) : L) (x α) (x (-α)) :=
        hx.toIsSl2System.isSl2Triple α hα
      have hstr := LieHom.dividedPower_map_e_mul_dividedPower_map_f φ
        ht.lie_e_f ht.lie_h_e_nsmul ht.lie_h_f_nsmul b b
      rw [min_self, Finset.sum_range_succ] at hstr
      have hlhs : dividedPower b (φ (x α)) * dividedPower b (φ (x (-α))) ∈ rootSubring H x :=
        (rootSubring H x).mul_mem
          (dividedPower_weight_mem_rootSubring hx α b)
          (dividedPower_weight_mem_rootSubring hx (-α) b)
      have hsum_lt :
          (∑ k ∈ Finset.range b,
            dividedPower (b - k) (φ (x (-α))) *
              Ring.choose (φ ((coroot α : H) : L) - (b + b : ℕ) + (2 * k : ℕ)) k *
                dividedPower (b - k) (φ (x α))) ∈ rootSubring H x := by
        refine (rootSubring H x).sum_mem fun k hk => ?_
        have hklt : k < b := Finset.mem_range.mp hk
        have hshift :
            φ ((coroot α : H) : L) - (b + b : ℕ) + (2 * k : ℕ) =
              φ ((coroot α : H) : L) +
                (((2 * (k : ℤ) - 2 * (b : ℤ)) : ℤ) : _root_.UniversalEnvelopingAlgebra K L) := by
          have hz : ((2 * (k : ℤ) - 2 * (b : ℤ) : ℤ) : _root_.UniversalEnvelopingAlgebra K L) =
              (2 * k : ℕ) - (b + b : ℕ) := by
            rw [← Int.cast_natCast (2 * k), ← Int.cast_natCast (b + b), ← Int.cast_sub]
            congr 1
            omega
          rw [hz]
          abel
        rw [hshift]
        have hch :
            Ring.choose
              (φ ((coroot α : H) : L) +
                (((2 * (k : ℤ) - 2 * (b : ℤ)) : ℤ) : _root_.UniversalEnvelopingAlgebra K L)) k ∈
              rootSubring H x :=
          TauCeti.Ring.choose_add_intCast_mem
            (fun j hj => ih j (lt_of_le_of_lt hj hklt)) (2 * (k : ℤ) - 2 * (b : ℤ))
        exact (rootSubring H x).mul_mem
          ((rootSubring H x).mul_mem (dividedPower_weight_mem_rootSubring hx (-α) (b - k)) hch)
          (dividedPower_weight_mem_rootSubring hx α (b - k))
      have htop :
          dividedPower (b - b) (φ (x (-α))) *
            Ring.choose (φ ((coroot α : H) : L) - (b + b : ℕ) + (2 * b : ℕ)) b *
              dividedPower (b - b) (φ (x α)) =
            Ring.choose (φ ((coroot α : H) : L)) b := by
        have harg :
            φ ((coroot α : H) : L) - (b + b : ℕ) + (2 * b : ℕ) = φ ((coroot α : H) : L) := by
          rw [Nat.two_mul, sub_add_cancel]
        simp only [Nat.sub_self, dividedPower_zero, one_mul, mul_one, harg]
      rw [htop] at hstr
      have heq :
          Ring.choose (φ ((coroot α : H) : L)) b =
            dividedPower b (φ (x α)) * dividedPower b (φ (x (-α))) -
              ∑ k ∈ Finset.range b,
                dividedPower (b - k) (φ (x (-α))) *
                  Ring.choose (φ ((coroot α : H) : L) - (b + b : ℕ) + (2 * k : ℕ)) k *
                    dividedPower (b - k) (φ (x α)) := by
        rw [hstr, add_sub_cancel_left]
      rw [heq]
      exact (rootSubring H x).sub_mem hlhs hsum_lt
  · have h0 : (coroot α : H) = 0 := coroot_eq_zero_iff.mpr (not_not.mp hα)
    rw [h0, ZeroMemClass.coe_zero, map_zero]
    cases b with
    | zero => simp
    | succ b => simp

theorem kostantMonomial_mem_rootSubring
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    {m ℓ : ℕ} (b : (rootSystem H).Base)
    (posOrd : Fin m ≃ {α : H.root // b.IsPos α})
    (baseOrd : Fin ℓ ≃ ↥b.support)
    (p : (Fin m → ℕ) × (Fin ℓ → ℕ) × (Fin m → ℕ)) :
    (List.ofFn fun j : Fin m =>
      dividedPower (p.1 j)
        (_root_.UniversalEnvelopingAlgebra.ι K (x (-((posOrd j).1 : Weight K H L))))).prod *
      (List.ofFn fun i : Fin ℓ =>
        Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι K
            (((rootSystem H).coroot (baseOrd i).1 : H) : L))
          (p.2.1 i)).prod *
      (List.ofFn fun j : Fin m =>
        dividedPower (p.2.2 j)
          (_root_.UniversalEnvelopingAlgebra.ι K (x ((posOrd j).1 : Weight K H L)))).prod ∈
      rootSubring H x := by
  refine (rootSubring H x).mul_mem ((rootSubring H x).mul_mem ?_ ?_) ?_
  · refine Subring.list_prod_mem _ fun u hu => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact dividedPower_weight_mem_rootSubring hx (-((posOrd j).1 : Weight K H L)) (p.1 j)
  · refine Subring.list_prod_mem _ fun u hu => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    rw [rootSystem_coroot_apply]
    exact ringChoose_coroot_mem_rootSubring hx (((baseOrd i).1 : H.root) : Weight K H L) (p.2.1 i)
  · refine Subring.list_prod_mem _ fun u hu => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact dividedPower_weight_mem_rootSubring hx ((posOrd j).1 : Weight K H L) (p.2.2 j)

end GeneralCharZeroField

section RatBridge

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L]
  [FiniteDimensional ℚ L] [LieAlgebra.IsKilling ℚ L]
  {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℚ H L]

attribute [local instance] TauCeti.moduleNNRat

theorem rootSubring_eq_chevalleyKostantForm_rat
    {ω : L ≃ₗ⁅ℚ⁆ L} {x : Weight ℚ H L → L} (hx : TauCeti.IsChevalleySystem ω x) :
    rootSubring H x = TauCeti.chevalleyKostantForm x := by
  apply le_antisymm
  · rw [Subring.closure_le]
    rintro _ ⟨⟨α, n⟩, rfl⟩
    exact TauCeti.dividedPower_mem_chevalleyKostantForm x (α : Weight ℚ H L) n
  · rw [TauCeti.chevalleyKostantForm_def, TauCeti.UniversalEnvelopingAlgebra.kostantForm_le_iff]
    refine ⟨fun α n => dividedPower_weight_mem_rootSubring hx α n, fun α n => ?_⟩
    rw [TauCeti.corootFamily_apply]
    exact ringChoose_coroot_mem_rootSubring hx α n

end RatBridge

end Humphreys26_4.GapA
