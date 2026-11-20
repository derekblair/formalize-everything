import Humphreys.Ch7.ChevalleyBasis25_2
import TauCeti.Algebra.Lie.Weights.Chevalley.System
import TauCeti.Algebra.Lie.Weights.InvariantForm
import TauCeti.Algebra.Lie.Weights.Root.String
import TauCeti.Algebra.Lie.Weights.StructureConstant.Opposite
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.RootString

open LieAlgebra LieAlgebra.IsKilling LieModule RootPairing TauCeti

universe u v w₁ w₂

namespace Humphreys25_2c

section RootPairing25_1c

variable {ι : Type w₁} {K : Type u} {M : Type v} {N : Type w₂}
  [Finite ι] [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- **Humphreys, Proposition 25.1(c) (p. 145, abstract root-system form):**
Let `α, β ∈ Φ` be linearly independent roots of a reduced crystallographic root pairing `P`
over a characteristic-zero field `K`, with `α`-string `β - rα, …, β, …, β + qα`
(`r = P.chainBotCoeff α β`, `q = P.chainTopCoeff α β`). If `γ = α + β ∈ Φ`, then for every
invariant bilinear form `B : P.InvariantForm`,
`r + 1 = q * B(α + β, α + β) / B(β, β)`. -/
theorem rootPairing_length_ratio_25_1c
    (P : RootPairing ι K M N) [P.IsCrystallographic] [P.IsReduced]
    (B : P.InvariantForm) {α β γ : ι}
    (_hlin : LinearIndependent K ![P.root α, P.root β])
    (hγ : P.root γ = P.root α + P.root β) :
    ((P.chainBotCoeff α β + 1 : ℕ) : K) =
      (P.chainTopCoeff α β : K) *
        (B.form (P.root γ) (P.root γ) / B.form (P.root β) (P.root β)) := by
  have h := B.chainTopCoeff_mul_apply_root_self_eq hγ
  have hβ : B.form (P.root β) (P.root β) ≠ 0 := B.ne_zero β
  rw [← mul_div_assoc, eq_div_iff hβ]
  exact h.symm

end RootPairing25_1c

section SplitKilling

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- **Humphreys, Proposition 25.1(c) (p. 145, Killing-form `(L, H)` specialization):**
For linearly independent nonzero roots `α, β ∈ Φ` whose sum `γ = α + β` is a nonzero root,
the Lie root-string parameters `r = chainBotCoeff α β` and `q = chainTopCoeff α β` and the
transferred Killing form `(λ, μ) = TauCeti.invForm λ μ = κ(t_λ, t_μ)` on `H*` satisfy
`r + 1 = q * (γ, γ) / (β, β)`. -/
theorem rootString_length_ratio_25_1c
    (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (_hlin : LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)])
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    ((chainBotCoeff α β + 1 : ℕ) : K) =
      (chainTopCoeff α β : K) *
        (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
          TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H)) := by
  let P := rootSystem H
  let i : H.root := ⟨α, by simpa [LieSubalgebra.root] using hα⟩
  let j : H.root := ⟨β, by simpa [LieSubalgebra.root] using hβ⟩
  let k : H.root := ⟨γ, by simpa [LieSubalgebra.root] using hγ⟩
  have hk : P.root k = P.root i + P.root j := by
    ext z
    simpa only [P, rootSystem_root_apply, i, j, k, Weight.toLinear_apply,
      LinearMap.add_apply, Pi.add_apply] using congrFun hαβ z
  have hlin' : LinearIndependent K ![P.root i, P.root j] := by
    simpa only [P, rootSystem_root_apply, i, j] using _hlin
  have hcoeff := rootSystem_chainCoeffs_eq _hlin
  have hratio := rootPairing_length_ratio_25_1c P (rootInvariantForm (H := H)) hlin' hk
  simpa only [P, i, j, k, rootInvariantForm_form, rootSystem_root_apply,
    hcoeff.1, hcoeff.2] using hratio

/-- **Humphreys, Proposition 25.2(c) (pp. 146–147, verbatim universal form):**
For **any** choice of root vectors `x : Weight K H L → L` satisfying `(a)` (`hx : TauCeti.IsSl2System x`,
i.e., `x δ ∈ L_δ` and `⁅x δ, x (-δ)⁆ = h_δ` for all `δ ∈ Φ`) and `(b)` (`c(-α, -β) = -c(α, β)`
at a genuine root sum `γ = α + β`, with no ambient Lie automorphism assumed), the structure
constant `⁅x α, x β⁆ = c(α, β) • x γ` automatically satisfies
`c(α, β)² = q(r + 1) * (γ, γ) / (β, β)`,
where `r = chainBotCoeff α β`, `q = chainTopCoeff α β`, and `(·, ·) = TauCeti.invForm`. -/
theorem structureConstant_sq_eq_mul_length_ratio
    {x : Weight K H L → L} (hx : TauCeti.IsSl2System x)
    (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (_hlin : LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)])
    (hαβ : (γ : H → K) = (α : H → K) + β)
    (hneg : ((-γ : Weight K H L) : H → K) =
      ((-α : Weight K H L) : H → K) + (-β : Weight K H L))
    (hb : hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg =
      -hx.structureConstant α β γ hγ hαβ) :
    hx.structureConstant α β γ hγ hαβ ^ 2 =
      ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
        (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
          TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H)) := by
  have hprod := hx.structureConstant_mul_structureConstant α β γ hγ hαβ hα hβ
  have hsymm := hx.structureConstant_neg_neg_mul_killingForm_eq α β γ hγ hαβ hβ
  rw [hb, neg_mul, neg_inj] at hsymm
  have hsq_kill : hx.structureConstant α β γ hγ hαβ ^ 2 * killingForm K L (x γ) (x (-γ)) =
      ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
        killingForm K L (x β) (x (-β)) := by
    calc
      hx.structureConstant α β γ hγ hαβ ^ 2 * killingForm K L (x γ) (x (-γ))
        = hx.structureConstant α β γ hγ hαβ *
            (hx.structureConstant α β γ hγ hαβ * killingForm K L (x γ) (x (-γ))) := by ring
      _ = hx.structureConstant α β γ hγ hαβ *
            (hx.structureConstant (-α) γ β hβ (by rw [Weight.coe_neg, hαβ]; abel) *
              killingForm K L (x β) (x (-β))) := by rw [hsymm]
      _ = (hx.structureConstant α β γ hγ hαβ *
            hx.structureConstant (-α) γ β hβ (by rw [Weight.coe_neg, hαβ]; abel)) *
            killingForm K L (x β) (x (-β)) := by ring
      _ = ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
            killingForm K L (x β) (x (-β)) := by rw [hprod]
  have hβkill : killingForm K L (x β) (x (-β)) =
      2 * (TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H))⁻¹ := by
    rw [hx.killingForm_root_neg_eq β hβ, TauCeti.invForm_apply_apply, Weight.toLinear_apply]
  have hγkill : killingForm K L (x γ) (x (-γ)) =
      2 * (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H))⁻¹ := by
    rw [hx.killingForm_root_neg_eq γ hγ, TauCeti.invForm_apply_apply, Weight.toLinear_apply]
  rw [hβkill, hγkill] at hsq_kill
  have hβne : TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H) ≠ 0 :=
    TauCeti.invForm_self_ne_zero hβ
  have hγne : TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) ≠ 0 :=
    TauCeti.invForm_self_ne_zero hγ
  field_simp [hβne, hγne] at hsq_kill ⊢
  linear_combination hsq_kill

/-- **Humphreys, Proposition 25.2(c) + Proposition 25.1(c) square reduction (pp. 147–148):**
For **any** `hx : TauCeti.IsSl2System x` satisfying `c(-α, -β) = -c(α, β)` at a genuine root sum
`γ = α + β`, combining Proposition 25.2(c) with Proposition 25.1(c) yields `c(α, β)² = (r + 1)²`. -/
theorem structureConstant_sq_eq_natCast_sq
    {x : Weight K H L → L} (hx : TauCeti.IsSl2System x)
    (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (_hlin : LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)])
    (hαβ : (γ : H → K) = (α : H → K) + β)
    (hneg : ((-γ : Weight K H L) : H → K) =
      ((-α : Weight K H L) : H → K) + (-β : Weight K H L))
    (hb : hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg =
      -hx.structureConstant α β γ hγ hαβ) :
    hx.structureConstant α β γ hγ hαβ ^ 2 =
      ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2 := by
  have hsq := structureConstant_sq_eq_mul_length_ratio hx α β γ hα hβ hγ _hlin hαβ hneg hb
  have hlen := rootString_length_ratio_25_1c α β γ hα hβ hγ _hlin hαβ
  rw [hsq]
  push_cast at hlen ⊢
  calc
    (chainTopCoeff α β : K) * ((chainBotCoeff α β : K) + 1) *
        (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
          TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H))
      = ((chainBotCoeff α β : K) + 1) *
          ((chainTopCoeff α β : K) *
            (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
              TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H))) := by ring
    _ = ((chainBotCoeff α β : K) + 1) * ((chainBotCoeff α β : K) + 1) := by rw [← hlen]
    _ = ((chainBotCoeff α β : K) + 1) ^ 2 := by ring

/-- **`IsChevalleySystem` specialization of Proposition 25.2(c):**
For any Chevalley system `(ω, x)` (`hx : TauCeti.IsChevalleySystem ω x`) and any nonzero roots
`α, β, γ` with `γ = α + β`, `α` and `β` are automatically linearly independent over `K` and
`c(α, β)²` equals both `q(r + 1) * (γ, γ) / (β, β)` and `(r + 1)²`. -/
theorem isChevalleySystem_structureConstant_sq_eq
    {ω : L ≃ₗ⁅K⁆ L} {x : Weight K H L → L} (hx : TauCeti.IsChevalleySystem ω x)
    (α β γ : Weight K H L)
    (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
    (hαβ : (γ : H → K) = (α : H → K) + β) :
    LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)] ∧
      hx.toIsSl2System.structureConstant α β γ hγ hαβ ^ 2 =
        ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
          (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
            TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H)) ∧
      hx.toIsSl2System.structureConstant α β γ hγ hαβ ^ 2 =
        ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2 := by
  let P := rootSystem H
  let i : H.root := ⟨α, by simpa [LieSubalgebra.root] using hα⟩
  let j : H.root := ⟨β, by simpa [LieSubalgebra.root] using hβ⟩
  let k : H.root := ⟨γ, by simpa [LieSubalgebra.root] using hγ⟩
  have hk : P.root k = P.root i + P.root j := by
    ext z
    simpa only [P, rootSystem_root_apply, i, j, k, Weight.toLinear_apply,
      LinearMap.add_apply, Pi.add_apply] using congrFun hαβ z
  have hlin : LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)] := by
    simpa only [P, rootSystem_root_apply, i, j] using
      P.linearIndependent_of_add_mem_range_root' ⟨k, hk⟩
  have hneg : ((-γ : Weight K H L) : H → K) =
      ((-α : Weight K H L) : H → K) + (-β : Weight K H L) := by
    rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
    abel
  have hb : hx.toIsSl2System.structureConstant (-α) (-β) (-γ) hγ.neg hneg =
      -hx.toIsSl2System.structureConstant α β γ hγ hαβ :=
    hx.toIsSl2System.structureConstant_neg_neg_of_hom α β γ hγ hαβ ω.toLieHom
      (hx.map_root α) (hx.map_root β) (hx.map_root γ)
  exact ⟨hlin,
    structureConstant_sq_eq_mul_length_ratio hx.toIsSl2System α β γ hα hβ hγ hlin hαβ hneg hb,
    structureConstant_sq_eq_natCast_sq hx.toIsSl2System α β γ hα hβ hγ hlin hαβ hneg hb⟩

/-- **Complete unconditional Proposition 25.2(a)–(b)–(c) (pp. 146–147):**
Composing landed `Humphreys25_2.exists_rootVectors_chevalley_ab` (`ChevalleyBasis25_2.lean` L75)
with Proposition 25.2(c) and Proposition 25.1(c), every finite-dimensional split Killing Lie
algebra `(L, H)` over a characteristic-zero field `K` admits a coroot-normalized root-vector
system `(x, hx : TauCeti.IsSl2System x)` satisfying `(a)`, `(b)`, and both `(c)` square
identities on every genuine root sum `γ = α + β`. -/
theorem exists_rootVectors_chevalley_abc :
    ∃ (x : Weight K H L → L) (hx : TauCeti.IsSl2System x),
      ∀ (α β γ : Weight K H L)
        (hα : α.IsNonZero) (hβ : β.IsNonZero) (hγ : γ.IsNonZero)
        (hαβ : (γ : H → K) = (α : H → K) + β)
        (hneg : ((-γ : Weight K H L) : H → K) =
          ((-α : Weight K H L) : H → K) + (-β : Weight K H L)),
        LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)] ∧
          hx.structureConstant (-α) (-β) (-γ) hγ.neg hneg =
            -hx.structureConstant α β γ hγ hαβ ∧
          hx.structureConstant α β γ hγ hαβ ^ 2 =
            ((chainTopCoeff α β * (chainBotCoeff α β + 1) : ℕ) : K) *
              (TauCeti.invForm (γ : Module.Dual K H) (γ : Module.Dual K H) /
                TauCeti.invForm (β : Module.Dual K H) (β : Module.Dual K H)) ∧
          hx.structureConstant α β γ hγ hαβ ^ 2 =
            ((chainBotCoeff α β + 1 : ℕ) : K) ^ 2 := by
  obtain ⟨x, hx, hab⟩ := Humphreys25_2.exists_rootVectors_chevalley_ab (K := K) (L := L) (H := H)
  refine ⟨x, hx, fun α β γ hα hβ hγ hαβ hneg ↦ ?_⟩
  let P := rootSystem H
  let i : H.root := ⟨α, by simpa [LieSubalgebra.root] using hα⟩
  let j : H.root := ⟨β, by simpa [LieSubalgebra.root] using hβ⟩
  let k : H.root := ⟨γ, by simpa [LieSubalgebra.root] using hγ⟩
  have hk : P.root k = P.root i + P.root j := by
    ext z
    simpa only [P, rootSystem_root_apply, i, j, k, Weight.toLinear_apply,
      LinearMap.add_apply, Pi.add_apply] using congrFun hαβ z
  have hlin : LinearIndependent K ![(α : Module.Dual K H), (β : Module.Dual K H)] := by
    simpa only [P, rootSystem_root_apply, i, j] using
      P.linearIndependent_of_add_mem_range_root' ⟨k, hk⟩
  have hb := hab α β γ hα hβ hγ hαβ hneg
  exact ⟨hlin, hb,
    structureConstant_sq_eq_mul_length_ratio hx α β γ hα hβ hγ hlin hαβ hneg hb,
    structureConstant_sq_eq_natCast_sq hx α β γ hα hβ hγ hlin hαβ hneg hb⟩

end SplitKilling

end Humphreys25_2c
