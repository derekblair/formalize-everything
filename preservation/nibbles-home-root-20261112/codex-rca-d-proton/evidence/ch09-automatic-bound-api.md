# 9.21: automatic norm bound for arbitrary complex Banach algebra homomorphisms

Read-only, source-based interface research. No Chapter 9 Lean source or compiler run was created. All paths below are relative to the pinned Mathlib checkout now preserved at `evidence/lake-before-clean-ch08/packages/mathlib`. Its Git HEAD was read as `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lean remains `leanprover/lean4:v4.34.1`.

The complete mathematical route is available from existing Mathlib results. Use the **L¹ norm on `WithLp 1 (Unitization ℂ A)`**, lift the given algebraic homomorphism to a unital homomorphism, apply `AlgHom.norm_apply_le_self`, and restrict to the isometric inclusion of A. This covers noncommutative and nonunital A, including the zero homomorphism. There is no continuity or boundedness hypothesis on the given homomorphism, no `RegularNormedAlgebra` assumption, and no assumption that the norm of multiplication operators equals the norm of their defining elements.

## Faithful input and output

The printed 9.20 definition, immediately before 9.21, assumes only complex linearity and multiplicativity. The following typeclasses express the printed complex Banach algebra structure:

```lean
{A : Type*}
[NonUnitalNormedRing A] [NormedSpace ℂ A]
[IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
[CompleteSpace A]
(φ : A →ₙₐ[ℂ] ℂ)
```

`NonUnitalNormedRing` supplies the associative multiplication and its submultiplicative norm bound. The two scalar-action compatibility classes express the usual bilinearity of multiplication. They are algebra structure requirements, not extra analytic assumptions. No `NormOneClass A`, unit, commutativity, star operation, or nonzero condition is needed.

The direct endpoint is `∀ a, ‖φ a‖ ≤ ‖a‖`. To state exactly the printed functional norm conclusion, construct a continuous linear map `φc : A →L[ℂ] ℂ` with `∀ a, φc a = φ a`, and prove `‖φc‖ ≤ 1`. The raw `NonUnitalAlgHom` is an algebraic bundle; do not assume that writing `‖φ‖` already expresses its continuous functional norm. An existence theorem for this extension, together with the pointwise bound, is a faithful formal statement of 9.21.

## The L¹ unitization instances

`Analysis/Normed/Algebra/UnitizationL1.lean` supplies all the following for

```lean
U := WithLp 1 (Unitization ℂ A)
```

| Declaration / source line | What is supplied |
| --- | --- |
| `WithLp.instUnitizationNormedAddCommGroup`, 43 | Norm and additive metric on U |
| `WithLp.instCompleteSpace`, 56 | `CompleteSpace U`, from completeness of ℂ and A |
| `WithLp.instUnitizationRing`, 88 | Unital ring structure on U |
| algebra instance, 94 | `Algebra ℂ U`, via the type equivalence |
| anonymous instance, 103 | `NormOneClass U` |
| `WithLp.instUnitizationNormedRing`, 120 | Multiplication satisfies `norm_mul_le` in the L¹ norm |
| `WithLp.instUnitizationNormedAlgebra`, 139 | `NormedAlgebra ℂ U` |

The general field version of the completeness instance requires both `[CompleteSpace 𝕜]` and `[CompleteSpace A]`. The former is automatic for ℂ. The ring/algebra instances additionally use exactly the scalar compatibility classes displayed above.

The essential norm identities are existing declarations at lines 65, 75 and 81:

```lean
WithLp.unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) :
  ‖x‖ = ‖(WithLp.ofLp x).fst‖ + ‖(WithLp.ofLp x).snd‖

WithLp.unitization_norm_inr (a : A) :
  ‖WithLp.toLp 1 (a : Unitization 𝕜 A)‖ = ‖a‖

WithLp.unitization_isometry_inr :
  Isometry (fun a : A => WithLp.toLp 1 (a : Unitization 𝕜 A))
```

The file's introduction explicitly distinguishes this construction from the norm on bare `Unitization 𝕜 A` coming from the regular representation. The latter can require `RegularNormedAlgebra`; this proof never equips bare `Unitization ℂ A` with that norm. It uses bare unitization only as an algebraic intermediate in a composition of algebra homomorphisms.

## Exact algebraic maps and their directions

`Algebra/Algebra/Unitization.lean:675` defines

```lean
Unitization.inrNonUnitalAlgHom (R A) : A →ₙₐ[R] Unitization R A
```

Its underlying function is the canonical coercion `a ↦ (a : Unitization R A)`, represented by scalar coordinate 0 and A coordinate a. The coordinate lemmas are `Unitization.fst_inr` and `Unitization.snd_inr`.

`Algebra/Algebra/Unitization.lean:766` defines the actual universal-property equivalence:

```lean
Unitization.lift : (A →ₙₐ[R] C) ≃ (Unitization R A →ₐ[R] C)
```

Here C is a unital R-algebra. This needs algebraic structures only. Its forward map is `NonUnitalAlgHom.toAlgHom` (line 736), whose defining function is exactly

```lean
fun x => algebraMap R C x.fst + φ x.snd
```

Thus `Unitization.lift φ` is a **unital** homomorphism even if φ is zero; on the scalar copy it is the algebra map, and on the A copy it is φ. `Unitization.lift_symm_apply_apply` (line 772) records the restriction of a unital homomorphism back to A. The source marks `lift` with `@[simps! apply symm_apply]`, but the planned proof can use the defining formula directly and need not guess the generated simplification lemma's precise shape.

`Analysis/Normed/Algebra/UnitizationL1.lean:113` defines

```lean
WithLp.unitizationAlgEquiv (R : Type*) :
  WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization 𝕜 A
```

Its scalar assumptions are `[CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A] [IsScalarTower R 𝕜 A]`, in addition to the section assumptions above. Specializing R = 𝕜 = ℂ is automatic from the displayed Banach algebra hypotheses. The direction is **from the normed type synonym to plain unitization**, and its underlying function is `WithLp.ofLp` by definition (`WithLp.linearEquiv`). Its inverse has underlying function `WithLp.toLp 1`.

Therefore the desired map has the explicit type and composition

```lean
Φ : WithLp 1 (Unitization ℂ A) →ₐ[ℂ] ℂ
Φ := (Unitization.lift φ).comp
  (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := A) ℂ).toAlgHom
```

No continuity of the algebraic equivalence is required: it is used only to construct the algebraic map Φ. Its defining evaluation on the embedded element is

```lean
Φ (WithLp.toLp 1 (a : Unitization ℂ A)) = algebraMap ℂ ℂ 0 + φ a = φ a
```

For the first equality, unfold the composition, `WithLp.unitizationAlgEquiv`, `Unitization.lift`, and `NonUnitalAlgHom.toAlgHom`, or use `change` to expose the same definitional expression. The second equality is `map_zero` and `zero_add`. The defining reduction avoids dependence on undocumented generated simp names.

There is no ordinary `Unitization.map` definition in the inspected pinned `Algebra/Algebra/Unitization.lean`. The nearby `Unitization.starMap` (line 833) requires a star homomorphism and is not appropriate here. Use the `lift`/`AlgHom.comp` construction above. No star or C⋆-algebra API is needed.

## The automatic bound theorem, exact requirements

`Analysis/Normed/Algebra/Spectrum.lean:538` states, with the surrounding section variables made explicit:

```lean
{𝕜 A F : Type*}
[NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
[CompleteSpace A] [NormOneClass A]
[FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]

AlgHom.norm_apply_le_self (f : F) (a : A) : ‖f a‖ ≤ ‖a‖
```

This theorem does **not** assume continuity of f. Its proof uses algebraic spectral membership `AlgHom.apply_mem_spectrum` and the Banach-algebra spectral norm bound. In the same section Mathlib derives `ContinuousLinearMapClass F 𝕜 A 𝕜` automatically and defines `AlgHom.toContinuousLinearMap`; continuity is an output of the spectral argument, not an input.

Instantiate the domain A of this theorem with U, use Φ for f, and apply it to `WithLp.toLp 1 (a : Unitization ℂ A)`. The map evaluation above and `WithLp.unitization_norm_inr` give

\[
 |\varphi(a)| = |\Phi(0,a)| \leq \|(0,a)\|_1 = \|a\|.
\]

This completes the full pointwise estimate, including a = 0 and φ = 0. No nonzero case split, invertible element chosen in A, normalized unit of A, approximation, or previously proved continuity is needed.

## Bundling the functional and proving its operator norm bound

`Algebra/Algebra/NonUnitalHom.lean:111` supplies a `LinearMapClass` instance for `NonUnitalAlgHomClass`. The precise safe conversion is

```lean
L : A →ₗ[ℂ] ℂ := LinearMap.ofClass φ
```

`LinearMap.ofClass` is defined in `Algebra/Module/LinearMap/Defs.lean:161`, and `LinearMap.coe_ofClass` (line 203) says its underlying function is φ, by `rfl`. Do not invent a `NonUnitalAlgHom.toLinearMap` projection: it is not defined in the pinned nonunital homomorphism file. The library itself uses `LinearMap.ofClass f` in `NonUnitalSubalgebra.map_toSubmodule`.

`Analysis/Normed/Operator/ContinuousLinearMap.lean:55` supplies

```lean
LinearMap.mkContinuous (f : E →ₛₗ[σ] F) (C : ℝ)
  (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F
```

For L, take C = 1. The preceding pointwise bound supplies its hypothesis after rewriting `one_mul`; `LinearMap.coe_ofClass` identifies function values. `LinearMap.mkContinuous_coe` and `LinearMap.mkContinuous_apply` at lines 81 and 86 preserve the original function. Consequently this construction adds continuity as proved data without changing φ.

`Analysis/Normed/Operator/Basic.lean:475` gives

```lean
LinearMap.mkContinuous_norm_le (f : E →ₛₗ[σ] F)
  {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
  ‖f.mkContinuous C h‖ ≤ C
```

At C = 1, this proves the exact operator-norm conclusion. One may expose the pointwise estimate, the resulting continuous functional, its agreement with φ, and its norm bound as a single theorem family. No new analytic bridge lemma beyond these immediate map/coercion identities is needed.

## Import and verification boundary

`Mathlib.Analysis.Normed.Algebra.Spectrum` publicly imports `Mathlib.Analysis.Normed.Algebra.UnitizationL1`, which publicly imports the algebraic unitization file. The implementation also needs the usual complex normed-field instances and `LinearMap.mkContinuous_norm_le` from `Mathlib.Analysis.Normed.Operator.Basic`. These can be explicit imports when the post-gate Chapter 9 fragment is written. No claim is made here that a smallest import set or the suggested elaboration steps have been compiler-tested.

All mathematical hypotheses and named source declarations were checked against the pinned files. The eventual Lean proof still requires the ordinary compilation and axiom audit after the Chapter 8 gate; this document is research evidence, not a completed Chapter 9 node.

## Source hashes

SHA-256 of the source files read for the interface:

```text
65dc4021546e5513d3b4e9df9847bd08a5784481c761a92a25ec866144d2f4b8  Analysis/Normed/Algebra/UnitizationL1.lean
99525c2ce12aae495f0ce09e9e55cb5056c3f7e426dd9f650c524f113886f333  Analysis/Normed/Algebra/Spectrum.lean
892c07ac61c73d4cd90d555a6b5bcbf1f1d4eb06f13994f18e361c401a09ffd2  Algebra/Algebra/Unitization.lean
de4c64c1ce754ec5db9012252f3c6a2cb741304c8f58622a8b5d7a6517830f07  Algebra/Algebra/NonUnitalHom.lean
aea1c354ffc798aaa5397f2f58124bc2ed7b29d24227ae568d3f5745f839570d  Algebra/Module/LinearMap/Defs.lean
a5bc6904f1abe7b2c6e9b1e2d946095bb0633815a31bf44fa8bb3ded3aa767b1  Analysis/Normed/Operator/ContinuousLinearMap.lean
548a0efc514e14f51df886f708e6693436c91692a73cfb814024c41ae7725138  Analysis/Normed/Operator/Basic.lean
```
