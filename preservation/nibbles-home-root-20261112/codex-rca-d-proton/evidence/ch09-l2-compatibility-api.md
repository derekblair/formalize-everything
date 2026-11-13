# 9.13: arbitrary L¹∩L² compatibility — pinned API plan

Source-based research only; no Chapter 9 Lean module, declaration, import, or compiler run was created. Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lean pin: `leanprover/lean4:v4.34.1`. Source paths below are relative to Mathlib. During this research root moved the old package tree to `evidence/lake-before-clean-ch08/packages/mathlib`; the theorem names and source line references refer to that same pinned tree.

The shortest route uses two test-pairing identities and local-integrable test uniqueness. It proves compatibility for every `f : ℝ → ℂ` with `Integrable f volume` and `MemLp f 2 volume`. It does **not** assume f is continuous or Schwartz, does **not** assume its classical Fourier transform is L¹ or L², and does not require proving any new density theorem. Mathlib already performed the Schwartz-density extension in `Lp.fourier_toTemperedDistribution_eq`.

## Exact target and notation

For this intermediate theorem use Mathlib's convention: volume on ℝ and `exp(-2πixt)`. Let

- `u := hf2.toLp f : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)`;
- `q := (𝓕 u : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))`;
- `F := (𝓕 f : ℝ → ℂ)`.

The desired bridge is `⇑q =ᵐ[volume] F`. Square integrability of F and equality of the bundled L² functions then follow, rather than being hypotheses. Explicit type annotations are important because `𝓕` is overloaded on ordinary functions, Schwartz functions, L² and tempered distributions.

Use `open scoped FourierTransform SchwartzMap` for the notations, and qualify `MeasureTheory.Lp` when the different Lp-related Fourier names could be confused. The unitary used here is exactly `MeasureTheory.Lp.fourierTransformₗᵢ`; no L¹-to-bounded-continuous-function map is being substituted for it.

## Existing APIs, with specialized types

The following are existing declarations. Signatures are specialized to ℝ/ℂ where that removes irrelevant typeclass parameters.

### L² and its distributional Fourier transform

`Analysis/Fourier/LpSpace.lean:50`:

```lean
MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ :
  (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) ≃ₗᵢ[ℂ]
  (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))
```

`Analysis/Fourier/LpSpace.lean:123`:

```lean
MeasureTheory.Lp.fourier_toTemperedDistribution_eq
  (u : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) :
  𝓕 (u : 𝓢'(ℝ, ℂ)) =
    ((𝓕 u : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : 𝓢'(ℝ, ℂ))
```

The source proves this for **all** L² u by `DenseRange.induction_on` using `SchwartzMap.denseRange_toLpCLM`. Its only generic domain assumptions are finite-dimensional real inner-product space with Borel structure; its codomain is a complete complex inner-product space. ℝ and ℂ discharge these directly. It has no L¹ or continuity hypothesis.

The inverse version `MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq` is at line 137 with both transforms replaced by `𝓕⁻`.

`Analysis/Distribution/TemperedDistribution.lean:482`:

```lean
TemperedDistribution.fourier_apply
  (T : 𝓢'(ℝ, ℂ)) (ψ : 𝓢(ℝ, ℂ)) :
  𝓕 T ψ = T (𝓕 ψ)
```

The inverse version is `TemperedDistribution.fourierInv_apply` (line 497). The distributional transform is defined by precomposition with Schwartz Fourier; there is no complex conjugation in this pairing convention.

`Analysis/Distribution/TemperedDistribution.lean:169`:

```lean
MeasureTheory.Lp.toTemperedDistribution_apply
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (u : MeasureTheory.Lp ℂ p (volume : Measure ℝ)) (ψ : 𝓢(ℝ, ℂ)) :
  MeasureTheory.Lp.toTemperedDistribution u ψ =
    ∫ x, ψ x • u x
```

The generic version requires the measure to have temperate growth, Borel structure on the finite-dimensional domain when using the later uniqueness lemma, and a complete complex normed target. Volume on ℝ has the required instances. The Lp-to-distribution coercion is `CoeHead`, explicitly because the target distribution type cannot infer the Lp exponent and measure. Spell out `Lp.toTemperedDistribution` if coercion elaboration becomes ambiguous.

### Ordinary Fourier / Schwartz pairing

`Analysis/Fourier/FourierTransform.lean:242`, exact general statement:

```lean
VectorFourier.integral_fourierIntegral_smul_eq_flip
  {f : V → ℂ} {g : W → F}
  (he : Continuous e)
  (hL : Continuous fun p : V × W => L p.1 p.2)
  (hf : Integrable f μ) (hg : Integrable g ν) :
  (∫ ξ, VectorFourier.fourierIntegral e μ L f ξ • g ξ ∂ν) =
    ∫ x, f x • VectorFourier.fourierIntegral e ν L.flip g x ∂μ
```

In this section μ and ν are sigma-finite Borel measures, one of V/W is second-countable, and the targets are complete complex normed spaces. For the bridge choose:

- V=W=ℝ, μ=ν=volume;
- `e := Real.fourierChar`, `L := innerₗ ℝ`;
- the theorem's first function f := `(ψ : ℝ → ℂ)`;
- the theorem's second function g := the arbitrary original f;
- `he := Real.continuous_fourierChar`, `hL := continuous_inner`;
- integrability arguments `ψ.integrable` and the given `hf1`.

This ordering gives `∫ (𝓕ψ) • f = ∫ ψ • (𝓕f)` directly. It avoids any commutation or conjugation step. `flip_innerₗ : (innerₗ ℝ).flip = innerₗ ℝ` is the simp lemma in `Analysis/InnerProductSpace/Basic.lean:148`.

`SchwartzMap.fourier_coe` (`Analysis/Distribution/SchwartzSpace/Fourier.lean:98`) identifies the underlying function of Schwartz Fourier with ordinary Fourier, definitionally. `SchwartzMap.integrable` (`SchwartzSpace/Basic.lean:1131`) gives integrability of ψ; Fourier preserves Schwartz space, so `(𝓕 ψ).integrable` is also available if separately needed.

The pinned proof of `SchwartzMap.integral_bilin_fourier_eq` (`SchwartzSpace/Fourier.lean:227`) is a useful elaboration template: it applies `VectorFourier.integral_bilin_fourierIntegral_eq_flip` with `(L := innerₗ V)`, `continuous_fourierChar`, `continuous_inner` and uses `simpa using!`. However that theorem itself assumes both inputs Schwartz; the proposed bridge must call the **VectorFourier** theorem above to retain arbitrary f.

### Representatives and local integrability

`MeasureTheory/Function/LpSpace/Basic.lean:116,151,190`:

```lean
MeasureTheory.MemLp.coeFn_toLp (hf : MemLp f p μ) :
  hf.toLp f =ᵐ[μ] f

MeasureTheory.Lp.ext {u v : MeasureTheory.Lp E p μ}
  (h : u =ᵐ[μ] v) : u = v

MeasureTheory.Lp.memLp (u : MeasureTheory.Lp E p μ) : MemLp u p μ
```

`MeasureTheory/Function/LocallyIntegrable.lean:351`:

```lean
MeasureTheory.MemLp.locallyIntegrable [IsLocallyFiniteMeasure μ]
  (hf : MemLp f p μ) (hp : 1 ≤ p) : LocallyIntegrable f μ
```

Apply this to `Lp.memLp q` and `1 ≤ (2 : ℝ≥0∞)` to get local integrability of the L² output representative, without assuming global L¹ membership.

`Analysis/Fourier/FourierTransform.lean:163`:

```lean
VectorFourier.fourierIntegral_continuous
  (he : Continuous e)
  (hL : Continuous fun p : V × W => L p.1 p.2)
  (hf : Integrable f μ) :
  Continuous (VectorFourier.fourierIntegral e μ L f)
```

It also has `[FirstCountableTopology W]`, discharged for ℝ. Instantiate the same e,L as above to get `Continuous F`. `Continuous.locallyIntegrable` (`MeasureTheory/Function/LocallyIntegrable.lean:560`) then gives `LocallyIntegrable F volume`; its requirements are a locally finite measure and `SecondCountableTopologyEither` of domain and codomain, both available here.

### Test uniqueness — root namespace

**The following names are root-level, not `MeasureTheory.ae_eq_…`.** `Analysis/Distribution/AEEqOfIntegralContDiff.lean` opens MeasureTheory but never enters its namespace.

At line 195:

```lean
ae_eq_of_integral_contDiff_smul_eq
  (hu : LocallyIntegrable u μ) (hv : LocallyIntegrable v μ)
  (h : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, φ x • u x ∂μ) = ∫ x, φ x • v x ∂μ) :
  ∀ᵐ x ∂μ, u x = v x
```

The generic theorem assumes a finite-dimensional real normed domain with its Borel sigma algebra and a complete real normed codomain. Specializing its codomain to ℂ is valid using the real scalar restriction. The zero version is `ae_eq_zero_of_integral_contDiff_smul_eq_zero` (line 186).

`HasCompactSupport.toSchwartzMap` is a root method (`SchwartzSpace/Basic.lean:555`):

```lean
HasCompactSupport.toSchwartzMap
  {f : E → F} (h₁ : HasCompactSupport f)
  (h₂ : ContDiff ℝ ∞ f) : 𝓢(E, F)
```

Given a real test φ, form the complex test ψ from `Complex.ofRealCLM ∘ φ`. The following exact construction is already used in the pinned proof of `Lp.ker_toTemperedDistributionCLM_eq_bot` (`TemperedDistribution.lean:216–226`):

```lean
have hcompact : HasCompactSupport (Complex.ofRealCLM ∘ φ) :=
  hφcompact.comp_left rfl
have hsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
-- ψ is hcompact.toSchwartzMap hsmooth
```

That existing proof uses `by simp` to change `∫ φ x • u x` (real scalar multiplication) into the corresponding distribution evaluation against this complex ψ. Reuse this conversion; no ad hoc complex-inner-product or conjugation argument is needed.

## Minimal bridge lemmas to prove

These names are **proposed**, not existing declarations or checked Lean code.

1. `l2_fourier_schwartz_pairing`, valid for every `u : Lp ℂ 2 volume` and every `ψ : 𝓢(ℝ,ℂ)`:

   `∫ x, ψ x • (𝓕 u) x = ∫ x, (𝓕 ψ) x • u x`.

   Take `Lp.fourier_toTemperedDistribution_eq u`, apply
   `congrArg (fun T : 𝓢'(ℝ,ℂ) => T ψ)`, reverse the equality, and simplify with `TemperedDistribution.fourier_apply` and `Lp.toTemperedDistribution_apply`. This is merely a convenient evaluation of existing arbitrary-L² compatibility.

2. `integrable_fourier_schwartz_pairing`, valid for every `hf1 : Integrable f volume` and `ψ : 𝓢(ℝ,ℂ)`:

   `∫ x, (𝓕 ψ) x • f x = ∫ x, ψ x • (𝓕 f) x`.

   Use the VectorFourier theorem with ψ as its first function and f as its second, as detailed above. The ordinary/Schwartz coercion and `flip_innerₗ` are the only normalization steps.

3. The actual `l1_l2_fourier_compatibility` theorem, with hypotheses exactly `Integrable f volume` and `MemLp f 2 volume`, and conclusion `⇑(𝓕 (hf2.toLp f) : Lp ℂ 2 volume) =ᵐ[volume] (𝓕 f : ℝ → ℂ)`.

   Establish local integrability of both sides as above. For every complex Schwartz ψ, chain:

   ```text
   ∫ ψ · q = ∫ (𝓕ψ) · u       by bridge 1
           = ∫ (𝓕ψ) · f       by integral_congr_ae and hf2.coeFn_toLp
           = ∫ ψ · F           by bridge 2.
   ```

   Restrict these tests to the complexifications of real smooth compactly supported φ and invoke the root-level test-uniqueness theorem. In the middle step use `filter_upwards [hf2.coeFn_toLp]` and rewrite the pointwise representative equality; neither replacing u by f pointwise nor changing its null set is justified.

A reusable `ae_eq_of_schwartz_test_integrals_eq` helper could encapsulate the compact-real-test conversion, but it is optional. Thus only two short pairing adapters and the principal compatibility theorem are necessary; no new L¹ distribution embedding, no simultaneous L¹/L² approximating sequence, and no new Schwartz-density proof are required.

## Corollaries without circular assumptions

From the proved a.e. equality h and `Lp.memLp q`, use

```lean
MeasureTheory.memLp_congr_ae h : MemLp (⇑q) 2 volume ↔ MemLp F 2 volume
```

(`Function/LpSeminorm/Basic.lean:561`) to obtain `hF2 : MemLp F 2 volume`. `Lp.ext`, `hF2.coeFn_toLp` and `Filter.EventuallyEq.symm h` then give `hF2.toLp F = q`. Now `Lp.norm_fourier_eq` and `Lp.inner_fourier_eq` (`Fourier/LpSpace.lean:91,95`) yield the classical norm and inner-product identities on L¹∩L². The corresponding inverse bridge follows from the inverse distributional API and the same pairing theorem with `L := -innerₗ ℝ`; no global integrability of the inverse transform is added.

The later cutoff argument can now use arbitrary L¹∩L² truncations, not just Schwartz inputs: their L² Fourier images equal their classical finite-interval integrals a.e. The actual L² cutoff convergence remains a separate obligation from this compatibility bridge.

Finally transfer this intermediate theorem to Rudin's normalized measure `m=dx/sqrt(2π)` and kernel `exp(-ixt)` using `U f(u)=f(sqrt(2π)u)`. The isometry of U and the identity `U F_R = F_M U` must be proved, as already recorded in `ch09-claims.md`. The compatibility argument itself only uses a.e. representatives, so it does not silently impose pointwise Borel measurability or continuity on Rudin's original Lebesgue-measurable f.

## Verification status and pitfalls

All cited signatures were read directly from the pinned source; this research does not claim the proposed adapter proofs elaborate. Root retains the compiler for Chapter 8.

- Keep the exact explicit `volume` on Lp types, as Mathlib's own LpSpace definition warns omission causes elaboration timeouts.
- Use `Filter.EventuallyEq.symm` explicitly when reversing an a.e. equality; this lane has seen `.symm` resolve to equality of null-measure propositions after unfolding.
- The distributional pairing is bilinear (`ψ • f`), whereas the Hilbert inner product is conjugate-linear in its first argument. The route above deliberately stays in the bilinear pairing until compatibility is proved.
- `Lp.ker_toTemperedDistributionCLM_eq_bot` compares two members of the same Lp space. Using it to compare q with the classical F before proving F∈L² would be circular. Local-integrable test uniqueness avoids this.
- An a.e. Fourier representative identity is the correct quotient-space conclusion. It cannot be upgraded to pointwise equality of arbitrary L² representatives.
