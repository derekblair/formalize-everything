# Research route for 9.18–9.23

Research only, before the Chapter 8 gate. Based on the printed pp.190–193 and the pinned Mathlib checkout. No Chapter 9 implementation or compiled claim is asserted here.

## All six nodes

| Node | Required endpoint | Route / principal remaining obligation |
|---|---|---|
| 9.18 | Nonunital complex Banach algebra, with all printed multiplication laws and norm inequality | `NonUnitalNormedRing`, `NormedSpace ℂ`, `IsScalarTower`, `SMulCommClass`, `CompleteSpace`. Do not build the unit into this definition. |
| 9.19(a) | C(X) is commutative, unital, complete for compact Hausdorff X | Existing continuous-map instances; preserve compactness and complex scalars. |
| 9.19(b) | C₀(ℝ) is commutative and has no unit | Existing zero-at-infinity algebra instances. For a hypothetical unit u, a compact bump nonzero at each x forces u(x)=1. Constant one cannot vanish at infinity on ℝ. |
| 9.19(c) | Continuous-linear endomorphisms are a unital Banach algebra; noncommutative on ℝᵏ for k>1 | Existing endomorphism instances. Matrix units E₀₁ and E₁₀ give explicit noncommutation with two distinct indices. |
| 9.19(d) | Convolution L¹ is commutative Banach algebra, Fourier embedding is injective algebra map, no unit | New quotient multiplication, integrability, norm, and a.e. algebra laws. Fourier identities and uniqueness prove associativity/commutativity and embedding. No unit follows from the same localized-character argument and Riemann–Lebesgue. |
| 9.20 | Algebra homomorphism without a continuity hypothesis, including the zero map | `NonUnitalAlgHom ℂ A ℂ`. |
| 9.21 | Automatic continuity and operator norm ≤1, including nonunital A | L¹ norm on `WithLp 1 (Unitization ℂ A)`, `Unitization.lift`, `WithLp.unitizationAlgEquiv`, `AlgHom.norm_apply_le_self`, `WithLp.unitization_norm_inr`. Default regular-norm unitization is not sufficient. |
| 9.22 | A bounded representative β, continuous and multiplicative when φ≠0, hence β(x)=exp(-itx) | Translation-orbit construction below replaces the need for a general L¹-dual representation theorem while proving the stated representation itself. |
| 9.23 | Every nonzero homomorphism is Fourier evaluation at one unique real frequency; evaluations themselves are nonzero homomorphisms | Finish all representation/classification directions. Do not start with a bounded φ or assume it is a Fourier evaluation. |

## Translation-orbit construction

Let T_y h(x)=h(x-y) on the quotient L¹, and take h with φ(h)≠0. After 9.21 supplies continuity, define

    β(y) = φ(T_y h) / φ(h).

Translation continuity (9.5) gives continuity of β. The translation isometry and the norm bound for φ give a uniform bound. The convolution identity

    (T_y f) * h = f * (T_y h)

and multiplicativity imply φ(T_y f)=φ(f)β(y), by division by φ(h). This works for every f, not only the chosen h. Apply it twice to obtain β(x+y)=β(x)β(y); β(0)=1. Thus β never vanishes.

The Bochner integral identity in L¹

    f * h = ∫ y, f(y) • T_y h dm(y)

then yields φ(f)φ(h)=φ(h)∫fβ, so φ(f)=∫fβ. Integrability of the L¹-valued function follows from strong measurability of the orbit and ‖f(y)T_yh‖=|f(y)|‖h‖.

This L¹-valued integral identity is a substantive bridge: point evaluation is not continuous on L¹. A direct L¹ curry/Fubini theorem was not found. A viable proof uses continuous linear set-integral maps:

- `LpToLpRestrictCLM` and its a.e. representative identity: `MeasureTheory/Integral/Bochner/Set.lean:998,1006`.
- `L1.integralCLM' ℂ`: `MeasureTheory/Integral/Bochner/L1.lean:529`.
- `ContinuousLinearMap.integral_comp_comm`: `MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:69`.
- Scalar/complex Fubini identifies the resulting integrals over every measurable set of finite measure.
- `Lp.ae_eq_of_forall_setIntegral_eq`: `MeasureTheory/Function/AEEqOfIntegral.lean:322`, then `Lp.ext`.

The `LConvolution` file is ENNReal convolution of ordinary functions; it does not supply this Banach-valued L¹ identity.

## Continuous multiplicative β is an exponential

No direct classification theorem for continuous bounded multiplicative ℝ→ℂ functions was found in the pinned character/Pontryagin/complex-circle files. The printed FTC argument is practical:

1. Let C(x)=∫₀ˣβ(y)dy. Continuity gives C'(x)=β(x) using `intervalIntegral.integral_hasDerivAt_right` (`FundThmCalculus.lean:725`).
2. Some δ has c=C(δ)≠0. Otherwise C is identically zero and differentiating at 0 contradicts β(0)=1. If a positive δ is needed explicitly, a negative one can be reflected using multiplicativity and β(-δ)≠0.
3. Change of variables and multiplicativity give cβ(x)=C(x+δ)-C(x). The exact adapter is `intervalIntegral.integral_comp_add_right` (`Basic.lean:956`). Hence β is differentiable everywhere.
4. Differentiate β(x+y)=β(x)β(y) in y at zero. With λ=β'(0), obtain β'(x)=λβ(x).
5. Differentiate β(x)exp(-λx), and apply `is_const_of_deriv_eq_zero` (`Analysis/Calculus/MeanValue.lean:751`). Initial value 1 gives β(x)=exp(λx).
6. Boundedness on both positive and negative x forces Re λ=0, so λ=-it for a real t. Alternatively first derive |β(x)|=1 from bounded powers and β(-x)β(x)=1.

Frequency uniqueness can be reduced to equality of these characters through the same translated h and then differentiated at zero. This avoids requiring an extra explicit Fourier test function solely for uniqueness. The converse nonzero-evaluation direction still needs a test function; the Poisson/exponential transform pair of 9.7 supplies one at every frequency.

## Two useful simplifications for the examples

For 9.19(d), the single function H(x)=exp(-|x|) has transform h₁(t)>0 at every real t by 9.7. A convolution identity u*H=H therefore forces û(t)=1 for every t; Riemann–Lebesgue contradicts this. No use of the later 9.23 classification and no separate family of test functions is required for the no-unit proof.

For 9.19(b), a compactly supported bump equal to one at x forces a hypothetical unit u to satisfy u(x)=1. `Topology/ContinuousMap/CompactlySupported.lean:658` supplies `ZeroAtInftyContinuousMapClass` for compact-support maps. The constant-one contradiction uses `Filter.cocompact` being nontrivial on the noncompact real line (`Topology/Compactness/Compact.lean:884`) and uniqueness of limits.

## Dependency-efficient L¹ algebra construction

At 9.19, Fourier injectivity (9.12) and the convolution/product identity (9.2(c)) are already available. After defining convolution on the L¹ quotient and proving its norm bound, use the injective Fourier map to establish every algebra identity: associativity, commutativity, distributivity, and scalar compatibility. This is the printed argument and avoids proving general pointwise associativity of the totalized Bochner convolution. A dedicated `ConvolutionL1` type synonym can carry multiplication while preserving the existing Lp additive/normed structure. Fourier values depend only on a.e. equivalence; all multiplicative identities are equalities in the quotient.
