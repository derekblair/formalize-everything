# Chapter 19.6–19.11 implementation research

Research date: 2026-10-29. **No Chapter 19 Lean source, checker, build, cache operation, installation, or removal was performed.** Chapter 18 remains the implementation gate. Every proposed lemma below is a plan, not a checked declaration. Existing Mathlib names are distinguished from proposed interfaces.

Source scope: printed Rudin, *Real and Complex Analysis*, third edition, §§19.6–19.11, pp. 377–383, in `scope-source-rudin.pdf` / `.txt`. The PDF hash and all numbered-node accounting are in `INVENTORY-19-20.md`. The final product/moment formulas on printed p. 383/PDF p. 396 were visually rechecked for this plan. In particular the printed moment bound has factor `1/π`; the inverse transform has factor `1/(2π)`.

All paths abbreviated `M/` mean `formalize-everything/books/rudin-real-and-complex-analysis/.lake/packages/mathlib/Mathlib/`. `git rev-parse HEAD` was rechecked as `d13f23b723b8a846827a245b89c10fc7d3f11612`. The API assessment below uses actual signatures and implementations at this pin. It does not assert a global theorem is unavailable solely because a name search failed.

## 1. Statements and representations to fix first

Use real derivatives of complex-valued functions throughout the class: `f : ℝ → ℂ`, `ContDiff ℝ ∞ f`, and `iteratedDeriv n f`. Complex derivatives enter only for holomorphic extensions and must be connected explicitly to these real derivatives.

A faithful convenient class predicate is:

- `M : ℕ → ℝ`, with positivity supplied separately;
- `f` is smooth;
- there exist real `β > 0`, `B > 0` such that for every natural `n` and every real `x`, `‖iteratedDeriv n f x‖ ≤ β * B^n * M n`.

This pointwise uniform bound avoids an unbounded-function supremum convention. It is equivalent to the book's supremum-norm formulation: each derivative is continuous by `ContDiff.continuous_iteratedDeriv`, and its displayed bound makes it a bounded continuous function. `BoundedContinuousFunction.mkOfBound` (`M/Topology/ContinuousMap/Bounded/Basic.lean:119`) requires a **diameter** bound, so a norm bound `C` supplies diameter bound `2C`; it does not accept a norm-bound proof directly. `BoundedContinuousFunction.norm_le_of_nonempty` (`.../Bounded/Normed.lean:91`) then gives the exact supremum-norm equivalence. Do not use plain `sSup` before proving boundedness.

Keep two hypothesis levels:

1. Arbitrary positive weights for 19.6's definition, vector space, affine invariance, and normalization by `M 0`.
2. Positive weights, `M 0 = 1`, and `M (n+1)^2 ≤ M n * M (n+2)` for 19.7 onward.

The second level must be an explicit hypothesis, not a consequence of the unrestricted regularization assertion, which is false. Bundle these hypotheses in a small proposed `WeightSequence` structure only after the basic predicate has been defined for arbitrary weights. No extra monotonicity, moderate-growth condition, derivative closure, or factorial lower bound should be inserted: none is a printed standing hypothesis. The class need not be stable under taking a derivative.

`Quasianalytic M` should quantify over every class member, all natural derivative orders including 0, and all real arguments in the zero conclusion. Its failure must supply an actual nonzero class member flat at 0. Pointwise equality on all of ℝ is required; almost-everywhere equality is insufficient here.

## 2. Exact derivative APIs and the class/algebra work

The following existing declarations are in `M/Analysis/Calculus/IteratedDeriv/Lemmas.lean`:

| Existing API | Hypotheses/result relevant here |
|---|---|
| `iteratedDeriv_add`, `iteratedDeriv_sub` (315, 336) | Require `ContDiffAt` at the requested finite order; give the pointwise derivative identities. |
| `iteratedDeriv_const_smul` (343), `iteratedDeriv_const_smul_field` (354) | The first permits complex scalars acting on a real normed space; the field variant removes smoothness assumptions when its commuting scalar hypotheses apply. |
| `iteratedDeriv_comp_const_smul` (397) | `ContDiff 𝕜 n f`; derivative of `f(c*x)` equals `c^n • Dⁿf(c*x)`, with general vector-valued target. This is the appropriate real-to-complex version; `...const_mul` has scalar-valued source/target. |
| `iteratedDeriv_comp_neg` (409) | Exact reflected derivative formula, including the `(-1)^n` factor. |
| `iteratedDeriv_mul` / `iteratedDeriv_fun_mul` (423) | Normed algebra target; finite binomial sum from 0 through `n`, with factors `Dⁱf * Dⁿ⁻ⁱg`. |
| `iteratedDeriv_comp_const_add`, `iteratedDeriv_comp_add_const` (459 onward) | Translation identities; the subsequent subtraction variants cover reflection plus translation. |
| `Filter.EventuallyEq.iteratedDeriv_eq` (439), `Set.EqOn.iteratedDeriv_of_isOpen` (444) | Locality, needed at points away from a glued boundary and outside support. |

`M/Analysis/Calculus/IteratedDeriv/Defs.lean:261–305` supplies `contDiff_iff_iteratedDeriv`, `contDiff_of_differentiable_iteratedDeriv`, `ContDiff.continuous_iteratedDeriv`, `ContDiff.differentiable_iteratedDeriv`, and `iteratedDeriv_succ`. The smoothness constructors in `ContDiff/Operations.lean` supply sums, products, constants, and affine compositions.

Proposed implementation order and explicit witnesses:

1. Zero and constant functions. A zero function still needs positive witnesses. Constants use `β ≥ ‖c‖/(M 0)` and any positive `B`; positive-order derivatives vanish.
2. Addition: `β = β_f + β_g`, `B = max B_f B_g`. Scalar multiplication: `β = max 1 ‖c‖ * β_f`, `B = B_f`, handling `c = 0` automatically. Package a complex submodule if useful.
3. Translation retains both constants. General affine composition uses `β_g = β_f`, `B_g = max 1 |a| * B_f`. This covers negative and zero slopes and proves the real derivative formula first.
4. Normalize arbitrary positive `M` to `M n / M 0`; adjust `β` in each direction. This normalization is valid without log convexity, unlike the unrestricted combined normalization/log-convexity assertion.
5. Supremum-norm/pointwise-bound equivalence, followed by the printed limsup estimate. Work with positive indices `n+1`, estimate the root by `β^(1/(n+1)) * B`, and prove the first factor tends to 1 using continuity of real powers at exponent 0. Eventual boundedness and nonnegativity must be supplied to real `limsup`; the finite initial term is irrelevant. The book gives the forward estimate, not an unconditional converse from a limsup of possibly infinite derivative norms.
6. For positive normalized log-convex weights, define `r n = M(n+1)/M n`. Prove positivity, `Monotone r`, and `M n = ∏ i<n, r i` by telescoping. From `r(i+j) ≥ r i`, derive `M j * M k ≤ M(j+k)`. The special case `k=n-j`, `j≤n`, is what the Leibniz formula needs.
7. Apply the binomial norm estimate with witnesses `β_f β_g`, `B_f+B_g`. Existing Leibniz and finite binomial identities handle the derivative expansion; the weight inequality is new. This proves 19.7 and permits a complex subalgebra of functions, with pointwise multiplication.
8. Translation and its inverse prove base-point invariance in both directions for 19.8. Preserve all derivative orders, including the value at the base point.

A ratio-product proof is preferable to encoding discrete log convexity through `ConvexOn` on a real interpolation: it needs only positive divisions, monotone sequences, induction, and finite products. The inspected convexity files do not provide the exact sequence-class package needed here.

## 3. The two 19.6 defects: formal counterexamples first

### Affine witness

The printed choice `B_g = a B_f` is not positive when `a≤0`. For `a=-1`, `M n=1`, and `f(x)=exp(i x)`, the first-derivative norm is 1 while the proposed right side is -1. Prove the counterexample to this witness and separately prove the valid affine-invariance conclusion with the absolute-value/max witness above. Do not describe the true invariance conclusion itself as false.

### Unrestricted regularization

**Research argument only; not yet Lean-proved.** Let `M n = exp(-(n:ℝ)^2)`. It is everywhere positive and normalized. Let `u(x)=exp((x:ℂ)*I)`.

1. Prove `Dⁿu(x) = I^n * u(x)` by induction. `Complex.hasDerivAt_exp` (`M/Analysis/SpecialFunctions/ExpDeriv.lean:89`), `HasDerivAt.comp_ofReal` (`M/Analysis/Complex/RealDeriv.lean:97`), scalar/product derivative rules, and `iteratedDeriv_succ` suffice. `Complex.norm_exp_ofReal_mul_I` (`M/Analysis/Complex/Trigonometric.lean:950`) gives norm 1 at every order.
2. For every positive normalized log-convex `N`, the ratio-product lemmas give `N n ≥ (N 1)^n`. Hence `u` belongs to its class with `β=1`, `B=1/N 1`.
3. If `u` belonged to the original class, its bound at just `x=0` would imply `1 ≤ β B^n exp(-n²)` for all `n`. Rewrite the right side as `exp(log β + n*log B - n²)` using positivity.
4. A particularly elementary decay proof avoids a special quadratic-limit API: eventually `n ≥ max 0 (log B + 1)`, so `n*log B - n² ≤ -n`. Bound the right side by `β*exp(-n)`; this tends to 0 by `Real.tendsto_exp_atBot` (`M/Analysis/SpecialFunctions/Exp.lean:230`) composed with the negated natural-cast limit. The inequality `1≤...` is impossible eventually.
5. Thus no positive normalized log-convex `N` can define the same class as this positive `M`. The theorem to discharge the defect should explicitly negate existence of such an `N` with equality of the two classes; no arbitrary axiom or weakened “chosen construction fails” claim suffices.

A necessary missing hypothesis for equivalence to a positive normalized log-convex class is an exponential lower bound `∃ c>0, ∃ r>0, ∀ n, c*r^n ≤ M n`. In fact this is exactly the condition that `u` belongs to the original class, by rearranging `1≤β B^n M n`; positivity makes both directions elementary. Its positive-index root-liminf formulation can be added later, but is not needed for the counterexample. **No proof that this added hypothesis is sufficient for full regularization has been found or asserted here.** Do not replace the false assertion with an unproved sufficiency claim. The later theorems use their explicit standing log-convex assumptions and remain meaningful independently of this defect.

## 4. Flat gluing and 19.10

No ready “smooth zero extension of an infinitely flat half-line function” theorem was identified in the inspected derivative, support, and smoothness files. There is a short route using existing one-sided derivative gluing; a new general piecewise-contDiff engine is unnecessary.

For smooth `f` flat at 0, define the proposed cutoff operation `g(x)=f(x)` for `0≤x`, and `0` otherwise. Define auxiliary `g_n(x)` by the same cutoff of `Dⁿf`.

- At `x>0`, `g_n` locally equals `Dⁿf`; at `x<0`, it locally equals zero. Local derivative congruence gives derivative `g_(n+1)`.
- At 0, use the derivative of `Dⁿf` restricted to `Ici 0`; it is 0 because `Dⁿ⁺¹f(0)=0`. On `Iic 0`, `g_n` agrees with the constant zero function, including the endpoint because `Dⁿf(0)=0`.
- `HasDerivWithinAt.congr` / `.congr_of_mem` (`M/Analysis/Calculus/Deriv/Basic.lean:557–563`) transport those two derivatives. `HasDerivWithinAt.union` (`:405`) combines them; `Ici 0 ∪ Iic 0 = univ`, followed by `hasDerivWithinAt_univ` (`:391`), gives the ordinary derivative.
- Inductively identify `iteratedDeriv n g = g_n` using `.deriv` and `iteratedDeriv_succ`. Every `g_n` is differentiable, so `contDiff_of_differentiable_iteratedDeriv` proves smoothness. The same `β,B` bound each `g_n` because each value is either the original derivative or zero. This proves class membership with no lost growth factors.

For 19.10, the forward implication uses a point outside the compact `tsupport f`; on a neighborhood there the function is zero, so all its derivatives vanish by locality. Apply 19.8 at that point. `M/Analysis/Calculus/Deriv/Support.lean:49–57` also provides `deriv_of_notMem_tsupport` and `tsupport_deriv_subset`; either locality or inducting those support containments works.

For the reverse implication, failure of quasi-analyticity supplies `f` flat at 0 and `f(x₀)≠0`. Necessarily `x₀≠0`; reflect if necessary to make `x₀>0`, using the corrected affine result. Set `h(x)=g(x)*g(2*x₀-x)`. Class closure follows from affine invariance and 19.7. It vanishes outside `[0,2*x₀]`, so its topological support is contained in that closed compact interval. At `x₀`, its value is `f(x₀)^2≠0`. This proves nontrivial compact support inside the specified class. An unrelated smooth bump cannot replace this argument.

## 5. 19.9: bounded strip extensions

Use `Strip b = {z : ℂ | |z.im| < b}` and an extension `F : ℂ → ℂ` with `DifferentiableOn ℂ F (Strip b)`, agreement on every real point, and one uniform bound on that strip. Values outside the strip are irrelevant. Do not require entire extension or merely boundedness on compact substrips.

### Bounded holomorphic extension implies factorial class

Choose an interior circle radius `R=b/2`, independent of the real center. The closed disk around any real `a` lies in the strip, so differentiability there supplies `DiffContOnCl`. Apply `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (`M/Analysis/Complex/Liouville.lean:44`), whose exact conclusion is `‖DⁿF(a)‖ ≤ n! * C / R^n`.

A new restriction lemma must identify every real iterated derivative of `x↦F(x:ℂ)` with the complex iterated derivative at real points. Prove it inductively from `HasDerivAt.comp_ofReal`, holomorphic analyticity/smoothness on the open strip, and derivative locality; a global entire hypothesis would be too strong. `DifferentiableOn.real_of_complex` (`M/Analysis/Complex/RealDeriv.lean:141`) is only restriction of the scalar field on a complex domain; it is **not by itself** the iterated real-line restriction identity. The smooth restriction follows locally by composing the real linear inclusion with complex smoothness restricted to real scalars. Use `β=max 1 C`, `B=1/R`.

### Factorial class implies bounded holomorphic extension

Given `β,B>0`, put `r=1/B` and define local Taylor sums
`F_a(z)=Σ_n (Dⁿf(a)/(n!:ℂ))*(z-a)^n` for each real `a`.

1. **Real Taylor convergence.** `taylor_integral_remainder` (`M/Analysis/Calculus/Taylor.lean:534`) works for the vector-valued target ℂ, any orientation of the real segment, and finite smoothness on `uIcc`. Derive the exact geometric remainder estimate by integrating the power kernel. Alternatively `taylor_mean_remainder_bound` (`:390`) gives a slightly weaker but sufficient `(n+1)*β*(B|x-a|)^(n+1)` bound: its denominator is `n!`, not `(n+1)!`. Use `tendsto_self_mul_const_pow_of_lt_one` (`M/Analysis/SpecificLimits/Normed.lean:218`). Do not cite the real-valued Lagrange theorem for a complex-valued function. Identify within derivatives on nondegenerate closed intervals with the global derivatives; handle `x=a` separately.
2. **Holomorphy of each disk sum.** On every smaller ball of radius `ρ<r`, the summands have norms ≤`β*(Bρ)^n`. `differentiableOn_tsum_of_summable_norm` (`M/Analysis/Complex/LocallyUniformLimit.lean:171`) applies to this summable geometric majorant and holomorphic polynomial summands. Use smaller balls locally to obtain differentiability on the radius-`r` disk. No full formal-multilinear-series construction is needed; `FormalMultilinearSeries.ofScalars` remains an alternative, with explicit radius obligations.
3. **Compatibility.** Intersecting radius-`r` disks with real centers have convex, hence preconnected, intersection and contain a nonempty open real interval. Both sums agree with `f` on that interval. `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (`M/Analysis/Analytic/IsolatedZeros.lean:238`) gives equality on the whole overlap. Supply an explicit accumulating sequence of distinct real points in the overlap; equality merely at one real point is insufficient.
4. **Glue.** Define `F(z)=F_(z.re)(z)` on `Strip r`. The overlap lemma proves that near any point this function equals a fixed center's disk sum; local equality gives holomorphy. The varying-center formula alone does not justify holomorphy.
5. **Uniform boundedness.** Restrict to `b=r/2`. Expanding at `a=z.re` yields `‖F(z)‖≤Σ β*(B|z.im|)^n≤2β`. Thus the required extension is uniformly bounded on one positive-width strip. The initially constructed width-`r` extension need not be bounded on that full strip.
6. **Quasi-analytic consequence.** If all real derivatives at 0 vanish, the center-0 Taylor sum is zero on a disk. Propagate zero over the connected strip via `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` (`M/Analysis/Analytic/Uniqueness.lean:204`), then restrict to ℝ. This avoids a second real-to-complex derivative comparison for the zero-jet step. An alternative uses analytic order (`M/Analysis/Analytic/Order.lean:75,333`), but the already-built Taylor sum is simpler.

## 6. Faithful extended quantities for 19.11

For `x≥0`, define `Q x : ℝ≥0∞` as the ENNReal sum of `ofReal(x^n/M n)` and `q x` as the ENNReal supremum of those terms. Include `n=0`: normalization makes `1≤q≤Q`. Define the nonnegative extended logarithms by `(ENNReal.log (Q x)).toENNReal` and similarly for `q`. This is faithful because those logarithms are nonnegative. The integrals are Lebesgue `lintegral` over `Ioi 0`, multiplying by `ENNReal.ofReal ((1+x^2)⁻¹)`; conditions (b),(c) are strict comparison with `⊤`.

The pin already contains:

- `ENNReal.log`, `log_top`, `log_ofReal_of_pos`, `log_monotone`, `zero_le_log_iff` in `M/Analysis/SpecialFunctions/Log/ENNRealLog.lean:46–125`. The result type is **EReal**, with `log ⊤=⊤`; it is not the totalized real logarithm.
- `ENNReal.continuous_log`, `ENNReal.measurable_log`, `Measurable.ennreal_log` in `.../ENNRealLogExp.lean:120,172,178`.
- `Measurable.ereal_toENNReal` in `M/MeasureTheory/Constructions/BorelSpace/Real.lean:444` and `EReal.coe_toENNReal` in `M/Data/EReal/Basic.lean:734`, the latter requiring nonnegativity.
- Countable sum/supremum measurability and nonnegative integral monotonicity. Terms are continuous on the positive half-line; explicit measurable extensions to ℝ can use `max x 0` or the restricted measure.

Prove agreement with real logarithms/integrals when finite. Never coerce `Q` or `q` to real before proving finiteness: `toReal ⊤=0` would erase precisely the divergent case. If `Q(x₀)=⊤` for positive `x₀`, monotonicity makes it infinite on an entire positive-measure tail, so condition (b) fails. A single infinite value alone would not force an infinite Lebesgue integral; the monotonicity argument is essential.

Index positive-root and ratio series using `n+1`: `a_n=M(n+1)^(1/(n+1))`, `λ_n=M n/M(n+1)`. Their positivity and convergence are ordinary real `Summable` assertions. State reindexing to the book's series starting at 1 explicitly.

## 7. Five-condition chain and precise missing lemmas

Prove the cycle `(a)→(b)→(c)→(d)→(e)→(a)` and derive all equivalences from it. None of the five conditions should be an additional hypothesis of the final equivalence theorem.

### (a) → (b): compact support and the boundary logarithm

1. Obtain a nonzero compactly supported member from 19.10. Affine scaling, translation, and scalar multiplication produce a smooth `F` supported in `[0,A]`, `A>0`, with `‖DⁿF‖∞≤2⁻ⁿ M n`. For example scale the argument by `1/(2B_f)` and the amplitude by `1/β_f`, then translate its support. Prove that nontriviality survives the invertible changes.
2. Define `f(z)=∫ F(t)*exp(I*t*z) dt`. Chapter 19.1's compact-support transform construction gives entire holomorphy; the support half-line gives a bound `A` on the upper half-plane. All derivatives of `F` have compact support and are integrable.
3. Establish `|x|^n ‖f(x)‖≤A*2⁻ⁿ*M n`. A normalized adapter for `Real.fourier_iteratedDeriv` (`M/Analysis/Fourier/FourierTransformDeriv.lean:818`) avoids repeating integration by parts. Its hypotheses are smoothness and integrability of **every** iterated derivative through the desired order; compact support supplies these. Alternatively prove the interval integration-by-parts formula with both boundary jets zero. Do not divide by `x` at 0; use the multiplied inequality.
4. Use Fourier injectivity/inversion to show `f` is nonzero. The original compactly supported smooth `F` has rapidly decaying transform: two integrations by parts already give an L¹ majorant. `MeasureTheory.Integrable.fourierInv_fourier_eq` (`M/Analysis/Fourier/Inversion.lean:165`) then applies, including its continuity hypothesis. Nontriviality does not follow just from a pointwise norm upper bound.
5. **Substantial new prerequisite:** bounded nonzero holomorphic functions in the disk, continuous at all boundary points except possibly one, have integrable negative boundary logarithm. This is printed 15.19 in the book's proof. The pin's `AnalyticOnNhd.circleAverage_log_norm` (`M/Analysis/Complex/JensenFormula.lean:375`) is Jensen's formula on each closed interior disk with nonzero center value; its signature is not the boundary theorem. Derive uniform interior logarithmic lower bounds, handle a zero at the center by factoring its finite order (or an explicit disk automorphism), and use Fatou on a nonnegative expression such as `log(C/|g|)`. `MeasureTheory.lintegral_liminf_le` (`M/MeasureTheory/Integral/Lebesgue/Add.lean:233`) is the needed limit tool. At boundary zeros the negative logarithm is infinite; an ENNReal/EReal formulation or a proved a.e. nonvanishing reduction must preserve this rather than use `Real.log 0=0` blindly.
6. Apply that prerequisite to `g(w)=f(I*(1-w)/(1+w))`. Prove the Cayley mapping, boundary continuity away from `w=-1`, and nontriviality. Substitution `x=tan(θ/2)` gives the weighted real-line logarithm. `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul` (`M/MeasureTheory/Function/JacobianOneDim.lean:44`) requires measurability of the source set, injectivity there, and a within-derivative formula; the injective interval is `(-π,π)`. Its image is ℝ. A single deleted endpoint is null.
7. Sum the derivative estimates to get `Q(x)*‖f(x)‖≤2A` wherever the product is meaningful. Prefer partial sums first, then monotone limits. For a.e. real `x` with `f(x)≠0`, infer a bound on `log Q(x)` by a constant plus the negative logarithm of `f`. `integrable_inv_one_add_sq` and `integral_univ_inv_one_add_sq` (`M/Analysis/SpecialFunctions/ImproperIntegrals.lean:274,292`) control the constant. This proves the extended integral finite.

### (b) → (c): direct comparison

Each nonnegative term of `Q` is ≤ its sum, so `q≤Q`. Apply monotonicity of the extended logarithm and the nonnegative weighted integral. No finiteness conversion to real is needed.

### (c) → (d): roots and a finite layer-counting bound

New sequence lemmas: `a_n` is positive and nondecreasing. Use monotone successive ratios and telescoping to prove `M(n+1)^n ≥ M(n)^(n+1)` for positive `n`, then positive real roots. The exact root identities are `Real.rpow_inv_natCast_pow` and `Real.pow_rpow_inv_natCast` (`M/Analysis/SpecialFunctions/Pow/Real.lean:509–515`); both need nonnegativity and a nonzero natural exponent.

For the book's positive indexing, `x≥e*a_n` implies `log q(x)≥n`. A convenient finite-sum proof of the printed telescoping estimate is to bound the counting function `Σ_(n=1)^N 1_[e*a_n,∞)(x)` by `log q(x)`. Monotone thresholds make its nonzero terms an initial segment, even when consecutive thresholds coincide. Integrating against `x⁻²` gives `(1/e) Σ_(n=1)^N 1/a_n`.

On the tail `x≥c=e*a_1>0`, `x⁻² ≤ (1+c⁻²)/(1+x²)`. Thus condition (c) bounds these partial sums uniformly. `integral_Ioi_rpow_of_lt` (`M/Analysis/SpecialFunctions/ImproperIntegrals.lean:178`) evaluates the tail of `x⁻²`, with exponent `<-1` and positive endpoint. `summable_of_sum_range_le` (`M/Topology/Algebra/InfiniteSum/Real.lean:91`) converts nonnegative bounded partial sums into summability. Working in ENNReal until the common finite bound is obtained avoids assuming `log q` is finite everywhere.

This route needs finite indicator-integral and reindexing lemmas but avoids an infinite layer-cake theorem and avoids dividing by `a_(n+1)-a_n`.

### (d) → (e): a short sequence comparison

For positive indexing let `λ_n=M(n-1)/M n`. Log convexity gives `λ_1≥λ_2≥...>0`, and telescoping gives `∏_(j=1)^n λ_j=1/M n`. Consequently `λ_n^n≤1/M n`, hence `λ_n≤1/a_n`. A nonnegative series comparison proves (e). The `n=0` case is excluded by the positive indexing; do not manufacture an inverse zeroth root.

### (e) → (a): entire sinc product and its Fourier transform

This is the other substantial construction. It uses 19.3, not just abstract L² Plancherel.

1. Construct a **complex entire sinc** with value 1 at 0. The inspected `Real.sinc` file (`M/Analysis/SpecialFunctions/Trigonometric/Sinc.lean`) is real-valued and supplies continuity and `|sinc x|≤1`; it is not an entire complex sinc declaration. Define the complex function via `dslope Complex.sin 0`; `Complex.differentiableOn_dslope` (`M/Analysis/Complex/RemovableSingularity.lean:60`) handles the removable point. Prove its agreement with `sin z/z` off 0 and with real sinc on ℝ.
2. Prove the integral identity `sinc z=(1/2)∫_(−1)^1 exp(I*t*z) dt`, including `z=0`. It gives `‖sinc z‖≤exp(|Im z|)` and, using `Complex.norm_exp_sub_one_le` (`M/Analysis/Complex/Exponential.lean:440`), a local linear estimate `‖sinc z-1‖≤C‖z‖` for `‖z‖≤1`. A Taylor-series estimate is an alternative. These are new complex-sinc lemmas, not consequences of the real inequality alone.
3. With positive summable `λ_n`, form `P(z)=sinc(z)^2 * ∏_(n≥1) sinc(λ_n*z)`. On a compact set of radius bound `R`, the factors minus 1 are eventually bounded by `C R λ_n`. `Summable.hasProdUniformlyOn_nat_one_add` (`M/Analysis/Normed/Module/MultipliableUniformlyOn.lean:116`) gives uniform product convergence on that compact set, using continuity of every factor. This theorem allows zeros in finitely many factors; the `hasProdUniformlyOn_of_clog` variant requires all factors nonzero and is inappropriate globally because sinc has zeros. Convert finite-range product convergence to locally uniform convergence on ℂ, then apply `TendstoLocallyUniformlyOn.differentiableOn` (`M/Analysis/Complex/LocallyUniformLimit.lean:136`). At 0 every factor is 1, so `P(0)=1` proves nontriviality without a global nonvanishing theorem.
4. Finite products satisfy `‖P_N(z)‖≤exp((2+Σ_(n<N)λ_n)*|Im z|)`. Pass to the limit, obtaining exponential type `A=2+Σλ_n>0`. The stronger imaginary-part bound implies the radial bound required by 19.3.
5. For real `x`, use `|sinc(λ_n x)|≤1` for all factors and `|x|*|sinc(λ_n x)|≤1/λ_n` for the first `k` factors. Pass finite-product estimates to the limit to obtain `|x|^k ‖P(x)‖≤M k*(Real.sinc x)^2`. Prove the zero-input case before cancelling `x`, and retain the normalization `M 0=1` in the telescoping product.
6. All moments are integrable. One feasible proof bounds `sinc²` by 1 on `[-1,1]` and by `x⁻²` on the two tails, giving a fixed finite integral constant. The printed proof uses the sharper integral `∫sinc²=π`; this plan has not identified or proved that exact identity in the pin. The weaker common constant is enough for the **theorem statement**, since it is absorbed into the permitted `β` of the class. If the sharp intermediate printed moment bound is recorded as an obligation, prove the sinc-square integral separately (for example by an explicitly normalized Fourier/Plancherel argument); do not label the weaker bound as that exact formula. `MeasureTheory.Function.SpecialFunctions.Sinc.integrable_sinc` is only for **finite measures** and does not assert Lebesgue integrability of sinc on ℝ.
7. The `k=0` bound also gives `P|ℝ∈L²`: boundedness plus L¹ integrability, or domination by an integrable square envelope. Apply the completed 19.3 to get a compactly supported L² coefficient representative. Separately define the pointwise integral `F(t)=(1/(2π))∫ P(x)*exp(-I*t*x) dx`.
8. Prove that this continuous integral transform agrees a.e. with the 19.3 coefficient function using the Chapter 19 Fourier normalization/inversion adapters. Since it is continuous and zero a.e. on the open complement of the compact interval, it is zero everywhere there. This gives genuine `HasCompactSupport F`, rather than only essential support of an L² class. A representation alone does not automatically identify this chosen pointwise transform.
9. `contDiff_fourier` (`M/Analysis/Fourier/FourierTransformDeriv.lean:704`) needs all moment norms integrable; `Real.iteratedDeriv_fourier` (`:802`) gives the derivative formula. For the book's convention use the adapter `F(t)=(1/(2π))*𝓕(P|ℝ)(t/(2π))`; the affine derivative factors cancel the `2π` factors in the existing theorem. Conclude one bound `‖DᵏF‖∞≤β*M k`, hence class membership with `B=1`.
10. Fourier inversion and `P(0)=1` show `F` is nonzero. Compact-support 19.10 then gives (a).

## 8. Work packages and completion evidence

| Order after the Chapter 18 gate | Deliverable | Main dependency / acceptance condition |
|---|---|---|
| 1 | Class predicate, pointwise/sup equivalence, vector/affine lemmas, limsup estimate | All 19.6 positive-weight clauses; zero and negative affine slopes included. |
| 2 | Both 19.6 formal defect witnesses; valid normalization | Unrestricted regularization negated for the explicit positive sequence. No unproved repaired equivalence. |
| 3 | Ratio-product estimates, algebra, translation of flatness | 19.7 and every clause of 19.8. |
| 4 | Flat zero-extension and support argument | Full two directions of 19.10, without assuming arbitrary-weight bump existence. |
| 5 | Real/complex derivative restriction, Taylor disks, gluing, strip bound | Full 19.9 equivalence and quasi-analytic consequence. |
| 6 | Extended Q/q, measurability, root/ratio estimates, (b→c→d→e) | Three implications can be developed before the Fourier constructions. |
| 7 | Boundary logarithm prerequisite and normalized compact transform | Full (a→b), including nontriviality and null-set handling. |
| 8 | Complex sinc, uniform product, exponential/moment estimates | Entire function with value 1 at 0, correctly quantified bounds. |
| 9 | 19.3 representation + pointwise Fourier/support adapters | Full (e→a), smooth compact support and uniform derivative growth. |
| 10 | Cycle-to-five-way equivalence, divergent-Q note, factorial example | Every one of the five conditions equivalent; harmonic-series divergence gives the `n!` corollary. |

No package should be marked complete on the strength of this plan, an API name match, or a statement taking one of the missing conclusions as an extra premise. Later validation should capture the exact source hash, a completed Lean check with exit status, and axiom reports for the public statements. The final chapter audit must include the formal counterexamples/corrections and retain the numerical node inventory. The most uncertain effort is in the boundary-log theorem and the pointwise compact-support Fourier adapter, followed by the sinc-product development; the class closure and flat gluing have much shorter explicit proof paths.
