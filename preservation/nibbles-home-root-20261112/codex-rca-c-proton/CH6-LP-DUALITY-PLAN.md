# Static plan for RCA 6.15–6.17 at the pinned Mathlib

Read printed pp. 126–129 and inspected local Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`. This note is a proof plan, not formalized coverage. Compiler work is serialized under the root agent's one-compiler scheduling rule. The independent 6.4–6.6 implementation has passed the root's combined check (`books/rudin-real-and-complex-analysis/evidence/ch06-development-2.log`), with only permitted axioms; no further 6.4–6.6 check is needed from this agent.

## Existing support

- `ContinuousLinearMap.lpPairing` in `MeasureTheory/Function/Holder.lean:149` builds the continuous bilinear integral pairing for ENNReal conjugate exponents. `lpPairing_eq_integral` identifies its value with the integral. With the scalar complex multiplication bilinear map it gives the construction in 6.15. `norm_holderL_le` supplies its bound together with the norm bound on `L1.integralCLM'`.
- No full Lp-dual representation/surjectivity/isometry theorem was found. Searches covered all filenames containing Lp or Dual and all occurrences of StrongDual/Lp pairings and conjugate-exponent duality in Mathlib. `Holder.lean` provides a map *into* the dual, not onto it.
- `indicatorConstLp p hs hμs c`, `indicatorConstLp_empty`, `indicatorConstLp_disjoint_union`, `norm_indicatorConstLp`, `tendsto_indicatorConstLp_set` in `LpSpace/Indicator.lean` cover finite-measure indicator algebra and convergence.
- `Lp.simpleFunc.denseRange` and `Lp.induction` in `Function/SimpleFuncDenseLp.lean` establish density for `p ≠ ∞`. The same file explicitly has a TODO for finite-dimensional L∞ simple-function density; do not assume that wrapper exists.
- `Lp.ae_eq_of_forall_setIntegral_eq` in `Function/AEEqOfIntegral.lean:322` handles nonzero finite exponents. For the q=∞ endpoint, use `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` (`:270`) after establishing local integrability. This gives uniqueness up to a.e. equality, then Lp extensionality.
- `ae_le_of_forall_setIntegral_le` (`AEEqOfIntegral.lean:151`) is **real-valued** and assumes integrable functions. It is useful after introducing phase tests; it is not directly the complex assertion `|∫E g| ≤ C μ(E) ⇒ |g|≤C`.

## Faithful target

Use `p q : ℝ≥0∞`, `Fact (1 ≤ p)`, `p ≠ ∞`, and `ENNReal.HolderConjugate p q`, with `[SigmaFinite μ]`. For every complex continuous linear functional Φ on `Lp ℂ p μ`, produce unique `g : Lp ℂ q μ` with `Φ f = ∫ x, f x * g x ∂μ` for every f, and `‖Φ‖ = ‖g‖`. The pairing is bilinear, with no conjugation in the printed formula. In the Hilbert-space p=q=2 specialization, conjugate the Riesz representing vector as needed rather than silently switching to a sesquilinear pairing.

## Finite-measure proof route

1. Define λ(E)=Φ(indicatorConstLp p hE finite 1) on measurable E, and 0 elsewhere. Establish finite additivity via `indicatorConstLp_disjoint_union`. For a countably disjoint family, finite unions converge to the full union in symmetric-difference measure. `tendsto_indicatorConstLp_set` and continuity of Φ give countable additivity. Alternatively construct the vector measure through a countably additive-on-finite-sums constructor if its hypotheses fit exactly.
2. Null indicators are zero in Lp, so λ≪μ. Apply the Chapter 6 complex RN theorem to get integrable g with λ(E)=∫E g.
3. Extend equality from indicators to simple functions by linearity. Extend further to bounded measurable f using uniformly bounded simple approximations, dominated convergence against |g|, and convergence in Lp on finite μ. The existing L∞ density TODO means this step needs explicit approximation or its own lemma.
4. If p=1, test with bounded measurable phase-corrected indicators so that the integral becomes ∫E |g|. The norm bound becomes ∫E |g|≤‖Φ‖μ(E). The real integral-order theorem gives |g|≤‖Φ‖ a.e., hence g∈L∞ with the correct bound.
5. If 1<p<∞, use the printed bounded test `1_{|g|≤n} * |g|^(q−1) * phase(g)`, where phase(g)g=|g|. This yields `∫_{|g|≤n}|g|^q ≤ ‖Φ‖^q`. Monotone convergence establishes g∈Lq and `‖g‖≤‖Φ‖`. Care is needed at g=0 for real powers and phase.
6. Once g∈Lq, both sides are continuous Lp functionals. Use simple-function density or `Lp.induction` to extend the equality to every f. Hölder gives the reverse norm bound and therefore equality.

## σ-finite extension

The book transports through the finite equivalent measure `w μ` using multiplication by `w^(1/p)`. No ready-made weighted Lp linear isometric equivalence was located in the pinned source, so that route entails constructing and auditing it, including p=1 and inverse-weight integrability.

An alternative is compatible local RN densities on increasing finite spanning sets. Apply the finite theorem to the restrictions of Φ obtained from zero extension, prove the local densities agree on overlaps via uniqueness, glue them along disjoint increments, and use uniform bounds on the increasing union to prove the global Lq bound. This avoids a weighted-isometry implementation but still requires restriction/zero-extension maps and compatibility proofs. Neither route has been formalized here.

All four components of 6.16—existence, representation for every f, uniqueness as an Lq class, exact norm—remain required. Restricting to p=2, finite μ only, or assuming an integral representation would be partial coverage and must be reported as such.

## Concrete first helper

First construct the `Lp ℂ p μ`-valued vector measure `E ↦ indicatorConstLp p hE finite 1`, then apply `VectorMeasure.mapRangeL Φ` (`VectorMeasure/Operations.lean:281`). This separates measure additivity from the particular functional. `VectorMeasure` asks for an unconditional `HasSum`, so proving only natural partial-sum convergence is insufficient. For a family `E : ℕ → Set X`, use the directed index `F : Finset ℕ`, finite unions `U F = ⋃ i∈F, E i`, and remainders `R F = (⋃ i,E i) \ U F`. The latter decrease to ∅. `tendsto_measure_iInter_atTop` (`Measure/Continuity.lean:222`) gives μ(R F)→0; `symmDiff_of_le` identifies the needed symmetric difference. `tendsto_indicatorConstLp_set` then supplies convergence along *all* finite subsets, which is exactly `HasSum` after finite-disjoint-indicator additivity. Finiteness of μ gives all null-measurability and finite-mass obligations.

This construction is now drafted in `books/rudin-real-and-complex-analysis/Scratch616.lean`: `finiteLpIndicator_hasSum`, `finiteLpIndicatorVectorMeasure`, `finiteLpFunctionalMeasure`, its measurable-set evaluation, norm bound, and absolute continuity. The first aggregate check identified a missing classical decider and explicit structure-field binders; both have been patched. A clean passing check is still required, so it is not claimed as coverage of 6.16.

For the next bounded-test extension, `SimpleFunc.tendsto_approxOn_range_Lp` (`Function/SimpleFuncDenseLp.lean:189`) gives the Lp convergence of `approxOn`; `SimpleFunc.norm_approxOn_zero_le` (`:83`) bounds the approximations by twice the pointwise norm. Thus for bounded measurable f and integrable g, the products with g are dominated by `2C‖g‖`. `SimpleFunc.induction` (`Function/SimpleFunc.lean:1263`) reduces the initial identity on simple functions to constant indicators and disjoint addition. This supplies an explicit route around the unimplemented L∞ density wrapper.

## Draft implementation status

Ten scratch files now contain a complete proposed proof route, but **none of 6.16 is counted complete until the aggregate compilation and axiom audit pass**. The root's second aggregate check includes A–I; it does not include the later J equivalence or the subsequent local inference of the conjugate-exponent lower bound in I.

| File | Contents | Verification |
| --- | --- | --- |
| `Scratch616.lean` | Finite-measure indicator vector measure and scalar functional measure | Accepted with permitted axioms in `evidence/aggregate-2-mapped.log` |
| `Scratch616B.lean` | Simple-function and bounded-measurable test identity from indicator RN data | Accepted with permitted axioms in `evidence/aggregate-2-mapped.log` |
| `Scratch616C.lean` | Phase test and the p=1 essential-supremum bound | Accepted with permitted axioms in `evidence/aggregate-2-mapped.log` |
| `Scratch616D.lean` | Strict conjugate exponents, truncated phase tests, global Lq bound by `Lp.eLpNorm_le_of_ae_tendsto` | Aggregate 2 local-notation collision patched; recheck pending |
| `Scratch616E.lean` | Sigma-finite uniqueness, finite-measure full representation and exact norm | Uniqueness accepted; function-type annotation and reserved-token error patched; recheck pending |
| `Scratch616F.lean` | Linear isometric zero extension from a measurable restriction and functional restriction | Aggregate 2 heartbeat timeout; scoped budget increased; recheck pending |
| `Scratch616G.lean` | Measurable gluing of compatible local densities with uniform Lq bound | Accepted with permitted axioms in `evidence/aggregate-2-mapped.log` |
| `Scratch616H.lean` | Arbitrary-measure representation from finite indicators; indicator convergence along spanning sets | Density extension accepted; binder declaration patched; convergence recheck pending |
| `Scratch616I.lean` | Full sigma-finite `theorem_6_16`, including p=1/q=∞, representation, uniqueness, exact norm | Explicit AE-equality type patched; dependency and recheck pending |
| `Scratch616J.lean` | Explicit complex linear isometric equivalence from Lq to the continuous dual of Lp, with integral evaluation | Not compiled |

The sigma-finite implementation uses the existing measurable `spanningSetsIndex`, `mem_spanningSetsIndex`, and `eventually_mem_spanningSets`. Each finite restriction receives a representing density by the finite theorem. Zero extension bounds the local functional norm by the original norm. Set-integral uniqueness proves overlap compatibility; the measurable index glues the densities; Fatou bounds the global Lq seminorm. Continuity on the indicators of `E ∩ spanningSets μ n`, followed by simple-function density, extends representation to every Lp class. The theorem statement retains the full sigma-finite scope.

## Static fidelity audit of the full draft

The public theorem assumes only an arbitrary measurable space, a sigma-finite positive measure, `1 ≤ p`, `p ≠ ∞`, and Hölder conjugacy of p and q. The redundant `1 ≤ q` fact is now inferred locally from conjugacy in the public representation theorem and the equivalence wrapper. The pairing is the printed complex bilinear product `f * g`; uniqueness is equality in Lq, hence equality modulo null sets. The conclusion contains representation for every Lp class and exact norm equality. The J construction packages these properties into an actual complex linear isometric equivalence, rather than merely describing an abstract bijection.

There are no hypotheses that X is nonempty, countable, topological, standard Borel, or that the measure is complete. Countability enters only through a sigma-finite exhaustion and sequences; completeness and separability needed in scalar integration are supplied by ℂ. The p=1/q=∞ case has its own essential-supremum argument. Zero measure and the zero functional remain included: no step divides by the total mass, the functional norm, or an indicator norm; power cancellation first splits off the zero case; zero extension uses its unconditional operator-norm bound of at most one. Every major theorem family has an explicit axiom-audit command, with additional direct commands for phase and zero-extension helpers. These are statement and source audits only; they do not replace compiler verification.

## The unrestricted-measure claim in 6.15

The paragraph preceding 6.16 states that dual representation is affirmative for `1 < p < ∞` before restricting the exposition to sigma-finite measures. This is an additional required assertion, not covered merely by the numbered sigma-finite theorem. No analytic reflexivity or Lp uniform-convexity theorem was found in the pinned source. Two additional **uncompiled** files now draft the full unrestricted result:

- `Scratch615GeneralSupport.lean`: finite-exponent uniqueness on arbitrary measures, zero-extension support lemmas, a sigma-finite restriction capturing the full operator norm, and finite-q norm rigidity under restriction.
- `Scratch615General.lean`: `theorem_6_15_duality_arbitrary_measure` for every positive measure, `1 < p < ∞`, with unique Lq density, representation for every Lp class, and exact norm. It explicitly excludes p=1, while 6.16 retains that endpoint under sigma-finiteness.

The construction chooses a sequence of Lp functions of norm less than one whose functional values approach the operator norm. Their sigma-finite supports have a sigma-finite union S; the functional restricted to S has the same norm. The sigma-finite theorem produces a density on S. For any other Lp function f, enlarge S by a sigma-finite support of f and apply the sigma-finite theorem again. The enlarged density agrees with the original on S, where it already attains the full allowed Lq norm. Since q is finite, splitting the q-th-power integral forces the enlarged density to vanish off S. Thus the original zero-extended density represents the functional on every f. This argument uses neither ambient sigma-finiteness nor a completeness hypothesis, and works when the measure or functional is zero.
