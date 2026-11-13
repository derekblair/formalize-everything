# Cluster G, Chapter 15 — pinned Mathlib claims map

Checked 2026-10-29. Mathlib clone: `formalize-everything/books/rudin-real-and-complex-analysis/.lake/packages/mathlib`; `git rev-parse HEAD` returned `d13f23b723b8a846827a245b89c10fc7d3f11612`. Paths below are relative to that clone. This is a source/signature claims check, not a completed Lean formalization or axiom audit. The numbered inventory is being independently transcribed by the printed-inventory agent.

## Numbered-node map, earliest first

| Node | Printed content | Coverage at the pin |
|---|---|---|
| 15.1 | Isolated zeros recap and Weierstrass motivation | Isolated-zeros and identity principles already proved; existence of an entire function with arbitrary prescribed discrete zeros not found. See A. |
| 15.2 | Infinite product as limit of ordered partial products, including zero | Must introduce/use sequential convergence explicitly. Mathlib `HasProd` is unconditional convergence over finite subsets. It implies sequential convergence; the converse is only provided under `Multipliable`. `tprod` alone has no convergence content and defaults to **1** for nonmultipliable families. See B. |
| 15.3 | `∏(1+‖u‖) ≤ exp Σ‖u‖`; `‖∏(1+u)-1‖ ≤ ∏(1+‖u‖)-1` | First bound is direct `Real.prod_one_add_le_exp_sum`. Mathlib provides the weaker final exponential bound for the second inequality; the sharp intermediate product bound needs an elementary finite induction/finite-product expansion. See C. |
| 15.4 | Bounded functions on arbitrary S, uniformly convergent norm series ⇒ uniformly convergent product; exact zero set; permutation independence | Pointwise convergence, nonvanishing and reindexing are directly available. Existing uniform-product theorems require numerical summable majorants and continuity/compactness; these do **not** cover the printed uniform-norm-series hypothesis. A new uniform Cauchy product argument is needed. See D. |
| 15.5 | `0≤u_n<1`: sequential product `∏(1-u_n)` exists and is positive iff `Summable u` | No exact iff found. Forward implication from summability uses existing product/nonzero results. Converse is short from antitonicity, exponential bound and `summable_of_sum_range_le`; details in E. |
| 15.6 | Holomorphic factors, compact-uniform norm-series convergence ⇒ holomorphic product and sum of zero multiplicities | Holomorphy follows once exact 15.4 is proved, using `TendstoLocallyUniformlyOn.differentiableOn`. Finite order-additivity exists. Infinite order-sum theorem not found; split off finitely many vanishing factors and prove analytic nonzero tail. See F. |
| 15.7 | Elementary factors `E₀(z)=1-z`; `E_p(z)=(1-z)exp(Σₖ₌₁ᵖ z^k/k)` | No matching canonical-factor definition found. Define explicitly; polynomial/sum/exponential holomorphy APIs suffice. Do not confuse with `Complex.canonicalFactor`, which is a different rational function with a pole. |
| 15.8 | `‖1-E_p(z)‖ ≤ ‖z‖^(p+1)` on the closed unit disk | No matching bound found. Needs book-faithful proof. |
| 15.9 | Weierstrass canonical product for an escaping sequence and suitable genera; choice `p_n=n-1` | No theorem found. Existing uniform product M-test is useful once 15.8 supplies its summable majorants; prescribed multiplicities still require 15.6. |
| 15.10 | Entire-function exponential-times-canonical-product factorization | No global factorization theorem found. Local/finite meromorphic zero extraction exists, and continuous logarithms on simply connected domains exist; neither is the printed theorem. See G. |
| 15.11 | Holomorphic prescribed zeros on every proper open subset of the Riemann sphere | No matching construction found. A plane-domain theorem alone would omit the printed sphere scope. |
| 15.12 | Meromorphic functions are quotients of holomorphic functions | Pointwise/local meromorphic APIs exist; the arbitrary-domain global denominator construction is not supplied by the finite extraction theorem in G. No matching global theorem found. |
| 15.13 | Holomorphic interpolation of arbitrary finite jets on a discrete set | No matching global interpolation theorem found; requires the preceding zero construction. |
| 15.14 | Finitely generated ideals in holomorphic-function algebra; zero multiplicity | General ring ideals and `analyticOrderAt` exist. The book-specific algebra and generated-ideal bridge require definitions. |
| 15.15 | Every finitely generated ideal of H(Ω) is principal | No matching theorem found. General abstract PID APIs do not prove H(Ω) is Bézout; disconnected/identically-zero cases must be retained. |
| 15.16 | Growth restrictions and Jensen motivation | Exposition; no separate theorem beyond surrounding nodes. |
| 15.17 | Mean of log‖1−exp(iθ)‖ is zero | Direct circle-average log-distance theorem exists, including boundary point. `circleAverage_log_norm_sub_const_of_mem_closedBall` in `Analysis/SpecialFunctions/Integrals/PosLogEqCircleAverage.lean:247`: `a∈closedBall c abs(R) → circleAverage (log ‖·-a‖) c R = log R`. Set c=0,R=1,a=1, reverse norm subtraction. |
| 15.18 | Jensen formula with closed-disc zeros counted by multiplicity | Usable stronger divisor-sum version exists; see H. Need conversion to finite enumerated product and angular integral, with boundary zeros retained. |
| 15.19 | Log means and boundary-log integrability for bounded holomorphic functions | No matching radial-boundary theorem found. Mathlib `Real.log 0=0` is **not** the printed extended `log 0=−∞`; an explicit extended convention or a.e. equivalence proof is needed. |
| 15.20 | Jensen zero-counting bound and growth exponent restriction | `AnalyticOnNhd.sum_divisor_le` (H) supplies a usable ball-count estimate. Normalization, maximum modulus, limsup growth, and sharpness example still require book restatements/proofs. |
| 15.21 | Infinite Blaschke product with exact zeros and multiplicities | No infinite theorem found; finite inverse-oriented factors in I are ingredients only. |
| 15.22 | Positive logarithm and Nevanlinna class | `Real.posLog` is defined as `max 0 (Real.log r)` in `Analysis/SpecialFunctions/Log/PosLog.lean:37`. On nonnegative norm inputs it matches the printed positive log. Value-distribution functions exist, but no disk Nevanlinna-class membership package found. |
| 15.23 | Nonzero Nevanlinna-class function has Blaschke-summable zeros, and uniqueness corollary | No matching disk theorem found. Jensen and positive-log integrability APIs are ingredients only. |
| 15.24 | Blaschke product has unimodular radial limit a.e.; log mean tends to zero | No matching infinite/radial theorem found. |
| 15.25 | Polynomial density and generalized-power spanning motivation | Real polynomial density directly exists: `polynomialFunctions_closure_eq_top (a b : ℝ)` in `Topology/ContinuousMap/Weierstrass.lean:54`, plus approximation variants; complex version needs real/imaginary combination or Stone–Weierstrass. |
| 15.26 | Müntz–Szász generalized-power density criterion and nonmembership | No matching theorem found by whole-Analysis searches for Muntz/Müntz/generalized powers. General Weierstrass polynomial density is not this theorem. |

The complete independent printed inventory has 26 Chapter 15 nodes. Jensen's formula is present in a usable divisor formulation (H). Infinite Blaschke products are absent from the full-source searches described below; a finite inverse-factor decomposition exists (I).

## A. Isolated zeros

`Mathlib/Analysis/Analytic/IsolatedZeros.lean:125`:

```lean
AnalyticAt.eventually_eq_zero_or_eventually_ne_zero
  (hf : AnalyticAt 𝕜 f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0
```

Same file, line 214:

```lean
AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
  (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
  (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U
```

The complex holomorphic/analytic bridge can turn these into the familiar isolated-zero statements on open connected complex domains. These are recap ingredients, not a construction of a function from prescribed zeros.

## B. Ordered products versus Mathlib products

`Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean:49,57,92`:

```lean
HasProd.tendsto_prod_nat (h : HasProd f m) :
  Tendsto (fun n ↦ ∏ i ∈ Finset.range n, f i) atTop (𝓝 m)
Multipliable.tendsto_prod_tprod_nat (h : Multipliable f) :
  Tendsto (fun n ↦ ∏ i ∈ Finset.range n, f i) atTop (𝓝 (∏' i, f i))
Multipliable.hasProd_iff_tendsto_nat [T2Space M] (hf : Multipliable f) :
  HasProd f m ↔ Tendsto (fun n ↦ ∏ i ∈ Finset.range n, f i) atTop (𝓝 m)
```

The last theorem **assumes** `Multipliable f`. Do not erase that hypothesis. `Mathlib/Topology/Algebra/InfiniteSum/Order.lean:246` explicitly uses `tprod_eq_one_of_not_multipliable`; a product value alone cannot be substituted for the printed convergence assertion.

## C. Finite bounds

`Mathlib/Analysis/Complex/Exponential.lean:683`:

```lean
Real.prod_one_add_le_exp_sum (s : Finset ι) {f : ι → ℝ}
  (hf : ∀ i, 0 ≤ f i) :
  ∏ i ∈ s, (1 + f i) ≤ Real.exp (∑ i ∈ s, f i)
```

`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:142`, for a normed commutative ring with `NormOneClass`:

```lean
Finset.norm_prod_one_add_sub_one_le (t : Finset ι) (f : ι → R) :
  ‖∏ i ∈ t, (1 + f i) - 1‖ ≤ Real.exp (∑ i ∈ t, ‖f i‖) - 1
```

This second result alone does not prove the sharper printed 15.3 bound. `Finset.prod_one_add` in `Mathlib/Algebra/BigOperators/Ring/Finset.lean:196` provides the powerset expansion; a direct induction is likely shorter.

## D. Infinite and uniform products

`Mathlib/Analysis/SpecialFunctions/Log/Summable.lean:171,199,222`:

```lean
multipliable_one_add_of_summable [CompleteSpace R]
  (hf : Summable fun i ↦ ‖f i‖) : Multipliable fun i ↦ 1 + f i
multipliable_one_sub_of_summable [CompleteSpace R]
  (hf : Summable fun i ↦ ‖f i‖) : Multipliable fun i ↦ 1 - f i
tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R]
  (hf : ∀ i, 1 + f i ≠ 0) (hu : Summable (‖f ·‖)) :
  ∏' i, (1 + f i) ≠ 0
```

In this section `[NormedCommRing R] [NormOneClass R]` are ambient hypotheses. For complex numbers they are automatic.

`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:183,562,796`:

```lean
Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a
Equiv.tprod_eq (e : γ ≃ β) (f : β → α) : ∏' c, f (e c) = ∏' b, f b
tprod_of_exists_eq_zero (hf : ∃ b, f b = 0) : ∏' b, f b = 0
```

The last declaration has the ambient commutative topological monoid-with-zero hypotheses, Hausdorffness and the appropriate product-filter hypotheses; specializing to the ordinary complex product is direct.

`Mathlib/Analysis/Normed/Module/MultipliableUniformlyOn.lean:112`:

```lean
Summable.hasProdUniformlyOn_nat_one_add
  {f : ℕ → α → R} (hK : IsCompact K) {u : ℕ → ℝ}
  (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
  (hcts : ∀ n, ContinuousOn (f n) K) :
  HasProdUniformlyOn (fun n x ↦ 1 + f n x)
    (fun x ↦ ∏' i, (1 + f i x)) K
```

This is a majorant theorem, not 15.4. Uniform convergence of `Σ ‖u_n(s)‖` need not imply summability of sup norms (take disjoint supports). The same file provides the locally uniform majorant analogue at line 142.

`Mathlib/Analysis/Normed/Ring/InfiniteProd.lean:29`:

```lean
tendsto_tprod_one_add_of_dominated_convergence
  (h_sum : Summable bound) (hab : ∀ k, Tendsto (f · k) 𝓕 (𝓝 (g k)))
  (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
  Tendsto (fun n ↦ ∏' k, (1 + f n k)) 𝓕 (𝓝 (∏' k, (1 + g k)))
```

Again this requires a common summable numerical majorant and does not close the arbitrary uniform-norm-series gap.

## E. Exact route for 15.5

Let `p N = ∏ n ∈ Finset.range N, (1-u n)` and assume `0≤u n<1`.

1. Every `p N` is positive and `p` is antitone (`Finset.prod_range_succ`, `antitone_nat_of_succ_le`). It is bounded below by zero, so `tendsto_atTop_ciInf` in `Mathlib/Topology/Order/MonotoneConvergence.lean:152` gives existence of its sequential limit.
2. If `Summable u`, specialize `multipliable_one_sub_of_summable`, and use `tprod_one_add_ne_zero_of_summable` with `f=-u`. `tprod_nonneg` (`.../InfiniteSum/Order.lean:246`) upgrades nonzero to positive. Then apply `Multipliable.tendsto_prod_tprod_nat`.
3. If `p→P` with `P>0`, `Antitone.le_of_tendsto` (`.../MonotoneConvergence.lean:298`) gives `P≤p N` for every N.
4. `Real.add_one_le_exp (-u n)` and `Finset.prod_le_prod₀` imply `p N≤exp(-Σrange N u)`. This finite bound applies to negative arguments; `Real.prod_one_add_le_exp_sum` itself requires nonnegative arguments and is not the right direct call.
5. `Real.log_le_iff_le_exp (hP : 0<P)` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:161`) yields `Σrange N u≤-log P`.
6. `summable_of_sum_range_le` (`Mathlib/Topology/Algebra/InfiniteSum/Real.lean:91`) concludes `Summable u`.

This converse starts with the printed sequential limit and does not presuppose unconditional convergence.

## F. Holomorphy and orders

`Mathlib/Analysis/Complex/LocallyUniformLimit.lean:136`:

```lean
TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
  (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
  (hU : IsOpen U) : DifferentiableOn ℂ f U
```

`Mathlib/Analysis/Analytic/Order.lean:509`:

```lean
analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
  analyticOrderAt (f * g) z₀ = analyticOrderAt f z₀ + analyticOrderAt g z₀
```

The natural-valued version `analyticOrderNatAt_mul` adds hypotheses that neither order is top. An infinite product-order identity was not found. Existing finite order identities are ingredients only.

## G. Global Weierstrass factorization gaps

The full source search for `Weierstrass.*(factor|product)`, `canonical product`, `elementary factor`, and prescribed-zero terminology found no matching entire-function theorem. `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean` is algebraic power-series preparation over local rings, a different theorem.

`Mathlib/Analysis/Meromorphic/FactorizedRational.lean:296`:

```lean
MeromorphicOn.extract_zeros_poles (h₁f : MeromorphicOn f U)
  (h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤)
  (h₃f : (divisor f U).support.Finite) :
  ∃ g, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
    f =ᶠ[codiscreteWithin U] (∏ᶠ u, (· - u) ^ divisor f U u) • g
```

Finite support is essential in this statement. The equality is initially codiscrete, not a global pointwise entire-function factorization.

`Mathlib/Analysis/Complex/BranchLogRoot.lean:37`:

```lean
Complex.exists_continuousOn_eqOn_exp_comp
  (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
  ∃ f, ContinuousOn f U ∧ EqOn (Complex.exp ∘ f) g U
```

This supplies a continuous logarithm, not yet its holomorphy. The upgrade can use `Mathlib/Analysis/Calculus/Deriv/Inverse.lean:73` directly:

```lean
HasDerivAt.of_comp_left (hst : ContinuousAt g a)
  (hf : HasDerivAt f f' (g a)) (hh : HasDerivAt h h' a) (hf' : f' ≠ 0)
  (hcomp : f ∘ g =ᶠ[𝓝 a] h) : HasDerivAt g (h' / f') a
```

Specialize outer f to the exponential and use `Complex.hasDerivAt_exp` and `Complex.exp_ne_zero`. This closes the branch upgrade using existing foundations; it still does not supply the canonical-product factorization itself.

## H. Jensen formula

`Mathlib/Analysis/Complex/JensenFormula.lean:375`:

```lean
AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
  (hR : R ≠ 0) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
  (h₂f : f c ≠ 0) :
  circleAverage (Real.log ‖f ·‖) c R =
    ∑ᶠ u, MeromorphicOn.divisor f (closedBall c |R|) u *
      Real.log (R * ‖c-u‖⁻¹) + Real.log ‖f c‖
```

This directly supplies a robust version, including boundary zeros whose logarithmic weight is zero. Book-faithful work is to convert the finite divisor sum to the enumerated zeros with multiplicity and expand `circleAverage` into the printed angular integral. The complex meromorphic version, including poles and a center-zero correction, is `MeromorphicOn.circleAverage_log_norm` at line 307. `AnalyticOnNhd.sum_divisor_le` at line 389 gives the zero-counting bound, with hypotheses `0<|r|`, `|r|<|R|`, `1≤M`, holomorphy on the larger closed ball, `f c≠0`, and boundary norm bound by M.

## I. Finite versus infinite Blaschke products

`Mathlib/Analysis/Complex/CanonicalDecomposition.lean:53` defines

```lean
Complex.canonicalFactor R w z = (R^2 - conj w * z) / (R * (z-w))
```

For `w∈ball 0 R`, `Complex.meromorphicOrderAt_canonicalFactor` (line 98) gives order **-1** at w, and `Complex.norm_canonicalFactor_eval_circle_eq_one` (line 162) gives norm one on the boundary. It is inverse-oriented relative to a holomorphic zero factor.

`MeromorphicOn.exists_canonicalDecomp` (same file:314) assumes meromorphy on `closedBall 0 R` and no infinite meromorphic orders there, and produces `∃g, Complex.CanonicalDecomp f g R`. The structure contains a finite product over the divisor, a codiscrete equality and a zero-free meromorphic remainder inside the disk. It does not state infinite Blaschke product convergence, the Blaschke condition, inner radial limits, or bounded-holomorphic factorization.

Research method: complete-tree filename search through the pinned GitHub tree, then full `rg` searches of the checked-out pin for Blaschke, Weierstrass product/factorization, canonical/elementary products, analytic/tprod combinations, and exact product/zero/order APIs. Mathlib's only textual `Blaschke` occurrence is the finite canonical-decomposition documentation above. Therefore the claim is that no matching declaration was found in the inspected pin, not that the mathematical results are impossible to derive from existing foundations.

## J. Exact 15.10 prerequisites: faithful enumeration and removable quotient

The printed theorem takes a sequence enumerating the zeros with multiplicity. It does not make construction of an enumeration a separate conclusion. A faithful Lean encoding is `∀ z, HasSum (fun n ↦ if a n = z then (1 : ℕ) else 0) (analyticOrderNatAt f z)`, together with `∀ n, f (a n) = 0`. An equality to the natural `tsum` alone is unsafe: the default for a nonsummable series is zero, so an infinitely repeated zero could evade the intended multiplicity condition. Actual `HasSum` closes that loophole. Finite and empty zero lists require the corresponding `Fin N` version/product conventions; they cannot silently be represented by an infinite sequence of nonzero zeros.

The escape-to-infinity condition needed by 15.9 follows from this enumeration rather than becoming an additional 15.10 hypothesis:

- `HasSum.map` in `Topology/Algebra/InfiniteSum/Basic.lean:218` (additivized from `HasProd.map`) maps the count series into the discrete group ℤ.
- `Summable.hasFiniteSupport_of_discreteTopology` in `Topology/Algebra/InfiniteSum/Group.lean:373` (additivized) shows every fiber `{n | a n = z}` is finite.
- `AnalyticOnNhd.preimage_zero_mem_codiscrete` in `Analysis/Analytic/Order.lean:700` gives `f ⁻¹' {0}ᶜ ∈ codiscrete ℂ` for an entire function with one nonzero value.
- `compl_mem_codiscrete_iff` in `Topology/DiscreteSubset.lean:478` identifies this with the zero set being closed and discrete.
- `IsCompact.inter_right` and `IsCompact.finite` in `Topology/Compactness/Compact.lean:87,1055` make every compact zero set finite.
- `Set.Finite.preimage'` in `Data/Set/Finite/Lattice.lean:213` upgrades finite fibers to finite preimages of compact zero sets.
- `tendsto_cofinite_cocompact_iff` in `Topology/DiscreteSubset.lean:185`, `Nat.cofinite_eq_atTop`, and `tendsto_norm_cocompact_atTop` in `Analysis/Normed/Group/Bounded.lean:59` then prove `‖a n‖ → ∞`.

For an entire product P with actual equal finite orders to f, Mathlib supplies all the removable quotient machinery. Define `q := toMeromorphicNFOn (f / P) univ`, using `Analysis/Meromorphic/NormalForm.lean:809`. Its normal-form property is `meromorphicNFOn_toMeromorphicNFOn` (line 872). Its orders are unchanged by `meromorphicOrderAt_toMeromorphicNFOn` (line 893), while `meromorphicOrderAt_div` in `Analysis/Meromorphic/Order.lean:582` subtracts the two orders. `AnalyticAt.meromorphicOrderAt_eq` (line 303) converts analytic order to meromorphic order. Equal finite orders therefore give order zero for q. The two characterizations `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` and `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` in `NormalForm.lean:122,156` make q entire and nonvanishing. The identity f=qP extends from punctured neighborhoods by `MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE` (line 840), the isolated-zero dichotomy, and `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` in `Topology/Separation/Hausdorff.lean:667`. Applying the entire-log helper gives the exponential factor.

These are dependency helpers only: neither the quotient lemma conditional on equal orders nor the escape lemma by itself is a formalization of the full 15.10 canonical factorization. Draft implementation is in `EntireLogWork.lean`; check status belongs in the lane evidence, not in this source-research map.

`FactorizationWork.lean` assembles the full infinite, finite and empty zero-list cases from those prerequisites and 15.9. It also records the printed origin-zero convention: `AnalyticAt.analyticOrderAt_ne_top` in `Analysis/Analytic/Order.lean:112` supplies a local factor `f z = z^k g z` with `g 0 ≠ 0`; extending `f z / z^k` away from zero and defining its value at zero to be `g 0` yields an entire residual factor. This is the direct removable-singularity argument, with `k = analyticOrderNatAt f 0`, rather than a new assumption that such a residual entire function already exists.

## K. Next dependency: meromorphic quotient construction (15.12)

The same normalization machinery can construct the numerator after 15.11 has supplied a denominator cancelling every pole. `MeromorphicOn.divisor` in `Analysis/Meromorphic/Divisor.lean:41` has type `Function.locallyFinsuppWithin U ℤ`; `MeromorphicOn.divisor_apply` (line 70) identifies its value on U with `(meromorphicOrderAt f z).untop₀`. Consequently the negative-divisor support is locally finite within U and is the correct pole data for 15.11. `Function.locallyFinsuppWithin.discreteSupport` in `Topology/LocallyFinsupp.lean:218` provides a discrete-support statement, but **discreteness alone must not replace absence of accumulation inside U**; the full `supportLocallyFiniteWithinDomain` field supplies that stronger condition.

For a denominator h supplied by 15.11, normalize f*h with `toMeromorphicNFOn (f*h) U`. Use `meromorphicOrderAt_mul` in `Analysis/Meromorphic/Order.lean:466` and the cancellation order to show nonnegative order, then `MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` gives its holomorphy. The resulting f=q/h identity should be codiscrete/punctured-germ equality, since Mathlib's scalar-valued meromorphic functions may contain arbitrary point values at poles. **Do not use `MeromorphicOn.divisor_mul` indiscriminately**: its signature at `Divisor.lean:330` requires both factors to have finite order at every point, which excludes components on which f vanishes identically. The underlying `meromorphicOrderAt_mul` has no such exclusion and handles the printed disconnected-domain case.

The pole-data and order-arithmetic draft is now `MeromorphicPoleDataWork.lean`: its natural multiplicity is `(-MeromorphicOn.divisor f Ω z).toNat`, its pole set is `{z | MeromorphicOn.divisor f Ω z < 0}`, and it targets the exact `∀ z ∈ Ω, ¬ AccPt z (𝓟 A)` interface needed by 15.11. It explicitly handles meromorphic order `⊤` before reducing the finite-order case to integer arithmetic. The root agent's separate `MeromorphicQuotientWork.lean` owns numerator regularization and quotient assembly. Both remain dependency work until the actual denominator-existence theorem is supplied and the combined statements are checked.
