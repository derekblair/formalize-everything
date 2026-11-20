# Pinned Mathlib claims check — research support

Checked 2026-10-29 against Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, first through the GitHub contents API at that exact ref and then in the fresh lane clone at `formalize-everything/books/rudin-real-and-complex-analysis/.lake/packages/mathlib`. These are source-inspected matches, not completed Lean chapter proofs or build/axiom-audit claims.

Authority read in full: issues [44](https://github.com/derekblair/formalize-everything/issues/44) and [36](https://github.com/derekblair/formalize-everything/issues/36). The printed third-edition text supplied by the scope researcher is `scope-source-rudin.txt`; Chapter 18 starts at line 19615 and ends after 18.21. Its title is *Elementary Theory of Banach Algebras*, which disagrees with issue 44's title/topic assignment. The findings below do not resolve that scope decision.

All Mathlib source paths below are relative to its root. For exact pinned online evidence use `https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/` followed by the path.

## Printed Chapter 18 mapping

| Node | Source-inspected coverage | Work still required for the printed node |
|---|---|---|
| 18.1 | `NormedRing`, `NormedAlgebra ℂ A`, `CompleteSpace A`, `NormOneClass A`, `Units`, `IsUnit`, `spectrum` cover the structures. | Explicitly include unit norm one and the book's invertibility sign convention; capture elementary continuity/group/uniqueness claims. Mathlib `spectrum` uses `λ·1-x`, while Rudin uses `x-λ·1`; these are equivalent by negation. |
| 18.2 | Expository paragraph. | No new theorem is asserted beyond references and motivation. |
| 18.3 | `Units.oneSub`, `hasSum_geom_series_inverse`, `geom_series_eq_inverse`, `tsum_geometric_le_of_norm_lt_one`. | Substitute `-x` to obtain `1+x`; prove the printed second-order bound explicitly. A geometric-series identity alone is incomplete coverage. |
| 18.4 | `Units.add`, `Units.ofNearby`, `Units.isOpen`, `NormedRing.inverse_continuousAt`, `hasFDerivAt_ringInverse`, `spectrum.isCompact`, `spectrum.norm_le_norm_of_mem`. | Printed quantitative remainder bound must be supplied; account for all three corollaries, including homeomorphism on the units. `inverse_add_norm_diff_second_order` is only a big-O statement and does not directly state the printed constant. |
| 18.5 | `spectrum.hasDerivAt_resolvent_const_left`, `spectrum.resolvent_tendsto_cobounded`. | Compose with the bounded complex linear functional; negate Mathlib's resolvent to match Rudin's `x-λe` convention; preserve both holomorphy and limit at infinity. |
| 18.6 | `spectrum.isCompact`, `spectrum.nonempty`. | Faithful restatement with the book's nontriviality/unit-norm assumptions. |
| 18.7 | `NormedRing.algEquivComplexOfComplete` plus `algebraMap_isometry`. | State isometric algebra isomorphism, not just algebraic equivalence. Do not use the separate multiplicative-norm variant as though it covered submultiplicative norms. |
| 18.8 | `spectralRadius`, `spectralRadius_eq_of_unital`. | Mathlib radius has codomain `ℝ≥0∞`; relate it to the finite real supremum in the book. |
| 18.9 | `spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius` and the nnnorm version. | Convert the extended-real limit to the printed real limit; existence of the limit is part of the conclusion. |
| 18.10 | `spectrum.subset_subalgebra`, spectral radius formula. Also subalgebra spectral-boundary lemmas in `Analysis/Normed/Algebra/Spectrum.lean`. | State both spectrum inclusion and equality of spectral radii with the inherited norm. Algebraicity is explanatory. |
| 18.11 | Continuous-function and Banach-algebra infrastructure exists. | No ready-made disc algebra was located. Need the closed disc algebra, its boundary restriction, and coordinate-function spectra (closed disk versus unit circle). |
| 18.12 | `Ideal`, `NonUnitalAlgHom`, `RingHom.ker`, ideal/submodule structures. | Rudin's general homomorphisms need not preserve 1 and may be zero; using only `AlgHom` silently narrows this definition. Build the kernel ideal for the nonunital map. |
| 18.13 | `Ideal.exists_le_maximal`; `Ideal.IsMaximal.closure_eq`; `Ideal.IsMaximal.isClosed`. | Direct faithful wrappers. |
| 18.14 | `Submodule.mkQ`, quotient modules, `Ideal.Quotient.mkₐ`, quotient kernel and field/maximal APIs. | Include coset equality/disjointness, surjectivity, operation compatibility, kernel, and field iff maximal; not merely an instance. |
| 18.15 | `Submodule.Quotient.normedAddCommGroup`, `.normedSpace`, `.completeSpace`; `Ideal.Quotient.normedCommRing`, `.normedAlgebra`; quotient norm lemmas. | State infimum/distance characterization and show quotient unit norm one for a proper closed ideal. The latter is not supplied by the named quotient-ring instance alone. |
| 18.16 | `A →ₐ[ℂ] ℂ` and `WeakDual.characterSpace ℂ A` with `WeakDual.CharacterSpace.equivAlgHom`. | Derive unitality and automatic continuity from a nonzero multiplicative linear functional. Do not assume continuity in the initial book character definition. |
| 18.17(a) | `Ideal.toCharacterSpace`, `Ideal.toCharacterSpace_apply_eq_zero_of_mem`; `WeakDual.CharacterSpace.ker_isMaximal`, `.ext_ker`. | Equality of the kernel with the given maximal ideal, not just containment, and translate to the book's character representation. |
| 18.17(b) | `WeakDual.CharacterSpace.mem_spectrum_iff_exists`. | Direct translation from `characterSpace` to book characters. |
| 18.17(c) | `.exists_apply_eq_zero` and `AlgHom.apply_mem_spectrum`. | State full iff between invertibility and nonvanishing under every character. |
| 18.17(d) | `AlgHom.apply_mem_spectrum`. | Direct wrapper. |
| 18.17(e), following paragraph | `spectralRadius_eq_of_unital`, `spectralRadius_le_nnnorm`, `AlgHom.norm_apply_le_self`, `.toContinuousLinearMap_norm`. | Preserve the intermediate spectral-radius bound, and prove automatic continuity/norm bound without assuming continuity initially. |
| 18.18 | General ideal/character machinery above; Taylor/holomorphic limit infrastructure. | No direct disc-algebra Bezout theorem or disc-algebra character classification located. Need actual disc algebra, polynomial density, character classification, then finite-family Bezout. |
| 18.19 | General closed subalgebra and Fourier APIs. | Need the disk-boundary identification, Fourier-negative-coefficient characterization, and maximality statement. |
| 18.20 | `fourierSubalgebra_closure_eq_top` provides density of *all* trigonometric polynomials, not the claim here. | No direct theorem located for density of the algebra generated by analytic polynomials and an arbitrary continuous `g` with one nonzero negative Fourier coefficient. Stone–Weierstrass alone must not be cited as exact coverage. |
| 18.21 | General character invertibility theorem; summable Fourier series convergence in `Analysis/Fourier/AddCircle.lean`; summable products in `Analysis/Normed/Ring/InfiniteSum.lean`. | No Wiener reciprocal theorem located. Need a Banach algebra of absolutely summable Fourier series (or ℓ¹ convolution), identify all characters, then transport inverse back to an absolutely summable sequence. Existing `lpSpace` ring structures concern ℓ∞ pointwise multiplication. |

## Precise reusable declarations

`Analysis/SpecificLimits/Normed.lean`, with `[NormedRing R] [HasSummableGeomSeries R]` (the latter has a `[CompleteSpace R]` instance):

```lean
Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ
-- value is 1-t; inverse is ∑' n : ℕ, t^n
hasSum_geom_series_inverse (x : R) (h : ‖x‖ < 1) :
  HasSum (fun i ↦ x ^ i) (1-x)⁻¹ʳ
geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) :
  ∑' i, x ^ i = (1-x)⁻¹ʳ
tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
  ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1-‖x‖)⁻¹
```

`Analysis/Normed/Ring/Units.lean`, same hypotheses:

```lean
Units.add (x : Rˣ) (t : R) (h : ‖t‖ < ‖(↑x⁻¹ : R)‖⁻¹) : Rˣ
Units.isOpen : IsOpen {x : R | IsUnit x}
NormedRing.inverse_continuousAt (x : Rˣ) : ContinuousAt Ring.inverse (x : R)
Ideal.closure_ne_top (I : Ideal R) (hI : I ≠ ⊤) : I.closure ≠ ⊤
Ideal.IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I
-- instance:
Ideal.IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R)
```

`Analysis/Calculus/FDeriv/Mul.lean` has `[NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra 𝕜 R]` with a nontrivially normed scalar field:

```lean
hasFDerivAt_ringInverse (x : Rˣ) :
  HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
```

`Analysis/Normed/Algebra/GelfandFormula.lean`, with `[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`:

```lean
spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
  Tendsto (fun n : ℕ => ENNReal.ofReal (‖a^n‖ ^ (1/n : ℝ))) atTop
    (𝓝 (spectralRadius ℂ a))
-- additionally [Nontrivial A]:
spectrum.nonempty (a : A) : (spectrum ℂ a).Nonempty
-- does not require NormMulClass or commutativity:
NormedRing.algEquivComplexOfComplete
  (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) : ℂ ≃ₐ[ℂ] A
```

`Analysis/Normed/Module/Basic.lean` supplies `algebraMap_isometry` under `[NormOneClass A]`. This is the missing isometry component for 18.7. The distinct file `Analysis/Normed/Algebra/GelfandMazur.lean` proves `NormedAlgebra.Complex.algEquivOfNormMul` under `[NormMulClass F]`; that stronger norm hypothesis does **not** directly match Rudin.

`Analysis/Normed/Algebra/Spectrum.lean`, with `[NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]`:

```lean
spectrum.isClosed (a : A) : IsClosed (spectrum 𝕜 a)
spectrum.isCompact [ProperSpace 𝕜] (a : A) : IsCompact (spectrum 𝕜 a)
spectrum.norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜}
  (hk : k ∈ spectrum 𝕜 a) : ‖k‖ ≤ ‖a‖
AlgHom.toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : StrongDual 𝕜 A
AlgHom.norm_apply_le_self [NormOneClass A] (f : A →ₐ[𝕜] 𝕜) (a : A) : ‖f a‖ ≤ ‖a‖
-- with nontrivially normed scalar field:
AlgHom.toContinuousLinearMap_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) :
  ‖φ.toContinuousLinearMap‖ = 1
WeakDual.CharacterSpace.equivAlgHom :
  WeakDual.characterSpace 𝕜 A ≃ (A →ₐ[𝕜] 𝕜)
```

`Analysis/CStarAlgebra/GelfandDuality.lean:74–129` has a section with **only** `[NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`. C-star assumptions begin afterward, so these particular declarations apply to general commutative complex Banach algebras:

```lean
Ideal.toCharacterSpace (I : Ideal A) [Ideal.IsMaximal I] : WeakDual.characterSpace ℂ A
Ideal.toCharacterSpace_apply_eq_zero_of_mem (I : Ideal A) [Ideal.IsMaximal I]
  {a : A} (ha : a ∈ I) : I.toCharacterSpace a = 0
WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
  ∃ f : WeakDual.characterSpace ℂ A, f a = 0
WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : ℂ} :
  z ∈ spectrum ℂ a ↔ ∃ f : WeakDual.characterSpace ℂ A, f a = z
spectrum.gelfandTransform_eq (a : A) :
  spectrum ℂ (WeakDual.gelfandTransform ℂ A a) = spectrum ℂ a
```

`Analysis/Normed/Algebra/Basic.lean:50–64` proves compactness of character space over a proper nontrivially normed scalar field. This is extra infrastructure, not a substitute for the disc algebra or Wiener character-identification arguments.

## Ticket-named topics checked separately

* `Analysis/Complex/PhragmenLindelof.lean` really proves strip, quadrant and half-plane variants. For example `PhragmenLindelof.vertical_strip` assumes `DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo a b)`, boundary bounds by `C`, and a double-exponential big-O growth rate with `c < π/(b-a)`; it concludes `‖f z‖ ≤ C` on the closed strip. Exact comparison with the eventual printed node is necessary.
* `Analysis/Complex/Hadamard.lean` proves **Hadamard three-lines**, not Hadamard factorization. `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` assumes `l < u`, differentiability/closure continuity on the strip, bounded norms on the entire closed strip, edge bounds `a,b`, and concludes `‖f z‖ ≤ a^(1-(z.re-l)/(u-l))*b^((z.re-l)/(u-l))`.
* Full-tree searches for `hadamard.*factor`, `factor.*hadamard`, `Fatou`, `nontangential`, `non.tangential`, `radial limit`, and `boundary values` did not locate Hadamard factorization or Fatou/Riesz boundary theorems. Fatou hits are measure-theoretic Fatou's lemma (and a martingale discussion using it), which is not the boundary theorem.
* `Analysis/Complex/CanonicalDecomposition.lean` is **finite** canonical/Blaschke decomposition of a meromorphic function on a compact disk. It does not establish a full entire-function canonical product or infinite Blaschke factorization.
* `Analysis/Complex/AbelLimit.lean` proves an Abel limit in Stolz sets/cones for a power series whose coefficient series already converges. It is useful boundary infrastructure, not almost-everywhere boundary-limit existence for arbitrary bounded analytic functions.
* `Analysis/Complex/Poisson.lean` and `Analysis/Complex/Harmonic/Poisson.lean` supply Poisson integral formulas under differentiability/harmonicity and continuity on closed disks. These assumptions cannot silently replace the boundary hypotheses of a Fatou theorem.

The negative findings mean no direct declaration was found by the documented source survey; they do not claim mathematical impossibility or prove absence under every conceivable theorem name.

## Scratch implementation evidence

`work/Chapter18Ideals.lean` implements printed18.12–18.17 with initially nonunital homomorphisms, algebraic characters without a continuity assumption, quotient/coset operations, quotient norms/completeness/unit norm, maximal ideal containment/closedness, and every part(a–e) of18.17. The generic Banach-algebra character argument is reconstructed using the maximal quotient and Gelfand–Mazur, avoiding the heavier Gelfand-duality import.

`evidence/ch18-ideals-check-04.log` records `lake env lean -j1 -R <lane>/work -o <lane>/work/Chapter18Ideals.olean <lane>/work/Chapter18Ideals.lean`, exit0, with35 printed axiom audits all limited to `propext`, `Classical.choice`, `Quot.sound`. This is a successful standalone scratch check, not a chapter clean-slate build. Checks01–03 were interrupted or failed and are not success evidence. Chapter18.1's printed standing convention explicitly assumes a unit and norm-one unit; ambient unital types in18.12–18.17 therefore follow that convention.

`work/Chapter18Maximality.lean` contains a separate full18.20 proof draft (proper closed subalgebra argument, Hahn–Banach positivity, Fourier density, and finite polynomial approximation). It is not validated yet and must not be counted as complete from source existence.
