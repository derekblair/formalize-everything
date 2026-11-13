# Pinned Mathlib claims check: RCA Chapters 13–14

Checked 2026-10-29 against the actual checkout at
`formalize-everything/books/rudin-real-and-complex-analysis/.lake/packages/mathlib`.
`git rev-parse HEAD` returned **d13f23b723b8a846827a245b89c10fc7d3f11612**.
The project toolchain is **leanprover/lean4:v4.34.1**. This is a source-level
claims audit, not a claim that any new book module has passed a build or axiom audit.
Printed scope is supplied by `inventory-ch13.md` and `inventory-ch14.md` in this directory:
**12 + 22 = 34 numbered nodes**. In particular Runge is 13.6/13.9,
13.10 is Mittag-Leffler, and 13.12 is harmonicity of log modulus.

## Classification and limits

- **Usable** means the mathematical assertion is already present in a usable
  theorem; routine domain restatement remains.
- **Partial** means relevant variants or parts exist, but the whole printed node
  is not supplied. The missing parts are named explicitly.
- **Missing** means no theorem proving the principal assertion was identified
  after searching the entire pinned source tree and reading the candidate files.
  It does not claim mathematical impossibility or absence from all other projects.

No row implies Stage 2 completion. Numbered definitions also carry the accompanying
printed assertions; a definition alone does not complete such a node.
Paths below are relative to `Mathlib/` at the verified pin. Exact source anchors
are supplied in the detailed evidence after the tables.

## Chapter 13: every numbered node

| Node | Status | Pinned source evidence and remaining obligation |
|---|---|---|
| 13.1 | Partial | `OnePoint ℂ`, its topology and compactness, and `onePointEquivSphereOfFinrankEq` give the sphere infrastructure. `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under` gives removability after inversion. `MeromorphicAt` and meromorphic order give a local singularity vocabulary. The exact printed stereographic coordinates, polynomial principal part at infinity, nonpolynomial-entire essential singularity, and strip-complement example still require proofs/restatement. |
| 13.2 | Partial | `RatFunc.num_div_denom`, `RatFunc.isCoprime_num_denom`, complex polynomial splitting, and `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` supply the algebraic ingredients. Must specialize to complex linear factors, package each principal part as a polynomial in `(z-a)⁻¹` with zero constant coefficient, identify pole orders, and restrict evaluation off poles. |
| 13.3 | Partial | `CompactExhaustion.choice`, `.subset_interior_succ`, and `.exists_superset_of_isCompact` supply (a),(b) for an appropriate open subtype. They do **not** supply (c), the spherical complement component condition. The book's explicit exhaustion or an equivalent construction remains needed. |
| 13.4 | Missing | `Combinatorics/SimpleGraph/Trails.lean` has undirected Eulerian-trail necessary conditions and explicitly lists the converse as a TODO. It does not give decomposition of a finite balanced directed multiset of intervals into cycles. |
| 13.5 | Missing | `Analysis/Complex/CauchyIntegral.lean` gives rectangle Cauchy–Goursat vanishing and circle Cauchy integral formulas, but not existence of one polygonal cycle in `Ω \\ K` serving all points of an arbitrary compact `K` and all holomorphic functions on `Ω`. |
| 13.6 | Missing | No Runge/rational-approximation theorem in the source search or candidate complex-analysis files. Prescribed spherical pole sets, compact approximation, and countability of complement components remain. |
| 13.7 | Missing | No complex-polynomial approximation on an arbitrary compact set with connected spherical complement was found. Real Stone–Weierstrass is not this assertion. |
| 13.8 | Missing | Maximum-modulus ingredients exist in `Analysis/Complex/AbsMax.lean`, but the bounded-complement obstruction and necessity of prescribed poles are not packaged/proved as this node. |
| 13.9 | Missing | Locally uniform convergence and `CompactExhaustion` exist. They do not prove existence of rational approximants with the prescribed poles. The Runge core and exhaustion condition remain. |
| 13.10 | Missing | `Analysis/Meromorphic/*` supplies meromorphic definitions and calculus, but no existence theorem with arbitrary discrete prescribed principal parts. `CategoryTheory/CofilteredSystem.lean` concerns a different Mittag-Leffler condition; `Trigonometric/Cotangent.lean` only a particular expansion. |
| 13.11 | Partial | `Analysis/Complex/BranchLogRoot.lean` gives continuous logarithm/root branches on simply connected open sets. `Analysis/Complex/HasPrimitives.lean` supplies local/convex primitive tools. The nine-way equivalence, spherical-complement equivalence, polynomial approximation direction, and disc homeomorphism direction are not one existing theorem. The printed final implication depends on 14.8. |
| 13.12 | Usable | `AnalyticAt.harmonicAt_log_norm` proves the pointwise assertion for a nonzero analytic function. On an open set, `DifferentiableOn.analyticOnNhd` converts the book hypothesis; apply the pointwise theorem at every domain point. |

## Chapter 14: every numbered node

| Node | Status | Pinned source evidence and remaining obligation |
|---|---|---|
| 14.1 | Partial | Standard derivatives, normalization of nonzero complex vectors, and conformality infrastructure exist. The book's oriented-angle limiting definition is not `ConformalAt`: Mathlib deliberately includes antiholomorphic conjugation. The exact definition and global characterization need a faithful encoding. |
| 14.2 | Partial | `DifferentiableAt.conformalAt` and the Cauchy–Riemann characterization are available, but the converse for book-oriented angles is not the existing unoriented conformality equivalence. The zero-derivative holomorphic exclusion and `|z|z` example remain. |
| 14.3 | Partial | Real-coefficient upper-half-plane Möbius action and projective-line/one-point equivalences exist; Euclidean inversion carries spheres through its center to hyperplanes. These are not a complete complex Riemann-sphere Möbius classification, generalized-circle preservation, unique three-point interpolation, or explicit Cayley-map package. |
| 14.4 | Missing | No Schwarz-reflection principle was found in the full-tree search. The circle version also requires a precise reflected-open-neighborhood/arc formulation. |
| 14.5 | Partial | `TendstoLocallyUniformlyOn` and its equivalence with uniform convergence on every compact subset exist. The finite-valued normal-family definition can be stated using them; the adoption of this convention and associated holomorphic-limit claim still need book declarations. |
| 14.6 | Missing | Arzelà–Ascoli and Cauchy estimates exist, but no Montel theorem for locally bounded holomorphic families was found. `Analysis/LocallyConvex/Montel.lean` concerns Montel topological vector spaces. |
| 14.7 | Partial | Open mapping and inverse-function theorem infrastructure exist. A holomorphic-bijection equivalence, holomorphic inverse, and pullback ring isomorphism require assembly; no exact book package found. |
| 14.8 | Missing | `Analysis/Complex/RiemannMapping.lean` expressly contains only partial results, with injective maps **into** the disc and no surjectivity. Its documentation points to unmerged PR 33505; that is outside the pinned dependency. The proper-domain Riemann mapping theorem is not supplied by this file. |
| 14.9 | Partial | `Analysis/Complex/Schwarz.lean` gives derivative bounds and affine equality cases on balls. Transport through the normalized conformal map remains, and its existence depends on 14.8. |
| 14.10 | Partial | Taylor expansion of holomorphic functions on discs exists in `Analysis/Complex/TaylorSeries.lean`; the normalized univalent class, its expansion restatement, and failure of algebra closure need declarations/proofs. |
| 14.11 | Missing | No Koebe/univalent-family theorem found. Rational differentiation and geometric-series tools are available but do not establish the full normalized injectivity and coefficient expansion claim. |
| 14.12 | Partial | Composition/rotation calculus and continuous square-root branches exist. They do not already prove membership of the rotated or odd square-root transforms in the normalized univalent class. |
| 14.13 | Missing | No univalent area theorem found. This also needs a faithful Laurent/pole formulation and a summability or nonnegative-series encoding, plus the sharp corollary. |
| 14.14 | Missing | No coefficient-two bound or Koebe quarter theorem found. The normalization and sharp examples are not a substitute for either inequality. |
| 14.15 | Missing | No omitted-value diameter bound for normalized simple-pole univalent functions found. |
| 14.16 | Missing | No matching simple-boundary-point predicate/sequence-interpolating-curve theorem found. Must encode the whole sequence, not an arbitrary subsequence. |
| 14.17 | Missing | No slit-disc/comb-domain boundary examples with the printed assertions found. |
| 14.18 | Missing | No boundary extension theorem at Rudin-simple boundary points, nor boundary injectivity theorem, found. |
| 14.19 | Missing | No matching conformal homeomorphic extension to closures found. |
| 14.20 | Missing | No matching Jordan-boundary converse, three-point conformal boundary normalization, or sphere-domain generalization found. All printed subclaims remain in scope, including the converse omitted from the book's proof. |
| 14.21 | Partial | Dilation and annulus-set facts can use elementary norm/scalar calculus. The assertion that all proper simply connected regions are conformally equivalent depends on the missing full 14.8. |
| 14.22 | Missing | Circle integration and annulus Cauchy theorems exist; no classification of conformal annuli by radius ratio was found. |

## Exact early-node APIs

### Riemann sphere and topology (13.1)

`Topology/Compactification/OnePoint/Sphere.lean:35`:

```lean
def onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (h : finrank ℝ V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1
```

Use `V := ℂ`, `ι := Fin 3`. This gives existence of a homeomorphism;
it does not assert equality with Rudin's specific coordinate map.
`Geometry/Manifold/Instances/Sphere.lean:249` constructs `stereographic` as an
`OpenPartialHomeomorph`; `stereographic_apply` is at line 271 and the reverse-map
formula is in the same file. Its normalization has to be checked against the book.

`Topology/Compactification/OnePoint/Basic.lean`:

- `OnePoint.isOpen_def` (220), `.isOpen_iff_of_mem` (228): neighborhood topology.
- `.isOpenEmbedding_coe` (272): ordinary plane embeds openly.
- `.nhdsNE_infty_eq` (300): punctured infinity is the image of `coclosedCompact`.
- `.hasBasis_nhds_infty` (325): complements of closed compact sets are a basis.
- `.continuousAt_infty` (359): continuity at infinity is a cocompact limit condition.

`Analysis/Complex/RemovableSingularity.lean:123`:

```lean
theorem Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f)
```

At line 101, `Complex.differentiableOn_update_limUnder_of_bddAbove` also proves
holomorphicity of the extension. Compose with inversion and prove the exterior-disc
and punctured-disc filter transport; do not confuse a raw value at zero with the
continuous extension value. `Analysis/Meromorphic/Basic.lean:38` defines
`MeromorphicAt` by multiplication with a sufficiently large power to obtain an
analytic function. `Analysis/Meromorphic/Order.lean` supplies signed orders, with
`tendsto_cobounded_iff_meromorphicOrderAt_neg` at line 234.

### Rational functions and partial fractions (13.2)

`FieldTheory/RatFunc/Basic.lean`:

```lean
RatFunc.monic_denom (x : K⟮X⟯) : x.denom.Monic
RatFunc.denom_ne_zero (x : K⟮X⟯) : x.denom ≠ 0
RatFunc.num_div_denom (x : K⟮X⟯) :
  algebraMap _ _ x.num / algebraMap _ _ x.denom = x
RatFunc.isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom
```

Source lines are 945, 952, 977, and 991, respectively.
`Algebra/Polynomial/Splits.lean:307` gives
`Polynomial.Splits.eq_prod_roots_of_monic`.
`Algebra/Polynomial/Roots.lean:810` gives
`Polynomial.prod_multiset_root_eq_finset_root`:

```lean
(p.roots.map fun a => X - C a).prod =
  p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p
```

`Algebra/Polynomial/PartialFractions.lean:407` gives the main general algebraic result:

```lean
theorem Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    [Nontrivial R] {ι : Type*} {s : Finset ι}
    (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    (n : ι → ℕ) {gi : ι → K}
    (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      algebraMap R[X] K f * ∏ i ∈ s, gi i ^ n i =
        algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
          algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1)
```

Ambient assumptions include `[CommRing R] [CommRing K] [Algebra R[X] K]`.
For a faithful global identity use `K := RatFunc ℂ`, rather than choosing a
point-evaluation algebra separately for every `z` (that risks obtaining
point-dependent coefficients). Specialize `g a := X - C a`; degree `< 1`
forces constant numerators. Package their inverse powers as polynomials with
zero constant coefficient, then evaluate off the denominator zero set.
The denominator pole-order identification is a separate analytic obligation.

### Compact exhaustion (13.3)

`Topology/Compactness/SigmaCompact.lean`:

```lean
CompactExhaustion.choice (X : Type*) [TopologicalSpace X]
  [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] : CompactExhaustion X
CompactExhaustion.subset_interior_succ (K : CompactExhaustion X) (n : ℕ) :
  K n ⊆ interior (K (n + 1))
CompactExhaustion.exists_superset_of_isCompact (K : CompactExhaustion X)
  {s : Set X} (hs : IsCompact s) : ∃ n, s ⊆ K n
```

Source lines 418, 353, and 376. The structure at line 323 has only compactness,
nested interiors, and union equal to the whole space. There is no complement
component field; (c) cannot be claimed by wrapping this structure.

## Other exact useful signatures

`Analysis/Complex/LocallyUniformLimit.lean:159`:

```lean
TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
  (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
  (hU : IsOpen U) : DifferentiableOn ℂ f U
```

At line 178, `.deriv` gives locally uniform convergence of derivatives. These
are usable closure results; they do not construct any approximation sequence.

`Analysis/InnerProductSpace/Harmonic/Constructions.lean:109`:

```lean
theorem AnalyticAt.harmonicAt_log_norm {f : ℂ → ℂ} {z : ℂ}
    (h₁f : AnalyticAt ℂ f z) (h₂f : f z ≠ 0) :
    HarmonicAt (Real.log ‖f ·‖) z
```

`Analysis/Complex/BranchLogRoot.lean:37,67` gives continuous branches:

```lean
Complex.exists_continuousOn_eqOn_exp_comp
  (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
  ∃ f, ContinuousOn f U ∧ EqOn (Complex.exp ∘ f) g U
Complex.exists_continuousOn_pow_eq
  (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (hn : n ≠ 0) :
  ∃ f, ContinuousOn f U ∧ ∀ x, f x ^ n = g x
```

Holomorphicity is not the literal conclusion of these two declarations; derive
it using local inverses or existing analytic lifting lemmas before claiming
13.11(h)/(j).

`Analysis/Complex/Conformal.lean:150`:

```lean
DifferentiableAt.conformalAt (h : DifferentiableAt ℂ f z)
  (hf' : deriv f z ≠ 0) : ConformalAt f z
```

At line 161 its iff theorem permits either holomorphicity **or antiholomorphicity**.
The warning in that file explicitly states that conjugation counts as conformal.
Book14.1's oriented-angle preservation therefore needs its own predicate or
an additional orientation condition.

`Analysis/Complex/RiemannMapping.lean:120` has only the weaker preparatory result:

```lean
exists_mapsTo_unitBall_injOn_deriv_ne_zero
  (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
  ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧
    ∀ z ∈ U, deriv f z ≠ 0
```

The file's lines 24–31 explicitly describe the incompleteness and a separate PR.
It has no `public section` for these preparatory declarations. In particular,
neither this result nor its name is evidence of a public full Riemann-mapping API.

## Search record

The entire `Mathlib/` tree was searched case-insensitively for `Runge`, `Mergelyan`,
`Mittag-Leffler`, `RiemannMapping`, `normal family`, `Montel`, `Koebe`, `univalent`,
`Schwarz reflection`, `reflection principle`, Möbius variants, annulus and boundary
terms. Candidate files for rational functions, partial fractions, stereographic
projection, one-point compactification, meromorphic orders, Cauchy integration,
locally uniform limits, harmonicity, conformality, Schwarz estimates,
Arzelà–Ascoli, compact exhaustion, and Eulerian trails were inspected directly.
Negative headline claims above are supported by these content checks, not merely
by absence of a theorem with the book's name. No dependency was modified or
replaced with an unpinned external theorem during this check.
