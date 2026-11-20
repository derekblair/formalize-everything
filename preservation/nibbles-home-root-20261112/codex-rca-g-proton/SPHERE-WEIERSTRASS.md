# Node 15.11: sphere scope and implementation prerequisites

Research snapshot: 2026-10-29. This is an implementation map, **not a proof or node-completion claim**. Pinned source is the lane clone's Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Printed scope

Rudin, *Real and Complex Analysis*, third edition, pp.303–304: the domain is a proper open subset of the Riemann sphere. A subset with no limit points in the domain, with arbitrary positive integer multiplicities, is the exact zero set of a holomorphic function with those multiplicities. The domain need not be connected. The empty set and finite zero sets are included.

Evidence: [scanned book](https://ru.djvu.online/file/NKmAEzkLVs8Io), printed p.303 image [315.webp](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/315.webp), saved as `rudin-scan-p303.webp` in this lane. The next printed page is [316.webp](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/316.webp), saved as `rudin-scan-316.webp`. Image index = printed page +12. Both page contents were inspected visually.

The proof normalizes by a fractional linear transformation so that infinity belongs to the domain but not to the prescribed zero set. Then the complement is a nonempty compact subset of the plane, and the zero sequence is bounded. Boundary poles are chosen at nearest points of that complement, and elementary factors supply the product. Holomorphy at infinity remains part of the conclusion.

## What the pinned library actually supplies

Paths below are relative to `books/rudin-real-and-complex-analysis/.lake/packages/mathlib/Mathlib/`.

| Ingredient | Exact source | Scope |
| --- | --- | --- |
| One-point topology | `Topology/Compactification/OnePoint/Basic.lean` | `OnePoint X`, finite-point open embedding (line272), neighborhoods at finite points (282), punctured infinity neighborhood (300), infinity continuity criterion (355), compactness (498), Hausdorff/normal separation (523). |
| Homeomorphisms extend | same file, `Homeomorph.onePointCongr` (628) | Extends a homeomorphism of the original space, fixing infinity. Does not directly give inversion exchanging zero and infinity. |
| Real sphere bridge | `Topology/Compactification/OnePoint/Sphere.lean`, `onePointEquivSphereOfFinrankEq` (34) | Topological homeomorphism of a finite-dimensional real vector space's one-point compactification with its real sphere. This alone supplies no complex analytic charts. |
| Projective line bridge | `Topology/Compactification/OnePoint/ProjectiveLine.lean`, `OnePoint.equivProjectivization` (94) | Set equivalence. The header explicitly lists extension to a homeomorphism even over the reals as TODO. |
| Fractional linear algebra | same file, `OnePoint.instGLAction` (134), `smul_infty_eq_ite` (149), `smul_some_eq_ite` (157) | Algebraic action of invertible 2 by 2 matrices; correct exceptional-point formulas. No continuity or holomorphy result in this file. |
| Inversion limits | `Analysis/Normed/Field/Lemmas.lean`, `Filter.tendsto_inv₀_cobounded'` (87), `tendsto_inv₀_cobounded` (90), `tendsto_inv₀_nhdsNE_zero` (93) | Exchange infinity and punctured zero filters. Combine with `Metric.cobounded_eq_cocompact`, `coclosedCompact_eq_cocompact`, and OnePoint neighborhood formulas. |
| Inversion away from zero | `Topology/Algebra/GroupWithZero.lean`, `Homeomorph.inv₀` (153) | Homeomorphism on nonzero elements. |
| Coordinate order transport | `Analysis/Analytic/Order.lean`, `AnalyticAt.analyticOrderAt_comp` (540), `analyticOrderAt_comp_of_deriv_ne_zero` (573) | Analytic order is invariant under a local analytic coordinate with nonzero derivative. |
| No accumulation criterion | `Topology/DiscreteSubset.lean`, `isClosed_and_discrete_iff` (226) | Closed-and-discrete iff every punctured neighborhood filter is disjoint from the set's principal filter. Apply inside the open-domain subtype. |
| Escape from compact sets | same file, `IsClosed.tendsto_coe_cofinite_of_isDiscrete` (207) | A closed discrete subset's inclusion tends from cofinite to cocompact. Useful to enumerate zeros with multiplicity without accumulation. |
| Countability | `Topology/Compactness/Lindelof.lean`, `IsLindelof.countable_of_isDiscrete` (652) | Discrete subsets that are Lindelöf are countable; second-countable spaces are hereditarily Lindelöf (726). |
| Nearest boundary point | `Topology/MetricSpace/HausdorffDistance.lean`, `IsCompact.exists_infDist_eq_dist` (611), `IsClosed.exists_infDist_eq_dist` (616) | A nearest point exists for nonempty compact sets, or nonempty closed sets in a proper metric space. |

Searches across the entire pinned Mathlib source for `RiemannSphere`, `Riemann sphere`, `OnePoint ℂ`, `OnePoint Complex`, and OnePoint/chart/analytic combinations found no complex-analytic sphere interface. Relevant files named OnePoint, Projectivization, Sphere, and RiemannMapping were checked directly. `Analysis/Complex/RiemannMapping.lean` contains partial Riemann-mapping results; it is not an analytic Riemann-sphere implementation. This rules out a ready declaration in these searched APIs, rather than asserting a general impossibility.

## Faithful reduction choices

1. Follow the printed normalization. Build enough sphere fractional-linear topology/holomorphy to move one point of the domain outside the zero set to infinity. Carry out the bounded-zero / compact-complement product construction and prove its local holomorphy at infinity using `w = 1/z`.
2. Choose a point omitted from the proper domain. Its complement in the sphere has one global Möbius coordinate into the plane. Prove the arbitrary-plane-open-domain Weierstrass theorem, transport the discrete set and multiplicities through that coordinate, and prove the result on the sphere using coordinate transition formulas. This avoids proving convergence directly at infinity but still requires a genuine chart bridge; a plane-only conclusion does not discharge 15.11.

A minimal explicit sphere interface can use `OnePoint ℂ`: holomorphy at finite points is `AnalyticAt ℂ (fun z => f (↑z))`; at infinity it is analyticity at zero of the pullback along the sphere inversion chart, whose zero value is `f ∞`. Multiplicity must use those same local coordinates. Transition maps are affine or fractional linear with nonzero derivatives on chart overlaps, and the existing analytic-order composition lemma proves invariance. Defining the interface alone does not prove the theorem.

For the normalized product, the infinity-chart argument has an especially simple formula. The factor with zero `a` and boundary pole `b` becomes `E_n ((a-b)*w/(1-b*w))`, analytic near `w=0` and equal to 1 there. One must establish uniform bounds on a fixed neighborhood of zero before invoking 15.6; pointwise limits are insufficient.

## Outstanding work

- An actual sphere inversion homeomorphism and chart invariance of holomorphy/order.
- Enumeration of a discrete zero set with prescribed finite positive multiplicities, treating empty and finite sets separately.
- The arbitrary-domain elementary-factor product and compact-uniform norm-series estimates.
- Full sphere theorem wrapper with no extra premise asking for the desired coordinate invariance or existence theorem.

No Lean check was run for this research note. No new declaration or completed numbered node is claimed here.

## Construction refinement after the initial API search

`SphereWork.lean` now contains an **uncompiled draft** of the explicit two-chart interface, inversion as a homeomorphism, holomorphy/order invariance under inversion and translations, the omitted-point parametrization, and the transfer helper `sphere_prescribed_zeros_of_plane`. Its premise still contains the real plane construction; it must not be counted as 15.11.

There is a genuine complication in the arbitrary-plane-domain construction: the nearest-finite-pole product by itself need not work for an unbounded zero sequence. For example, a distant zero and a nearby boundary pole can give a ratio whose norm is not less than one on a fixed compact set. Thus one must either split zeros between entire factors and boundary-pole factors, or normalize a domain point outside the zero set to infinity, as the printed proof does. The latter uses the chart infrastructure already drafted and appears shorter.

The normalized construction can proceed with the following exact intermediate hypotheses:

- `C : Set ℂ` is nonempty and compact (the transformed omitted set).
- `a : ℕ → ℂ` is bounded, has values outside `C`, lists each prescribed zero exactly its finite positive multiplicity, and eventually avoids each compact subset of `Cᶜ`.
- Choose `b n ∈ C` with `infDist (a n) C = dist (a n) (b n)`.

Then `infDist (a n) C → 0` follows without a subsequence argument: for any positive ε, the set `closedBall 0 R ∩ {z | ε ≤ infDist z C}` is compact and contained in `Cᶜ`, so the zero sequence eventually avoids it. Thus `‖a n-b n‖→0`.

`BoundaryProductGeometryWork.lean` is an **uncompiled draft** of this implication plus the following two estimates:

1. On each compact `K ⊆ Cᶜ`, the ratios `(a n-b n)/(z-b n)` eventually have norm at most one half, uniformly on `K`. A positive lower bound on `infDist z C` comes from `IsCompact.exists_forall_le'` applied to the continuous distance function.
2. A common bound `‖b n‖≤B` yields a fixed positive radius ρ at most one with `‖1-b n*w‖≥1/2` whenever `‖w‖≤ρ`, for every n. On this disc, the infinity-coordinate ratios `(a n-b n)*w/(1-b n*w)` eventually also have norm at most one half.

Apply 15.8 with elementary-factor index n (zero-based) to bound both norm-series tails by `(1/2)^(n+1)`. The existing `tendstoUniformlyOn_tsum_nat_eventually` in `Analysis/Normed/Group/FunctionSeries.lean:82` permits an eventual bound directly, so finite initial terms need no separate dominating-series construction. Then 15.6 gives the product and multiplicities on the finite chart and on the infinity chart. All factors at infinity have value one, hence their product has value one there. The two products agree on the punctured chart by the exact rational expression; the chosen value at infinity agrees too.

Remaining real gaps after these drafts: derive the normalized compact-complement/bounded-zero setup from the original sphere data; enumerate the closed discrete set with its positive finite multiplicities; build the analytic elementary factors and prove each has one simple zero at its prescribed point; assemble the two-chart product; finally transport through the proved coordinate equivalence. Empty and finite zero sets require finite-product branches. No gap may be hidden as an extra hypothesis in the final numbered theorem.

Useful enumeration APIs: `Filter.Tendsto.cofinite_of_finite_preimage_singleton` (`Order/Filter/Cofinite.lean:258`) handles projection from multiplicity copies; `IsClosed.tendsto_coe_cofinite_of_isDiscrete` handles escape from compact subsets; `Nat.cofinite_eq_atTop` changes enumeration filters. A countable infinite multiplicity-copy type can be identified with the naturals, while a finite copy type should use its finite product directly.

## Full draft assembly, still uncompiled

The previously listed gaps now have proof drafts, without placeholder proofs, in six isolated book-directory files:

1. `SphereWork.lean`: two charts, inversion/translation homeomorphisms and analytic/order invariance, omitted-point chart.
2. `BoundaryProductGeometryWork.lean`: escape-to-boundary distance and both chart ratio bounds.
3. `ZeroSetNormalizationWork.lean`: a domain point outside the zero set; compact nonempty normalized complement; countable bounded normalized zeros with no accumulation; finite compact intersections.
4. `ZeroMultiplicityEnumerationWork.lean`: the type of finite multiplicity copies; exact `HasSum` counts; infinite enumeration escaping compact domain subsets.
5. `BoundaryProductWork.lean`: actual elementary-factor products, exact zero/multiplicity formula on the finite chart, analytic product at infinity, and finite sphere factors.
6. `PrescribedZerosWork.lean`: normalized finite/infinite constructions and the full statement `prescribed_zeros_on_sphere`, with no omitted existence premise. The finite branch also includes an empty zero set. The empty-domain branch is explicit.

`SpherePrescribedZerosWork.lean` is the generated single-startup assembly, in this dependency order, importing only the chapter base and external Mathlib. The current regenerated assembly contains 1,266 lines, including the plane-domain corollary required by 15.12. Original isolated drafts remain the editing sources; regenerate the combined file after changes before freezing its check snapshot.

**Validation status: none of these 15.11 drafts has been compiled.** Root has reserved the single compiler slot first for the 15.8 base and 15.9–15.10 integration, then this combined 15.11 draft. The full assembly is an implementation candidate, not evidence that node 15.11 passes. Source-level mistakes may remain, and must be fixed from actual compiler output before any completion claim.

## Downstream 15.15 draft while the compiler slot is reserved

`HolomorphicBezoutWork.lean` contains uncompiled proof drafts for removable holomorphic quotients under finite-denominator order inequalities, no-common-zero two-generator Bézout from the exact 15.13 analytic-germ interpolation interface, a minimum-order common divisor from the exact 15.11 plane interface, and open-partition gluing that includes locally identically zero generators and all-zero components. The resulting pair-principal helper keeps both construction interfaces as explicit hypotheses. Finite-family induction over `Fin n`, including the empty family with zero generator, is now drafted too. Arbitrary-Fintype reindexing is now drafted. `HolomorphicIdealAssemblyWork.lean` proves the algebraic equivalence of generated and principal ideals from coefficient identities. `HolomorphicIdealTheoremWork.lean` states the no-extra-premise 15.15 wrappers against the actual names `prescribed_zeros_on_plane` and `interpolate_analytic_germs`; the latter now has a full uncompiled construction in `InterpolationWork.lean`. The final wrapper is present against those draft declarations; successful checks of the construction chain remain required. None of these helpers has been compiled, and no 15.15 completion is claimed.
