# 13.6 analytic route at the pinned Mathlib revision

This is an implementation plan and source audit, not completion of 13.6.
`RungeFunctional.lean` contains a proof attempt for the supporting lemmas below;
its initial check is queued in `runge-functional-check.log`.

Use the Banach algebra C(K) and a continuous complex linear functional L directly.
The book's Riesz representation/Fubini detour is unnecessary: continuous linear
maps commute with the segment Bochner integrals, giving the same annihilator
argument with the exact original conclusion.

The proposed chain is:

1. Rational restrictions with poles in the prescribed spherical set A form a
   complex linear subspace M of C(K). The closure criterion says f|K belongs
   to closure(M) iff every bounded linear annihilator of M also kills f|K.
   `RungeFunctional.lean` proves the criterion by separating the quotient by
   the closed subspace, using `SeparatingDual.eq_zero_of_forall_dual_eq_zero`.
2. Let q be the coordinate function on K. `ContinuousMap.spectrum_eq_range`
   (Topology/ContinuousMap/Units.lean:112) gives spectrum(q)=K. The resolvent
   `(z*1-q)⁻¹` evaluates pointwise to `(z-x)⁻¹`; its L-image is holomorphic
   on the complement, by `spectrum.hasDerivAt_resolvent_const_left`
   (Analysis/Normed/Algebra/GelfandFormula.lean:53).
3. At a finite prescribed pole α, all positive powers of resolvent(q,α) are
   rational restrictions with that one pole. A geometric expansion gives
   local vanishing of L(resolvent(q,z)) near α. The algebraic identity used is
   R(z)=R(α)*(1-(α-z)*R(α))⁻¹. The draft proves the identity and the local
   vanishing lemma using `hasSum_geom_series_inverse`.
4. At infinity, the inverse-chart extension is
   `w ↦ L(w * (1-w*q)⁻¹)`, analytic at zero and equal to L(R(1/w)) away
   from zero. If infinity is prescribed, annihilation of all powers of q
   makes this expression locally zero by the same geometric series.
   `spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul` is the exact
   analyticity API (Analysis/Normed/Algebra/Spectrum.lean:354).
5. On the spherical complement of K, the set of points where this transform
   is locally zero is clopen: use isolated zeros in each finite chart and in
   the inverse chart at infinity. The draft includes the abstract topological
   zero-germ lemma and component propagation. The remaining bridge is the
   transport of the analytic dichotomies to the spherical complement subtype.
   Since every component contains a prescribed point, the transform vanishes
   everywhere on the spherical complement. This handles a finite prescribed
   point in the unbounded component without adding infinity to A.
6. Use the actual 13.5 cycle representation as a C(K)-valued identity. Commute
   L through each finite segment integral using
   `ContinuousLinearMap.intervalIntegral_comp_comm`
   (MeasureTheory/Integral/IntervalIntegral/Basic.lean:872). The transform is
   zero on the cycle, so L(f|K)=0.
7. Hahn–Banach gives closure membership, and the metric characterization of
   closure gives an element of M within ε in supremum norm. Unpack its rational
   function witness and the original pole restriction. K empty must be
   handled uniformly or as an explicit trivial case.

Additional pinned spectral topology API, useful for alternate pole movement:
`Subalgebra.spectrum_sUnion_connectedComponentIn` (Spectrum.lean:665),
`Subalgebra.spectrum_isBounded_connectedComponentIn` (686), and
`Subalgebra.spectrum_eq_of_isPreconnected_compl` (702). A closed subalgebra's
extra spectrum fills whole bounded complement components. This does not by
itself settle the case where infinity is forbidden, because the coordinate
function need not initially belong to the allowed rational subalgebra.

Root is separately proving the printed countability assertion for spherical
complement components in `PolynomialObstruction.lean`, using open finite-chart
preimages and `PairwiseDisjoint.countable_of_isOpen`.

## Frozen source dependency order

- `RungeFunctional.lean` is frozen in the first aggregate batch `AllPending.lean`.
- `CauchyTransformSphere.lean` is frozen for the next batch and must occur after
  `RungeFunctional.lean`, whose declarations it uses. It also imports the built
  Chapter13 sphere definitions. It supplies the inverse-chart transport,
  isolated-zero component argument, and `compact_cauchy_transform_eq_zero`.
- Neither frozen source has a successful check yet; parent owns aggregate
  diagnostics and their controlled unfreezing. Do not count 13.6 complete.

## Later scratch assembly state

`RungeAssembly.lean` packages the universal `FiniteCauchyRepresentation K Ω`
input explicitly, proves closure by the Cauchy-transform/annihilator argument,
and extracts a canonical RatFunc witness. `RungeUniformSequences.lean` supplies
uniform rational and polynomial sequences. `OpenRungeAssembly.lean` combines
that compact theorem with the full validated 13.3 exhaustion to obtain the
13.9 locally uniform sequences, preserving prescribed spherical poles.

`MittagLefflerCore.lean`, `MittagLefflerSeries.lean`, and
`MittagLefflerAssembly.lean` carry the chain through exact prescribed principal
parts (13.10); see `mittag-leffler-api-plan.md`. The final existence prerequisite
is explicit universal finite Cauchy representation existence, to be supplied by
the parent's grid proof. `PolygonalPrimitives.lean` independently constructs
13.11(f)→(g) from actual vanishing closed piecewise-C¹ path integrals.

All of these later drafts remain pending aggregate compiler checks. The first
aggregate verified full `Exhaustion.lean` with permitted axioms. Initial
RungeFunctional diagnostics exposed incorrect qualification `spectrum.resolvent`
(the definition is global `resolvent`), explicit quotient/scalar arguments, and
the closed-complement iff name; originals were corrected. Two additional static
corrections (inverse-product final step and `Units.smul_def`) are present in the
original but were made after the second aggregate snapshot. The parent owns
aggregate runs; no individual Lean compile should be queued while this shared
host is under memory pressure.
