# Chapter 13.3 implementation plan and source API check

Prepared while the Chapter13.1 infinity-polynomial check waits in the lane compile queue.
This file is a plan, not a proof certificate.

Use zero-based indices in Lean, with `N n = (n+1 : ℝ)` and

```
K n = closedBall 0 (N n) ∩ ⋂ a ∉ Ω, {z | (N n)⁻¹ ≤ dist z a}.
```

This is exactly Rudin's construction after shifting his positive indexing.

1. `K n ⊆ Ω`: if `z ∉ Ω`, apply its separation clause at `a=z`, contradicting
   `(N n)⁻¹>0` and `dist z z=0`.
2. Compactness: closed intersection of the closed ball and the closed distance
   superlevel sets; closed subset of the compact ball.
3. Monotonicity: larger radius, smaller reciprocal distance threshold.
4. Interior nesting: for `z∈K n`, choose a positive radius less than both `1`
   and `(N n)⁻¹-(N(n+1))⁻¹`. Triangle inequalities give a ball contained in
   `K(n+1)` uniformly for all `a∉Ω`.
5. Union equals `Ω`: at each point use an open ball inside `Ω`, then choose a
   natural index large enough for both its norm and the reciprocal radius.
6. Compact cofinality: interiors cover `Ω` by steps 4–5; monotonicity makes
   them a directed cover. `IsCompact.elim_directed_cover` then gives one
   containing compact level. An alternative uses
   `IsCompact.exists_cthickening_subset_open` and a uniform norm bound.

The complement-component clause is not a `CompactExhaustion` field. Prove it
using the following general component lemma:

> If `A⊆T`, and every `x∈T` lies in a preconnected subset `S⊆T` meeting `A`,
> then for every `x∈T` there is `a∈A` with
> `connectedComponentIn A a ⊆ connectedComponentIn T x`.

Available exact APIs in `Topology/Connected/Basic.lean`:

- line 555: `IsPreconnected.subset_connectedComponentIn hs hxs hsT`.
- line 587: `connectedComponentIn_eq (h : y ∈ connectedComponentIn T x)`.
- line 667: `connectedComponentIn_mono x (h : A ⊆ T)`.
- line 273: `IsPreconnected.subset_closure hs (hST : S ⊆ T)
  (hTcl : T ⊆ closure S)`.
- line 302: `IsPreconnected.image`.

For `A=(coe '' Ω)ᶜ` and `T=(coe '' K n)ᶜ`, a point in a small disc about
`a∉Ω` has its whole connected disc inside `T` and meeting `A` at `coe a`.
`Metric.isPreconnected_ball` is in
`Analysis/Normed/Module/Connected.lean:171`, and `OnePoint.continuous_coe`
preserves its preconnectedness under the embedding.

For a finite point `z` outside the radius bound, one can avoid proving the
whole infinity disc connected: take the radial ray `{t • z | 1≤t}` and adjoin
infinity. Its planar part is the continuous image of `Ici 1`, hence
preconnected; all its points remain outside the radius bound. It is unbounded,
so infinity belongs to the closure of its image in `OnePoint ℂ`. The
`IsPreconnected.subset_closure` lemma shows that adjoining infinity preserves
preconnectedness. The resulting set meets `A` at infinity. For the point
infinity itself, use the singleton.

The closure-at-infinity step follows directly from
`OnePoint.hasBasis_nhds_infty` (`OnePoint/Basic.lean:325`): every infinity
neighborhood contains the complement of a closed compact planar set. A
compact set is norm-bounded; the ray is unbounded. Thus every such
neighborhood meets the ray. This route also works without invoking the
real dimension of the plane.

None of these reductions drops clause (c), assumes the open set connected,
or replaces spherical complements by planar complements.

Implementation attempt: `Exhaustion.lean` now contains the explicit construction, compactness, nesting, union, compact cofinality, and full spherical-component clause, assembled as `compact_exhaustion_with_spherical_complement_components`. Its first compile is queued under `lean-compile.lock`; this is not yet verified. It imports the already-built Chapter13 sphere helpers.
