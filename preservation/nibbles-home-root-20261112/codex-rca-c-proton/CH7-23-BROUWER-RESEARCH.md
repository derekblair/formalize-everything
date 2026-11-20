# Chapter 7.23: faithful Brouwer support research

Research only, 2026-10-29. No dependency changes, installations, builds, or external communications. This report does not establish local compatibility or a local axiom audit.

## Printed obligation

Rudin 7.23: for a continuous map F on the closed Euclidean unit ball, if 0 < ε < 1 and ‖F(x) − x‖ < ε on the unit sphere, then F of the open unit ball contains the open ball of radius 1 − ε centered at zero. The OCR loses the closure bar in places; the boundary hypothesis and printed proof determine the closed-ball domain. The proof uses Brouwer on G(x) = (a − F(x)) / ‖a − F(x)‖ for a hypothetically omitted a. Boundary estimates exclude a and rule out boundary fixed points; interior points cannot equal a unit vector. A contraction/open-map hypothesis would weaken the obligation and is not acceptable.

## Pinned Mathlib search

The pinned source has no identified Brouwer fixed-point theorem, KKM theorem, triangulation Sperner lemma, applicable no-retraction theorem, or sphere-degree theorem. `Combinatorics/SetFamily/LYM.lean` concerns Sperner's antichain theorem, not the needed combinatorial simplex/cube lemma. Generic homotopy/algebraic-topology foundations do not directly supply this result. This is a source search finding, not a claim that no proof could be developed there.

## Reusable proof found

Primary repository: https://github.com/harfe/fixed-point-theorems-lean4

Recommended source snapshot: **d9c3aba7340f21a13df59c61d92bfe9622e40da2** (2026-09-21). Its actual `lean-toolchain` is `leanprover/lean4:v4.34.0`; `lakefile.toml` requires Mathlib `v4.34.0`. Our task is pinned to Lean4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. This is close enough to justify a later compatibility attempt, but compatibility is presently untested.

Source snapshot: https://github.com/harfe/fixed-point-theorems-lean4/tree/d9c3aba7340f21a13df59c61d92bfe9622e40da2
Successful upstream build: https://github.com/harfe/fixed-point-theorems-lean4/actions/runs/35646217495/job/106487216166
Upstream CI runs `leanprover/lean-action@v1`; this success is not evidence that the separate `scripts/AxiomAudit.lean` was run.

The current main commit 93a3eed3364281a9dbf9652bb52356a8db65057c has a merge message mentioning 4.33.1 but its actual files use 4.35.0. Do not infer compatibility from its commit message. The earlier recommended snapshot is preferable.

License: **MIT**, copyright (c) 2026 harfe. Preserve the complete upstream copyright and permission notice in any copied substantial source. Exact license: https://github.com/harfe/fixed-point-theorems-lean4/blob/d9c3aba7340f21a13df59c61d92bfe9622e40da2/LICENSE

Exact top theorem, with no extra mathematical hypotheses:

```lean
theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ s : Set V, Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ f : C(s, s), ∃ x, f x = x
```

The proof uses compact-convex homeomorphisms to a finite cube and cubical Sperner. It allows lower-dimensional compact convex sets and zero-dimensional ambient spaces. The required ball case follows by specializing to a finite-dimensional Euclidean space and its closed unit ball. The Kakutani file is not needed.

## Required proof dependency closure

All five source files below were fetched read-only from the exact recommended commit and scanned for whole-word `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, and `extern`. No matches were found. This syntactic scan is preliminary evidence; local compilation and `#print axioms brouwer_fixed_point` remain mandatory. The upstream audit script exists and prints the Brouwer/cube axiom sets, but no inspected upstream CI step invokes it.

- `FixedPointTheorems/cubical_sperner_prep.lean`: 1670 lines, 50083 bytes, SHA256 `f5b616d8b6c22c4785aada0de45dd1702ae923c511bfa24af05d6be4a0689fb3`. Imports: `public import Mathlib.Combinatorics.Enumerative.DoubleCounting`, `import Mathlib.Algebra.BigOperators.Ring.Nat`, `import Mathlib.Tactic`.
- `FixedPointTheorems/cubical_sperner.lean`: 833 lines, 21852 bytes, SHA256 `41511111b38d21f7b77b7f45f7efd6f3928df8bb1c181120c2e7da6856e92e01`. Imports: `public import FixedPointTheorems.cubical_sperner_prep`, `import Mathlib.Algebra.BigOperators.Ring.Nat`, `import Mathlib.Tactic`.
- `FixedPointTheorems/apply_cubical_sperner.lean`: 290 lines, 8815 bytes, SHA256 `02fc3b0346cbc016115cee34903a5755bafa78133f4437e85fbad44cf6b70650`. Imports: `public import Mathlib.Analysis.Convex.Intrinsic`, `public import Mathlib.Topology.Defs.Basic`, `public import FixedPointTheorems.cubical_sperner`.
- `FixedPointTheorems/convex_homeos.lean`: 134 lines, 4971 bytes, SHA256 `804c8c0d1687248bbb9e820e61d0e80aba7542ad15896bc846cb5fc702f3bc57`. Imports: `public import Mathlib.Analysis.Convex.Intrinsic`, `public import Mathlib.Analysis.Convex.GaugeRescale`.
- `FixedPointTheorems/brouwer.lean`: 44 lines, 1894 bytes, SHA256 `8b2f9924d63ae256cbead189a668486cee28811320e590b32ebc15fa1f8f266c`. Imports: `public import FixedPointTheorems.apply_cubical_sperner`, `public import FixedPointTheorems.convex_homeos`, `public import Mathlib.Dynamics.FixedPoints.Basic`.

The project uses `module`, `public import`, and `@[expose] public section` in several support files; those wrappers may require adaptation if consolidating into an ordinary book module. The combinatorial files import `Mathlib.Tactic`; avoid importing more than necessary after initial compatibility has been established.

## Other candidates ruled out as direct proof sources

- Lean evaluation page https://lean-lang.org/eval/problems/brouwer_fixed_point/ recognizes an outside-Mathlib proof, but the benchmark theorem itself is an obligation, not reusable proof evidence.
- Mathlib PR https://github.com/leanprover-community/mathlib4/pull/36770 proves invariance of domain **assuming** Brouwer; it does not discharge Brouwer.

## Next authorized implementation stage

After Chapter6 is complete and root authorizes work: copy the five MIT-licensed support sources into the book's allowed support layout, preserve attribution and full license, adapt imports against the existing pin without changing dependencies, compile serially, and audit the final Brouwer theorem's axioms. Then prove Rudin7.23 from it with the exact strict boundary estimate and open-image conclusion. No compilation or vendoring has been attempted during this research phase.

## Exact 7.23 derivation against the pinned APIs

A convenient faithful signature uses a total ambient function with continuity only on the required domain:

```lean
{V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
(F : V → V) (hF : ContinuousOn F (Metric.closedBall 0 1))
{ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
(hclose : ∀ x, ‖x‖ = 1 → ‖F x - x‖ < ε) :
Metric.ball 0 (1 - ε) ⊆ F '' Metric.ball 0 1
```

Specializing `V := EuclideanSpace ℝ (Fin n)` is precisely the book's Euclidean assertion. This stronger ambient-space generality uses the same assumptions on F and does not weaken the numbered result. Alternatively use a continuous map whose domain is the closed-ball subtype; no behavior outside the closed ball is used.

1. Fix `a` with `ha : ‖a‖ < 1 - ε`, and assume `a ∉ F '' Metric.ball 0 1`. For any `x` in the closed unit ball, prove `a - F x ≠ 0`. If `‖x‖ < 1`, equality contradicts the missing-image assumption. Otherwise `‖x‖ = 1` follows from `‖x‖ ≤ 1`. If `F x = a`, the pinned inequality `norm_sub_norm_le x (F x)` gives `1 - ‖a‖ ≤ ‖x - F x‖`; use `norm_sub_rev` and `hclose` to contradict `ha` by `linarith`. Thus the denominator never vanishes on the whole closed ball, including its boundary.

2. Put `B := Metric.closedBall (0 : V) 1`, `v (x : B) := a - F x`, and `g x := NormedSpace.normalize (v x)`. The pinned file `Mathlib.Analysis.Normed.Module.Normalize` supplies:

```lean
NormedSpace.normalize x = ‖x‖⁻¹ • x -- definition
NormedSpace.norm_normalize : x ≠ 0 → ‖NormedSpace.normalize x‖ = 1
NormedSpace.norm_smul_normalize (x) :
  ‖x‖ • NormedSpace.normalize x = x
```

The normalization file has no continuity wrapper, but it is immediate with existing APIs: `hF.domRestrict` gives continuity of F on B, then `hv := continuous_const.sub hF.domRestrict`, and `((hv.norm).inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hv_ne x))).smul hv` gives continuity of g. Package `g` into `C(B,B)` using `Continuous.subtype_mk` and the unit-norm bound. The exact pinned continuity names are `ContinuousOn.domRestrict`, `Continuous.inv₀`, `Continuous.norm`, `Continuous.smul`, and `Continuous.subtype_mk`.

3. Apply the located `brouwer_fixed_point` to B, with `convex_closedBall 0 1`, `isCompact_closedBall 0 1`, and `Metric.nonempty_closedBall.mpr zero_le_one`. The pinned `FiniteDimensional.proper_real` instance supplies properness under the stated assumptions, so there is no extra compactness hypothesis. Obtain x and use `congrArg Subtype.val` on its fixed-point identity to get `g x = (x : V)`. Then `NormedSpace.norm_normalize` gives `‖(x : V)‖ = 1`, so the boundary estimate applies.

4. Let `r := ‖a - F x‖`. From `NormedSpace.norm_smul_normalize` and the fixed-point equation, obtain `r • x = a - F x`. Consequently

```text
(1 + r) • x = a + (x - F x).
```

For the vector equality, expand with `add_smul`, `one_smul`, rewrite the scalar identity, and finish by the additive-group tactic `abel`. Taking norms and using `norm_smul_of_nonneg (add_nonneg zero_le_one (norm_nonneg _))`, `‖x‖ = 1`, and `norm_add_le` gives

```text
1 + r ≤ ‖a‖ + ‖x - F x‖ < (1 - ε) + ε = 1.
```

This contradicts `0 ≤ r` by `linarith`. It avoids inner-product infrastructure entirely while preserving the printed conclusion. Only the norm triangle inequality is needed after Brouwer.

For ball conversions, `simpa only [Metric.mem_ball, dist_zero_right]` and `simpa only [Metric.mem_closedBall, dist_zero_right]` avoid dependence on generated norm-ball aliases. The boundary can be stated as `‖x‖ = 1`, equivalently `x ∈ Metric.sphere 0 1`.

### Edge cases

- `n = 0` needs **no separate exclusion or positive-dimension hypothesis**. The ambient type is still nonempty, the unit closed ball is nonempty/compact/convex, and the located Brouwer theorem covers it. The nonzero-vector hypothesis used to normalize is derived only under the contradictory omitted-image assumption; no nonzero vector is postulated in dimension zero.
- The input `0 < ε < 1` implies `0 < 1 - ε` by `sub_pos.mpr hε1`. Preserve both strict inequalities in the public statement. The closed ball's radius is exactly1 and its nonemptiness uses only `zero_le_one`.
- If a later scaled corollary uses a ball of radius R, require `0 < R` before division/scaling; R=0 has an empty open source ball and is not covered by a positive target-radius claim. No scaling is needed for the exact numbered lemma.
- Do not replace the boundary's strict error `< ε` with a global error bound, do not assert continuity outside the closed ball, and do not require an open mapping or contraction.

This is a checked source/API plan, not a Lean elaboration/build claim. No Chapter07 implementation has been written.

## Evaluation-tactic precheck

The same five exact-commit source files were scanned for `native_decide`, `decide_cbv`, `reduceBool`, `reduceNat`, `implemented_by`, `of_decide_eq_true`, `bv_decide`, `native`, `unsafe`, `extern`, `eval`-prefixed identifiers, `run_tac`, `run_elab`, `Lean.ofReduce`, `trust`, and `decide`. Results:

- `FixedPointTheorems/cubical_sperner_prep.lean`: no matches.
- `FixedPointTheorems/cubical_sperner.lean`: no matches.
- `FixedPointTheorems/apply_cubical_sperner.lean`: no matches.
- `FixedPointTheorems/convex_homeos.lean`: no matches.
- `FixedPointTheorems/brouwer.lean`: no matches.

No native-evaluation proof mechanism was found. Ordinary kernel `decide` occurrences, if listed, are acceptable under the requested axiom policy. Source scanning does not replace compiling and inspecting `#print axioms brouwer_fixed_point` at the book pin.
