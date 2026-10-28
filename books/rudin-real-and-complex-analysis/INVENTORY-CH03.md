# Chapter 3 inventory and pinned Mathlib claims check

Source: the [1987 third-edition scan and OCR](https://djvu.online/file/NKmAEzkLVs8Io), printed pp. 61–71. The [publisher's contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india) independently confirms Chapter 3 and its title. Numbered headings 3.1–3.17 are verified; no invented numbering. OCR loses inequality bars: endpoint-sensitive statements below were checked against the scan. Exercises are excluded.

**Count:** 17 numbered items: 10 theorems, 5 definitions, 2 numbered remarks. All 17 are inventoried; no original numbered item is yet counted proved. The counterexample and repair for 3.7 are separate results, not completion of that item.

Mathlib was inspected at `d13f23b723b8a846827a245b89c10fc7d3f11612`. `U` = already in Mathlib in usable form; `V` = variant requiring a faithful restatement/bridge; `M` = missing packaged result after the searches described below. This classifies reuse, not book-node completion. For definitions, it classifies the corresponding representation.

| Node | Kind; printed page | Subject | Claim | Exact Mathlib route / remaining issue |
|---|---|---|---|---|
| 3.1 | Definition; 61 | Interval convexity | V | `ConvexOn`; associated slope and derivative characterizations require separate restatements. |
| 3.2 | Theorem; 61–62 | Convexity implies continuity | U | `ConvexOn.continuousOn` on an open interval, `Analysis/Convex/Continuous.lean`. |
| 3.3 | Theorem; 62–63 | Jensen inequality | V | `ConvexOn.map_integral_le`, `Analysis/Convex/Integral.lean`, assumes a closed convex set and integrability of the composition. Rudin permits an open interval and an infinite upper integral; those cases must be retained. |
| 3.4 | Definition; 63 | Conjugate exponents | V | `Real.HolderConjugate` and `ENNReal.HolderConjugate`; bridge finite parameters and the endpoint pair. |
| 3.5 | Theorem; 63–65 | Hölder and Minkowski | U | `MeasureTheory.lintegral_mul_le_Lp_mul_Lq`, `MeasureTheory.lintegral_Lp_add_le`, `MeasureTheory/Integral/MeanInequalities.lean`; finite exponents, nonnegative extended-valued measurable functions. |
| 3.6 | Definition; 65 | Finite-exponent Lp norm | V | `MeasureTheory.eLpNorm`, `MeasureTheory.MemLp`; distinguish actual measurable representatives from AE strong measurability. |
| 3.7 | Definition; 65–66 | Essential supremum; L∞ | V; FIDELITY HOLD | `MeasureTheory.essSup`, `eLpNorm_exponent_top`. The printed real-threshold set is unbounded below for zero measure; see the event below. |
| 3.8 | Theorem; 66 | Product in L1; Hölder including endpoints | V | `MeasureTheory.MemLp.mul`, `MeasureTheory.eLpNorm_smul_le_mul_eLpNorm`, `LpSeminorm/CompareExp.lean`. The printed L∞ convention must first be repaired explicitly. |
| 3.9 | Theorem; 66 | Lp addition; triangle inequality | V | `MeasureTheory.MemLp.add`, `MeasureTheory.eLpNorm_add_le`, `LpSeminorm/TriangleInequality.lean`; endpoint depends on 3.7. |
| 3.10 | Remarks; 66–67 | Vector space; AE quotient metric | V | `MeasureTheory.Lp.instNormedAddCommGroup`, `Lp.instModule`, `MemLp.toLp_eq_toLp_iff`, `Lp.dist_def`; separate representative/quotient bridge. |
| 3.11 | Theorem; 67–68 | Lp completeness, including infinity | V | `MeasureTheory.Lp.instCompleteSpace`, `LpSpace/Complete.lean`; direct after the explicit convention decision for 3.7. |
| 3.12 | Theorem; 68 | AE convergent subsequence | U | `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` then `TendstoInMeasure.exists_seq_tendsto_ae`, `Function/ConvergenceInMeasure.lean`. |
| 3.13 | Theorem; 69 | Simple-function density | V | `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`, `Function/SimpleFuncDenseLp.lean`; translate its subtype to finite-range measurable functions with finite-measure support. |
| 3.14 | Theorem; 69 | Compactly supported continuous density | V | `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, `Function/ContinuousMapDense.lean`; Mathlib assumes `μ.Regular`, whereas Rudin uses the completion/regularity package of 2.14. Preserve that distinction. |
| 3.15 | Remarks; 69–70 | Euclidean Lp completions | V | Combine 3.11/3.14 with `BoundedContinuousFunction.toLp_injective` and positive-open-set Lebesgue measure; includes the different infinity completion. |
| 3.16 | Definition; 70 | Continuous functions vanishing at infinity | U | `ZeroAtInftyContinuousMap`, `Topology/ContinuousMap/ZeroAtInfty.lean`. |
| 3.17 | Theorem; 70–71 | C₀ completion of Cc | M (assembled theorem) | `ZeroAtInftyContinuousMap.instCompleteSpace` supplies completeness. No packaged Cc-to-C₀ density/completion theorem found in `Topology/ContinuousMap`, `Analysis`, or whole-tree density searches. Urysohn cutoff construction remains. |

The 17 classifications are U=4, V=12, M=1. These are source-level claims checks, not successful Lean invocations of every listed route.

## Fidelity event 3.7

The [p.65 scan](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/077.webp) specifies real thresholds, with no nonnegativity restriction. On a singleton with zero measure and zero function every real threshold qualifies. Thus that set has no real lower bound and no real infimum in the order-theoretic sense. Using an extended-real infimum instead gives minus infinity, which is not a nonnegative norm. This is a defect in the definition's zero-measure case, not a claimed failure of the standard Lp theorems.

`Chapter03.lean` stops the printed definition, proves the unboundedness counterexample, and proves an explicitly labelled correction using thresholds in `ℝ≥0∞`. The corrected essential supremum is zero for zero measure, is an almost-everywhere upper bound, and is the least such bound. No downstream node is counted complete by silently adopting this repair. Coordinator disposition is recorded in `QUEUE.md`.
