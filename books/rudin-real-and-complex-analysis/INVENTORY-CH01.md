# Chapter 1 inventory and Mathlib claims check

Verified against the [third-edition scan](https://zaco.au/uni/2023-spr/35007-ra/real-and-complex-analysis-1.pdf), title/copyright pages and printed pp. 6–31 (PDF pp. 21–46). The [publisher contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india) independently confirms the chapter title; it does **not** verify theorem numbering. No numbering was inferred from that contents list.

The complete numbered sequence is **1.1–1.41: 41 items**. There are **24 numbered result-bearing groups** when 1.9, 1.15, and 1.24 are included: 21 headings explicitly labeled theorem/proposition/lemma, the proposition within 1.15, and two groups of propositions. Unnumbered corollaries belong to 1.14 and 1.27; they do not create extra numbered items. Definitions, comments, and examples remain inventoried because the package bar includes definition-bearing items. All 41 identifiers and their kinds are VERIFIED. Exercises are excluded.

Mathlib checkout inspected: `d13f23b723b8a846827a245b89c10fc7d3f11612`. **U** = already in Mathlib in usable form; **V** = Mathlib variant/components needing a faithful restatement or packaging; **M** = exact content missing in the inspected sources (not a claim that the result cannot be proved). A candidate mapping is not a book proof. In particular, `Integrable` alone uses almost-everywhere strong measurability; before 1.37 the book additionally requires ordinary measurability. Completion and finite-valued simple functions also need explicit bridges.

| Node | Printed page | Kind / topic | Claim | Pinned Mathlib declaration or implementation route |
|---|---:|---|:---:|---|
| 1.1 | 6 | Notation | U | `Set`, `EReal`, function composition; foundational vocabulary |
| 1.2 | 8 | Definition: topology | U | `TopologicalSpace`, `Continuous` |
| 1.3 | 8 | Definition: measurability | V | `MeasurableSpace`, `Measurable`; target uses `borel Y` |
| 1.4 | 9 | Comments: metric topology | V | `MetricSpace`, `Metric.ball`, `ContinuousAt`, `OrderTopology EReal`; bundled explanatory claims |
| 1.5 | 9 | Proposition: continuity | U | `continuous_iff_continuousAt` |
| 1.6 | 10 | Comments: sigma-algebra closure | U | `MeasurableSet.empty`, `.union`, `.iInter`, `.diff` |
| 1.7 | 10 | Theorem: composition | U | `Continuous.comp`, `Continuous.measurable`, `Measurable.comp` |
| 1.8 | 11 | Theorem: paired functions | U | `Measurable.prodMk`, then continuous composition |
| 1.9 | 11 | Propositions: complex operations | V | `Measurable.re`, `.im`, `.norm`, `.add`, `.mul`, `.indicator`; measurable unit phase requires value 1 at zero |
| 1.10 | 12 | Theorem: generated sigma-algebra | U | `MeasurableSpace.generateFrom`, `measurableSet_generateFrom`, `generateFrom_le` |
| 1.11 | 12 | Definition: Borel sets | V | `borel`, `IsClosed.measurableSet`, `IsGδ`, `IsFσ`, `Continuous.measurable` |
| 1.12 | 13 | Theorem: pullbacks | V | `MeasurableSpace.map`, `Measurable`, `Measurable.comp`, `measurable_of_Ioi`; real-threshold `EReal` formulation requires endpoint handling |
| 1.13 | 13 | Definition: limit extrema | V | `Filter.limsup`, `Filter.liminf`, `limsup_eq_iInf_iSup_of_nat`; subsequence characterization included in prose |
| 1.14 | 14 | Theorem/corollaries: measurable limits | U | `Measurable.iSup`, `.iInf`, `.limsup`, `.liminf`, `.sup`, `.inf`, `measurable_of_tendsto_metrizable` |
| 1.15 | 15 | Definition/proposition: positive parts | V | Lattice positive/negative-part identities; minimality proved by `max_le` after interpreting subtraction |
| 1.16 | 15 | Definition: simple functions | V | `MeasureTheory.SimpleFunc` bundles measurable finite-range functions; book initially separates these properties and excludes infinity |
| 1.17 | 15 | Theorem: simple approximation | V | `SimpleFunc.eapprox`, `monotone_eapprox`, `iSup_eapprox_apply`; prove approximants never equal infinity |
| 1.18 | 16 | Definition: measures | V | `MeasureTheory.Measure`, `ComplexMeasure`; outer-measure representation versus values on measurable sets |
| 1.19 | 16 | Theorem: measure properties | U | `measure_empty`, `measure_biUnion_finset`, `measure_mono`, monotone/antitone continuity of measure |
| 1.20 | 17 | Examples | V | `Measure.count`, `Measure.dirac`; descending infinite tails give failure without finite initial measure |
| 1.21 | 17 | Terminology | U | Types and instances supply the underlying space/sigma-algebra/measure data |
| 1.22 | 18 | Extended arithmetic | V | `ENNReal` semiring/order-continuity, `Measurable.add`, `.mul`; collect stated laws and cancellation restrictions |
| 1.23 | 19 | Definition: positive integral | V | `SimpleFunc.lintegral`, `lintegral`, `lintegral_eq_nnreal`; reconcile finite-valued simple functions |
| 1.24 | 19 | Propositions: integral properties | U | `lintegral_mono`, `lintegral_mono_set`, `lintegral_const_mul`, `lintegral_zero`, `lintegral_indicator`, restriction to null sets |
| 1.25 | 20 | Proposition: simple integration | U | `Measure.withDensity`, `withDensity_apply`, `lintegral_add_left`; specializes to finite-valued simple functions |
| 1.26 | 21 | Theorem: monotone convergence | U | `ENNReal.measurable_of_tendsto`, `lintegral_tendsto_of_tendsto_of_monotone` |
| 1.27 | 22 | Theorem/corollary: series | U | `lintegral_tsum`, `ENNReal.tsum_comm` |
| 1.28 | 23 | Lemma: Fatou | U | `lintegral_liminf_le` |
| 1.29 | 23 | Theorem: density measure | U | `Measure.withDensity`, `withDensity_apply`, `lintegral_withDensity_eq_lintegral_mul` |
| 1.30 | 24 | Definition: integrability | V | `Integrable`, `HasFiniteIntegral`, plus ordinary `Measurable` |
| 1.31 | 24 | Definition: complex integral | V | Bochner `integral`, real/imaginary projections, positive/negative decomposition; also extended-real integral convention |
| 1.32 | 25 | Theorem: linearity | U | `Integrable.add`, `.const_mul`, `integral_add`, `integral_const_mul`; retain ordinary measurability |
| 1.33 | 26 | Theorem: integral bound | U | `norm_integral_le_integral_norm` |
| 1.34 | 26 | Theorem: dominated convergence | V | `integrable_of_dominated_convergence`, `tendsto_integral_of_dominated_convergence`; package integrability, L1 convergence, integral convergence |
| 1.35 | 27 | Definition: almost everywhere | U | `ae`, `Filter.EventuallyEq`, `lintegral_congr_ae`, `integral_congr_ae` |
| 1.36 | 28 | Theorem: completion | V | `Measure.completion`, `NullMeasurableSet`; sandwich characterization and extension values must be stated |
| 1.37 | 29 | Extended measurability | V | `AEMeasurable`, `AEStronglyMeasurable`, measurable representatives; reconcile partially defined functions |
| 1.38 | 29 | Theorem: integrable series | V | `integral_tsum_of_summable_integral_norm`, `summable_norm_of_tsum_eLpNorm_ne_top`; package a.e. convergence and integrability |
| 1.39 | 30 | Theorem: zero/equality cases | V | `lintegral_eq_zero_iff`, `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`; constant-phase equality clause needs separate proof |
| 1.40 | 30 | Theorem: closed-set averages | M | No exact closed-set converse found by searching `MeasureTheory` for average/closed/a.e.-membership combinations; prove using a countable disk cover |
| 1.41 | 31 | Theorem: finite occurrence | U | `MeasureTheory.ae_eventually_notMem` |

The source and numbering check found no false printed statement. The M entry is a library coverage gap, not a fidelity correction. Partially represented groups must remain incomplete until every clause and attached corollary is covered.
