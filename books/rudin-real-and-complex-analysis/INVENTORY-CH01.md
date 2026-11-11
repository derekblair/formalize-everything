# Chapter 1 inventory and Mathlib claims check

Verified against the [third-edition scan](https://zaco.au/uni/2023-spr/35007-ra/real-and-complex-analysis-1.pdf), title/copyright pages and printed pp. 6–31 (PDF pp. 21–46). The [publisher contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india) independently confirms the chapter title; it does **not** verify theorem numbering. No numbering was inferred from that contents list.

The complete numbered sequence is **1.1–1.41: 41 items**. There are **25 numbered result-bearing groups** when 1.9, 1.15, 1.22, and 1.24 are included: 21 headings explicitly labeled theorem/proposition/lemma, the propositions within 1.15 and 1.22, and two groups of propositions. Unnumbered corollaries belong to 1.14 and 1.27; they do not create extra numbered items. Definitions, comments, and examples remain inventoried because the package bar includes definition-bearing items. All 41 identifiers and their kinds are VERIFIED. Exercises are excluded.

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
| 1.11 | 12 | Definition: Borel sets | V | `borel`, `IsClosed.measurableSet`, `IsGδ`, `Continuous.measurable`; `IsFSigma` is the book's own definition |
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
| 1.22 | 18 | Arithmetic/proposition: products | V | `ENNReal` semiring/order-continuity, `Measurable.add`, `.mul`; collect stated laws and cancellation restrictions |
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
| 1.34 | 26 | Theorem: dominated convergence | V | `MeasureTheory.hasFiniteIntegral_of_dominated_convergence`, `tendsto_integral_of_dominated_convergence`; package integrability, L1 convergence, integral convergence |
| 1.35 | 27 | Definition: almost everywhere | U | `ae`, `Filter.EventuallyEq`, `lintegral_congr_ae`, `integral_congr_ae` |
| 1.36 | 28 | Theorem: completion | V | `Measure.completion`, `NullMeasurableSet`; sandwich characterization and extension values must be stated |
| 1.37 | 29 | Extended measurability | V | `AEMeasurable`, `AEStronglyMeasurable`, measurable representatives; reconcile partially defined functions |
| 1.38 | 29 | Theorem: integrable series | V | `integral_tsum_of_summable_integral_norm`, `summable_norm_of_tsum_eLpNorm_ne_top`; package a.e. convergence and integrability |
| 1.39 | 30 | Theorem: zero/equality cases | V | `lintegral_eq_zero_iff`, `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`; constant-phase equality clause needs separate proof |
| 1.40 | 30 | Theorem: closed-set averages | M | No exact closed-set converse found by searching `MeasureTheory` for average/closed/a.e.-membership combinations; prove using a countable disk cover |
| 1.41 | 31 | Theorem: finite occurrence | U | `MeasureTheory.ae_eventually_notMem` |

The source and numbering check found no false printed statement. The M entry is a library coverage gap, not a fidelity correction. Partially represented groups must remain incomplete until every clause and attached corollary is covered.

## Branch declaration coverage

All **41/41 numbered items** have a formal representation and proofs of
their assertions in `RudinRCA/Chapter01.lean`; all **25/25 result groups**
and their attached corollaries are proved. This is the author's coverage
claim, pending the coordinator's independent review, not acceptance on
main. Definitions and vocabulary are represented, not mislabeled as new
mathematical theorems. The U/V/M table above records the initial library
claims check; the M result 1.40 is now proved in the book module.

All names below are in `RudinRCA.Chapter01`. A suffix `*` denotes the
explicit family of declarations in that numbered section.

| Node | Declaration coverage |
|---|---|
| 1.1 | `proposition_1_1`; `Set`/function vocabulary documented in module |
| 1.2 | `definition_1_2_topology`, `definition_1_2_continuous` |
| 1.3 | `definition_1_3_sigma`, `definition_1_3_measurable` |
| 1.4 | `definition_1_4_metric`, `definition_1_4_local`, `proposition_1_4_*` |
| 1.5 | `theorem_1_5` |
| 1.6 | `proposition_1_6` |
| 1.7 | `theorem_1_7a`, `theorem_1_7b` |
| 1.8 | `theorem_1_8` |
| 1.9 | `proposition_1_9a`–`proposition_1_9e` |
| 1.10 | `theorem_1_10` |
| 1.11 | `IsFSigma`, `definition_1_11_borel`, `definition_1_11_halfOpen`, `definition_1_11_continuous` |
| 1.12 | `pullbackSigma`, `theorem_1_12a`–`theorem_1_12d` |
| 1.13 | `definition_1_13_*`, `pointwiseSup`, `pointwiseLimsup`, `IsPointwiseLimit` |
| 1.14 | `theorem_1_14`, `theorem_1_14_inf`, `corollary_1_14a`, `corollary_1_14b` |
| 1.15 | `definition_1_15`, `proposition_1_15` |
| 1.16 | `IsSimple`, `IsNonnegativeSimple`, `definition_1_16_*` |
| 1.17 | `theorem_1_17` |
| 1.18 | `BookPositiveMeasure`, `BookComplexMeasure` and their conversion/value theorems |
| 1.19 | `theorem_1_19a`–`theorem_1_19e` and complex-measure addenda |
| 1.20 | `example_1_20a_finite`, `example_1_20a_infinite`, `example_1_20b`, `example_1_20c` |
| 1.21 | `BookMeasureSpaceData`, `measureSpaceData` |
| 1.22 | `definition_1_22`, `proposition_1_22`, cancellation and measurability wrappers |
| 1.23 | `definition_1_23`, `definition_1_23_simple` |
| 1.24 | `proposition_1_24a`–`proposition_1_24f` |
| 1.25 | `proposition_1_25` |
| 1.26 | `theorem_1_26` |
| 1.27 | `theorem_1_27`, `corollary_1_27` |
| 1.28 | `theorem_1_28` |
| 1.29 | `theorem_1_29` |
| 1.30 | `BookL1`, `definition_1_30` |
| 1.31 | `BookComplexIntegral`, `definition_1_31_finite`, `definition_1_31`, `ExtendedIntegralDefined`, `BookExtendedIntegral` |
| 1.32 | `theorem_1_32` |
| 1.33 | `theorem_1_33` |
| 1.34 | `theorem_1_34` |
| 1.35 | `BookAEOn`, `definition_1_35`, `proposition_1_35_*` |
| 1.36 | `completionSigma`, `completedMeasure`, `theorem_1_36` |
| 1.37 | `proposition_1_37` |
| 1.38 | `theorem_1_38` |
| 1.39 | `theorem_1_39a`–`theorem_1_39c` |
| 1.40 | `theorem_1_40`; measurable-representative helper |
| 1.41 | `theorem_1_41` |

### Representation boundaries

- The Borel-target convention is proved equivalent to the book's open-set
  definition in 1.3. Sequences use natural indices starting at zero.
- Nonnegative simple functions are finite-valued; 1.17 explicitly excludes
  infinity, and 1.23 proves that these finite-valued approximants suffice.
- 1.18 reconstructs measures from exactly the book's countable-additivity
  and finite-somewhere data, preserving every measurable-set value.
- Before 1.37, `BookL1` includes ordinary measurability. Its bridge to
  Mathlib `Integrable` and the four-term integral identity are proved in
  1.30–1.31. After 1.37, null modifications/partially defined functions are
  handled by measurable representatives; 1.40 does not impose extra
  ordinary measurability on the supplied integrable function.
- 1.15 is valid even with Mathlib's totalized extended subtraction; it
  therefore adds no exclusion of simultaneous infinities. The book's
  explicitly restricted extended integral in 1.31 has an explicit domain.
- `Set`, interval, image/preimage, and function vocabulary in 1.1, and the
  typed ordered-triple convention in 1.21, are representation choices.
  Historical discussion and examples of applications in later chapters
  are not asserted as new theorems here.

No Chapter 1 printed statement was corrected or weakened. The counting-tail
counterexample in 1.20(c) is the book's own example, not a fidelity event.
