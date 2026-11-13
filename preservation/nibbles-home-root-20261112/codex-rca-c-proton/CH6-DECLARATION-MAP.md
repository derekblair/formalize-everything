# Chapter 6 declaration map

2026-10-29. Navigation map for the nineteen printed nodes, 6.1–6.19, and their attached assertions. This records **statements present in the current sources**, not successful compilation, permitted-axiom audits, final module integration, or a clean-slate gate. Consult the aggregate evidence and coverage ledger for validation state.

Source paths below are relative to `formalize-everything/books/rudin-real-and-complex-analysis/`. **Unqualified declaration names in the tables have the exact namespace prefix `RudinRCA.Chapter06.`** Names in other namespaces are written in full. Section names such as `FiniteRMK` do not enter declaration names.

## Numbered-node map

| Node | Main and attached assertion | Public declarations | Source |
|---|---|---|---|
| **6.1** | Complex-measure countable additivity and absolute convergence | `complexMeasure_hasSum`; `complexMeasure_summable_norm` | `RudinRCA/Chapter06.lean` |
| 6.1 | Countable measurable partitions; total variation is the printed partition supremum | `CountablePartition`; `totalVariation`; `variation_eq_iSup_countablePartitions` | `RudinRCA/Chapter06.lean` |
| 6.1 | Domination, least dominating positive measure, and agreement with positive measures | `enorm_le_totalVariation`; `totalVariation_minimal`; `variation_positive`; `variation_positive_extended` | `RudinRCA/Chapter06.lean` |
| **6.2** | Total variation is a positive measure, including empty-set and countable-additivity laws | `totalVariation` has codomain `Measure X`; `totalVariation_empty`; `totalVariation_iUnion` | `RudinRCA/Chapter06.lean` |
| **6.3** | Finite subset estimate with exact constant `1 / π` | `RCA63.exists_subset_sum_norm` | `Scratch63.lean` |
| **6.4** | Every complex measure has finite total variation | `complex_variation_univ_lt_top`; `complexVariationFinite` | `RudinRCA/Chapter06.lean` |
| **6.5** | Setwise addition/scalar multiplication, complex vector-space structure, and total-variation norm | `complexMeasure_add_apply`; `complexMeasure_smul_apply`; `complexMeasureNorm`; `complexMeasureNormedAddCommGroup`; `complexMeasureNormedSpace`; `complex_norm_eq_variation` | `RudinRCA/Chapter06.lean` |
| 6.5 | Every set value is bounded by the total-variation norm | `complex_measure_norm_le` | `RudinRCA/Chapter06.lean` |
| **6.6** | Positive/negative variations are finite positive measures | `positiveVariation`; `negativeVariation`; `positiveVariationFinite`; `negativeVariationFinite` | `RudinRCA/Chapter06.lean` |
| 6.6 | Jordan sum/difference identities and the half-sum/half-difference formulas | `positive_add_negative_variation`; `positive_sub_negative_variation`; `positiveVariation_real_eq`; `negativeVariation_real_eq` | `RudinRCA/Chapter06.lean` |
| **6.7** | Absolute continuity is the measurable null-set condition; concentration is equivalent to intersection restriction; singularity is concentration on disjoint measurable sets | `absolutelyContinuous_iff_null_sets`; `ConcentratedOn`; `concentratedOn_iff_inter`; `mutuallySingular_iff_concentrated` | `RudinRCA/Chapter06.lean` |
| **6.8(a)** | Concentration passes to variation | `variation_concentratedOn` | `RudinRCA/Chapter06.lean` |
| 6.8(b) | Singularity passes to variation | `variations_mutuallySingular` | `RudinRCA/Chapter06.lean` |
| 6.8(c) | Addition preserves singularity to a fixed positive measure | `singular_add` | `RudinRCA/Chapter06.lean` |
| 6.8(d) | Addition preserves absolute continuity | `absolutelyContinuous_add` | `RudinRCA/Chapter06.lean` |
| 6.8(e) | Absolute continuity passes to variation | `variation_absolutelyContinuous` | `RudinRCA/Chapter06.lean` |
| 6.8(f) | An absolutely continuous measure and a singular measure are mutually singular | `mutuallySingular_of_ac_of_singular` | `RudinRCA/Chapter06.lean` |
| 6.8(g) | A measure both absolutely continuous and singular is zero | `eq_zero_of_ac_of_singular` | `RudinRCA/Chapter06.lean` |
| **6.9** | Measurable integrable weight, strictly between zero and one at every point | `lemma_6_9` | `Scratch69.lean` |
| 6.9 attached | Equivalent finite positive measure with exactly the original null sets | `lemma_6_9_equivalent_finite_measure` | `Scratch69.lean` |
| **6.10(a)** | Unique complex absolutely-continuous/singular decomposition | `theorem_6_10_lebesgue` | `Scratch69.lean` |
| 6.10(a), positive clause | For finite positive input, both components are finite positive measures and the pair is unique | `theorem_6_10_positive` | `Scratch69.lean` |
| 6.10(b) | Measurable L¹ density representing the absolutely continuous part; uniqueness a.e. | `theorem_6_10_radon_nikodym` applied to the first component from `theorem_6_10_lebesgue` | `Scratch69.lean` |
| 6.10 attached | Sigma-finite positive extension, unique singular component/density, and local integrability | `RCA610Discussion.sigmaFinite_positive_decomposition` | `Scratch610Discussion.lean` |
| 6.10 attached | Common increasing measurable exhaustion, finite for both positive measures, with density integrable on each member | `RCA610Discussion.sigmaFinite_positive_decomposition_with_exhaustion` | `Scratch610Exhaustion.lean` |
| 6.10 attached | Global integrability can fail: density one for counting measure on the natural numbers | `RCA610Discussion.sigmaFinite_density_need_not_be_integrable` | `Scratch610Discussion.lean` |
| 6.10 attached | On the completed Lebesgue space `(0,1)`: counting measure has no positive Lebesgue decomposition; Lebesgue measure is absolutely continuous with respect to counting measure but has no density, including no integrable complex density | `RCA610Discussion.openInterval_counterexamples`; `RCA610Discussion.completedOpenUnitInterval_count_not_sigmaFinite` | `Scratch610Discussion.lean` |
| **6.11** | Real epsilon/delta characterization of absolute continuity, with no sigma-finiteness hypothesis | `theorem_6_11` | `Scratch69.lean` |
| 6.11 attached | Reciprocal-density counterexample on completed Lebesgue `(0,1)`: absolute continuity but infinite mass on arbitrarily small sets | `RCA611Completed.completedInverseDensity`; `RCA611Completed.completedInverseDensity_absolutelyContinuous`; `RCA611Completed.completedInverseDensity_Ioo`; `RCA611Completed.completedInverseDensity_fails_uniform_absoluteContinuity` | `Scratch611Completed.lean` |
| **6.12** | Measurable polar density of modulus one everywhere, with exact complex-measure reconstruction | `theorem_6_12` | `Scratch69.lean` |
| **6.13** | Variation of an integrable complex density, as a measure identity and on every measurable set | `theorem_6_13`; `theorem_6_13_apply` | `Scratch69.lean` |
| **6.14** | Hahn partition and the positive/negative variation restriction identities | `theorem_6_14` | `Scratch69.lean` |
| 6.14 attached | Explicit nonnegative/nonpositive values on every measurable subset of the corresponding partition member | `theorem_6_14_signs` | `Scratch614Signs.lean` |
| 6.14 corollary | Minimality of the Jordan positive/negative parts among positive difference representations | `theorem_6_14_minimal` | `Scratch69.lean` |
| **6.15** | The unconjugated integral pairing is a bounded complex-linear functional, with the Hölder norm upper bound, for all conjugate exponents | `theorem_6_15` | `Scratch69.lean` |
| 6.15 attached | Representation, uniqueness and exact norm for arbitrary positive measures when `1 < p < ∞` | `theorem_6_15_duality_arbitrary_measure` | `Scratch615General.lean` |
| 6.15 attached | The affirmative `p = 1` assertion under sigma finiteness | `theorem_6_16` specialized to `p = 1`, `q = ∞` | `Scratch616I.lean` |
| 6.15 attached | A bounded complex functional on Lebesgue `L∞([0,1])` that has no L¹ density | `theorem_6_15_infinity_not_representable` | `Scratch615Infinity.lean` |
| **6.16** | Sigma-finite `1 ≤ p < ∞` dual representation, uniqueness in Lq and exact norm, using the product `f g` | `theorem_6_16` | `Scratch616I.lean` |
| 6.16 attached | Complex linear isometric equivalence between Lq and the dual of Lp, with its integral formula | `theorem_6_16_linearIsometryEquiv`; `theorem_6_16_linearIsometryEquiv_apply` | `Scratch616J.lean` |
| **6.17** | Hilbert `p = q = 2` specialization, uniqueness/exact norm, with explicit conjugation bridge to the book's `f g` convention | `hilbert_lp_duality` | `RudinRCA/Chapter06.lean` |
| **6.18** | Compactly supported subspace of C₀ with inherited supremum norm; cutoff density; unique norm-preserving extension | `RCA618.compactSupportSubmodule`; `RCA618.exists_compactSupport_approx`; `RCA618.dense_compactSupport`; `RCA618.exists_unique_extension` | `Scratch618Extension.lean` |
| 6.18 | Complex integral and identification with the polar-density integral | `complexIntegral`; `vectorIntegral_eq_polar` | `Scratch69.lean`; `Scratch618Polar.lean` |
| 6.18 | Indicator identity; additivity in the measure for bounded measurable functions; total-variation bound | `theorem_6_18_indicator`; `theorem_6_18_add`; `theorem_6_18_bound` | `Scratch69.lean` |
| 6.18 | Regular complex Borel measure means regular total variation | `IsRegularComplexMeasure` | `Scratch618Final.lean` |
| 6.18 | Integration is a bounded complex-linear functional on C₀, with norm at most total variation mass | `theorem_6_18_functional` | `Scratch618Final.lean` |
| **6.19** | Existence of a regular complex Borel representing measure on every LCH space; representation on all C₀; exact norm; uniqueness among regular complex measures | `theorem_6_19` | `Scratch619Assembly.lean` |
| 6.19, separately exposed conclusions | Exact norm and uniqueness of a regular representing measure | `theorem_6_19_norm`; `theorem_6_19_zero`; `theorem_6_19_unique` | `Scratch619Uniqueness.lean` |

## Bridges and integration dependencies

These declarations explain the representations above; they are not extra numbered nodes.

| Purpose | Public declarations | Source |
|---|---|---|
| Exact completed-open-interval model for the 6.10/6.11 examples | `RCA610Discussion.openIntervalVolume`; `RCA610Discussion.CompletedOpenUnitInterval`; `RCA610Discussion.openIntervalLebesgue`; `RCA610Discussion.openIntervalLebesgue_apply`; `RCA610Discussion.completedOpenUnitInterval_measurable_iff`; `RCA610Discussion.openIntervalLebesgue_isComplete`; `RCA610Discussion.openIntervalLebesgue_isProbabilityMeasure`; `RCA610Discussion.openIntervalLebesgue_nullSingletonClass` | `Scratch610Discussion.lean` |
| Generic counting obstructions supporting the exact example | `RCA610Discussion.absolutelyContinuous_count`; `RCA610Discussion.count_no_decomposition`; `RCA610Discussion.count_no_density`; `RCA610Discussion.count_no_complex_density` | `Scratch610Discussion.lean` |
| Transfer of the inverse-density computation to the completed interval | `RCA611Completed.measurable_interval_val`; `RCA611Completed.interval_val_measurePreserving`; `RCA611Completed.completedInverseDensity_preimage` | `Scratch611Completed.lean` |
| Ambient Borel inverse-density computation used by that transfer | `unitIntervalMeasure`; `inverseDensityMeasure`; `inverseDensity_absolutelyContinuous`; `inverseDensity_Ioo`; `inverseDensity_fails_uniform_absoluteContinuity` | `Scratch611Example.lean` |
| Arbitrary-measure duality through sigma-finite support | `lpFunctional_exists_sigmaFinite_norm_support`; `lp_integral_pairing_unique_finite_exponent`; `lp_ae_zero_compl_of_norm_le_restrict` | `Scratch615GeneralSupport.lean` |
| Finite-measure Lp duality and sigma-finite assembly | `theorem_6_16_finite`; `sigmaFinite_glue_densities`; `lpZeroExtend`; `lpFunctionalOnRestriction`; `lpFunctional_eq_of_finite_indicator` | `Scratch616E.lean`; `Scratch616G.lean`; `Scratch616F.lean`; `Scratch616H.lean` respectively |
| Linear isometry underlying the isometric equivalence | `lpDualityLinearIsometry`; `lpDualityLinearIsometry_apply`; `lpDualityLinearIsometry_surjective` | `Scratch616J.lean` |
| Polar construction of the C₀ functional | `theorem_6_18_polar_functional` | `Scratch69.lean` |
| Real positive-part decomposition and finite RMK measures for arbitrary LCH spaces | `RCA619PositivePart.exists_positive_decomposition`; `RCA619PositivePart.rieszMeasure_univ_le`; `RCA619PositivePart.rieszMeasure_isFiniteMeasure`; `RCA619PositivePart.exists_finite_measure_representation`; `RCA619PositivePart.exists_signed_representation` | `Scratch619PositivePart.lean` |
| Regularity preserved under finite domination, sums and complex differences | `regular_of_le_finite_regular`; `regular_add_finite`; `complex_variation_sub_regular` | `Scratch619Regular.lean` |
| LCH approximation without an added normality assumption | `lch_exists_continuous_eLpNorm_sub_le_of_compact`; `lch_memLp_exists_hasCompactSupport_eLpNorm_sub_le`; `lch_integrable_exists_hasCompactSupport_integral_sub_le` | `Scratch619Density.lean` |
| Unit-bounded compactly supported approximants for norm identification | `unitClip`; `continuous_unitClip`; `norm_unitClip_le`; `unitClip_eq_self`; `unitClip_error_le`; `exists_unitBounded_compactSupport_approx` | `Scratch619Clip.lean` |
| Assembly from four finite positive measures and real/imaginary functionals | `unitComplexMeasure`; `unitComplexMeasure_variation`; `unitComplexMeasure_integral`; `realCcToComplexC0`; `realCcToComplexC0_norm_le` | `Scratch619Assembly.lean` |

## Fidelity and integration notes

- `Scratch61.lean`, `Scratch64.lean` and `Scratch617.lean` contain development copies of declarations already present in `RudinRCA/Chapter06.lean`. Their bodies must not be included a second time during integration. The table points to the integrated copy.
- The 6.7–6.8 statements use general vector-measure codomains, including complex/signed measures and arbitrary positive measures through the ENNReal vector-measure encoding. Positive references need not be sigma finite.
- The 6.10 RN statement applies to an absolutely continuous complex measure; applying it to the AC component of the separately unique decomposition is the full numbered theorem. The sigma-finite positive extension also exposes a.e. density uniqueness, and the separate exhaustion wrapper displays its local-integrability consequence.
- `RCA610Discussion.unitInterval_counterexamples` and `RCA610Discussion.unitInterval_count_not_sigmaFinite` are additional **closed** interval variants. They do not replace the printed completed-open-interval examples in the map above.
- The finite-positive hypotheses in `theorem_6_14_minimal` encode ordinary finite real subtraction: a finite signed measure equal to a difference of positive measures requires both total masses finite for that subtraction to be defined and finite. No use of `ENNReal.toReal ∞ = 0` is intended to simulate subtraction.
- The 6.15 negative endpoint assertion is a Lebesgue example, not just an arbitrary counting-measure counterexample. The exercise's stronger annihilator construction is not part of this node's statement. The general `1 < p < ∞` theorem is separate from 6.16's sigma-finite theorem.
- The 6.17 dependency explanation is mathematical exposition in the source documentation; no proposition can assert that the present imported proof implementation follows Rudin's exact historical proof order.
- The 6.18 compact-support submodule is the same space of compactly supported continuous functions with inherited sup norm. The polar-integral bridge is stated on `Integrable f c.variation`, which includes all bounded measurable tests because 6.4 supplies finite variation.
- The final 6.19 declaration retains only the LCH, Hausdorff and Borel-space assumptions. Its real/imaginary positive decomposition, regularity and density helpers are proof infrastructure, not substitutions of positive-only or second-countable representation theorems.

All nineteen node numbers occur above. Repeated rows describe subclauses and attached assertions; they do not increase the printed-node count.
