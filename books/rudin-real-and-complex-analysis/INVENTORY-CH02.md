# Chapter 2 inventory and claims check

Checked 2026-10-27 against the **third edition (1987)**. The [book's
title page, contents and numbered text](https://djvu.online/file/NKmAEzkLVs8Io)
verify the contiguous range **2.1–2.25** (printed pp. 33–57). The
[publisher's contents](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india)
independently identify Chapter 2 as *Positive Borel Measures*; contents
alone do not verify individual theorem numbers. No entry below is inferred
from a contents listing alone, and none has UNVERIFIED numbering.

There are **25 numbered items: 14 theorem/lemma items, 6 definition items,
and 5 exposition/notation/remarks items**. Attached unnumbered corollaries
are tracked under their parent, not counted as invented numbered nodes.
Exercises and the ten internal proof steps of 2.14 are not new nodes.

Claims refer to Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, inspected locally. **U** =
already in Mathlib in usable form; **V** = Mathlib variant/components,
requiring a book-faithful restatement; **M** = missing full statement in
the inspected pinned source. M records a search result, not a proof that
no differently named derivation exists. A Mathlib claim is not a proof
of a `RudinRCA` node. For definition/exposition items the classification
describes the represented concepts and accompanying assertions.

| Node | Kind; page | Content | Claim | Pinned Mathlib evidence / fidelity work |
|---|---|---|---|---|
| 2.1 | Definition; 33 | Vector spaces; linear maps | U | `Module`, `LinearMap`, over `ℂ` (with additive commutative groups). |
| 2.2 | Exposition; 34 | Integration functionals | V | `integral_add`, `integral_smul`, `integralPositiveLinearMap`; collect the complex-valued examples and positivity explicitly. |
| 2.3 | Definitions; 35 | Topological vocabulary | V | `IsClosed`, `closure`, `IsCompact`, `T2Space`, `LocallyCompactSpace`; Rudin's neighborhood is **open**, unlike membership in Mathlib's `nhds` filter. |
| 2.4 | Theorem; 36 | Closed subset compactness | U | `IsCompact.of_isClosed_subset`; attached closure corollary via `closure_mono`. |
| 2.5 | Theorem; 36 | Point–compact separation | U | `IsCompact.separation_of_notMem`; attached corollaries `IsCompact.isClosed`, `IsCompact.inter_left`. |
| 2.6 | Theorem; 37 | Finite intersection principle | U | `IsCompact.elim_finite_subfamily_closed`, plus insertion of one compact member; empty indexing families must also be handled. |
| 2.7 | Theorem; 37 | Compact neighborhood interpolation | U | `exists_open_between_and_isCompact_closure`; LCH implies the regular-space instance. |
| 2.8 | Definition; 37 | Semicontinuity | V | `LowerSemicontinuous`, `UpperSemicontinuous`, `lowerSemicontinuous_iff_isOpen_preimage`; accompanying indicator and supremum/infimum assertions need inclusion, using extended reals for arbitrary suprema. |
| 2.9 | Definition; 38 | Compactly supported functions | U | `tsupport`, `HasCompactSupport`, `CompactlySupportedContinuousMap`; support here means **closure** of the nonzero locus. |
| 2.10 | Theorem; 38 | Compact continuous images | U | `IsCompact.image`; attached compact-range corollary uses `HasCompactSupport` and continuity. |
| 2.11 | Notation; 38 | Compact/open cutoff relations | V | Encode the two relations with all conditions: compact/open set, continuous compact support, values in `[0,1]`, and equality/support containment. |
| 2.12 | Lemma; 39 | Urysohn cutoff | U | `exists_continuousMap_one_of_isCompact_subset_isOpen`; real-valued cutoff embeds in the complex-valued `C_c(X)`. |
| 2.13 | Theorem; 40 | Finite partition of unity | U | `exists_continuous_sum_one_of_isOpen_isCompact`; include compact supports and pointwise bounds. |
| 2.14 | Theorem; 40 | Riesz representation | V | `RealRMK.integral_rieszMeasure`, `RealRMK.regular_rieszMeasure`, `Measure.ext_of_integral_eq_on_compactlySupported`; real positive functional must be related to the book's **complex** functional, and the completed σ-algebra, uniqueness, finiteness and both regularity clauses supplied. |
| 2.15 | Definition; 47 | Borel regularity | V | `borel`, `Measure.OuterRegular`, `Measure.InnerRegular`; **do not identify Rudin's regularity with Mathlib `Measure.Regular` alone**. |
| 2.16 | Definition; 47 | σ-compactness; σ-finiteness | V | `IsSigmaCompact`, `SigmaCompactSpace`, `SigmaFinite`; sets are handled by restriction/subtypes. Also retain the stated implications under 2.14. |
| 2.17 | Theorem; 48 | Regular approximation | V | `MeasurableSet.exists_isOpen_sdiff_lt`, `MeasurableSet.exists_isCompact_sdiff_lt`, `Measure.InnerRegularWRT.of_sigmaFinite`; assemble closed/open approximation and Fσ/Gδ envelopes on the completed space. |
| 2.18 | Theorem; 48 | Automatic Borel regularity | V | `Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` is **pseudometrizable**, unlike the book's LCH space with every open set σ-compact. General book hypotheses still need a proof; the available instance cannot be substituted verbatim. |
| 2.19 | Exposition; 49 | Euclidean cells; dyadic decomposition | V | `EuclideanSpace`, `Real.volume_pi_Ico`, `BoxIntegral.Box`; exact half-open dyadic partition and open-set decomposition must be assembled. |
| 2.20 | Theorem; 50 | Lebesgue measure package | V | `volume`, `Measure.completion`, `Real.volume_pi_Ioo/Ioc/Ico`, Haar uniqueness, `Real.map_linearMap_volume_pi_eq_smul_volume_pi`; package completion, all cell boundary conventions, regularity, translations, uniqueness and linear images. |
| 2.21 | Remarks; 53 | Interval integrals; non-Borel sets | V | `Measure.restrict`, `intervalIntegral.integral_eq_integral_uIoc`, singleton-null lemmas, Riemann/Bochner comparison; the cardinality/non-Borel-subset discussion is not discharged by these APIs. |
| 2.22 | Theorem; 53 | Nonmeasurable subsets | M | Searched `MeasureTheory` and full Mathlib for nonmeasurable-set existence/Vitali sets; no theorem proving that every all-subsets-measurable real set is null was located. Requires a choice/transversal argument, including the attached positive-measure corollary. |
| 2.23 | Exposition; 54 | Determinant scale factor | V | `Real.map_linearMap_volume_pi_eq_smul_volume_pi` and linear-image measure results; retain singular maps and completed-measurable sets. |
| 2.24 | Theorem; 55 | Lusin approximation | M | Searches for Lusin/Luzin and measurable continuous-on approximation found no full compact-support, disagreement-measure and sup-bound theorem. `ContinuousMapDense` proves Lp approximation, which does **not** establish this node. Lusin–Souslin is a different theorem. Attached bounded a.e. approximation corollary remains part of the node. |
| 2.25 | Theorem; 56 | Vitali–Carathéodory bounds | V | `exists_le_lowerSemicontinuous_lintegral_ge`, `exists_upperSemicontinuous_le_lintegral_le`; combine positive/negative parts without adding σ-finiteness. The main real strict-inequality wrappers assume `SigmaFinite μ` and are not the book's statement. |

Claim totals: **U 9, V 14, M 2** (25 items).

The attached corollary obligations are 2.4 (compact closure under inclusion),
2.5(a,b) (closedness and closed intersections), 2.10 (compact range),
2.17 (Fσ plus a null set), 2.22 (nonmeasurable subset), and 2.24 (bounded
continuous a.e. approximation): seven clauses, attached to six numbered nodes.

## Exact overlap and fidelity distinctions

[Hirata's AFP entry](https://isa-afp.org/entries/Riesz_Representation.html),
dated 2024-06-04, explicitly follows pp. 37–47. Its
[`Urysohn_Locally_Compact_Hausdorff`](https://isa-afp.org/browser_info/current/AFP/Riesz_Representation/Urysohn_Locally_Compact_Hausdorff.html)
explicitly identifies Lemma 2.12 and develops the semicontinuity ingredients
of 2.8. Its
[`Riesz_Representation`](https://isa-afp.org/browser_info/current/AFP/Riesz_Representation/Riesz_Representation.html)
contains `Riesz_representation_complex_complete`, matching the central
complex/completed representation content of 2.14, together with real,
Borel and compact specializations. Its
[`Regular_Measure`](https://isa-afp.org/browser_info/current/AFP/Riesz_Representation/Regular_Measure.html)
supplies regularity and tightness infrastructure. This is prior work on
the representation fragment and its prerequisites, **not a numbered-node
formalization of all Chapter 2**, and establishes no prior coverage claim
here for Lebesgue construction (2.20), Lusin (2.24), or Vitali–Carathéodory
(2.25). The supporting partition construction is not treated as an
independently verified AFP theorem 2.13 solely from the page-range claim.

At the pinned Mathlib revision,
[`VitaliCaratheodory.lean`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean)
cites “Theorem 2.24” with bibliography key `rudin2006real`. The actual 1987
third-edition numbering is **2.24 Lusin; 2.25 Vitali–Carathéodory**. This is
a bibliographic discrepancy, not a correction to either mathematical
statement. The file itself explains why its strict form assumes
σ-finiteness. The non-strict component results are the appropriate starting
point for the book's general statement.

Likewise,
[`Regular.lean`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/Measure/Regular.lean)
defines `Measure.Regular` using inner regularity on **open** sets, while
Rudin 2.15 requires it for **every Borel** set. 2.14 deliberately does not
claim the latter in arbitrary LCH spaces. This distinction prevents a
spurious one-line proof of 2.17 or 2.18.

No false printed assertion or corrected mathematical statement was found
during this inventory. The variant gaps above are implementation work,
not permission to add hypotheses.

## Implemented in this branch

`RudinRCA/Chapter02.lean` proves **7 of the 14 theorem/lemma nodes**:
2.4, 2.5, 2.6, 2.7, 2.10, 2.12 and 2.13. Their four attached corollary
clauses (2.4, 2.5(a,b), 2.10) are included. The declarations are
`theorem_2_4`, `theorem_2_5`, `theorem_2_6`, `theorem_2_7`,
`theorem_2_10`, `lemma_2_12`, and `theorem_2_13`, under
`RudinRCA.Chapter02`; corollary names append `_corollary` and, for 2.5,
`_a` or `_b`.

The definition-bearing notation node **2.11** is also implemented by
`IsCutoff`, `CompactCutoff` and `OpenCutoff`; the chained relation is their
conjunction. `ofRealCutoff` supplies the explicit real-to-complex bridge
used in 2.12 and 2.13. Thus **8/25 numbered items are represented fully,
17/25 remain**; the theorem-only count is **7 proved / 7 remaining**.
The other definition/exposition entries remain inventoried, even where
their vocabulary is already present in Mathlib. They are not counted as
completed merely because Mathlib was imported. No measure-theoretic
numbered theorem from 2.14 onward is claimed proved in this module.
