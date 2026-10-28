# Atiyah–Macdonald: partial Stage 1 scoping

**Status: DRAFT / PARTIAL STAGE 1 — not accepted, not complete.**  
Assignment: [formalize-everything #4](https://github.com/derekblair/formalize-everything/issues/4). Author: Cleveland (Bunny). Evidence assessment: 2026-10-28.  
**Stage 1 residual blocker:** complete within-chapter section inventory is UNVERIFIED.  
**Stage 2 pending:** exercise-by-exercise inventory requires an authorized book copy supplied by the coordinator/Derek.  
**Queue hold:** [#5](https://github.com/derekblair/formalize-everything/issues/5) remains behind Stage 1 review.

This report implements the bounded evidence work allowed by the [Stage 1/Stage 2 ruling](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6457673203) and preserves the [section-inventory checkpoint](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6457827716). It is a documentation deliverable only. Independent review and coordinator disposition are still required; a draft PR is not Stage 1 acceptance.

## Completion matrix

| Requirement | Status | Evidence / exact limit |
|---|---|---|
| Bibliographic identification | Supported, with format/printing limits | WorldCat, publisher search-indexed metadata, and CUTN MARC below support the 1969 work. No original printing or authorized source copy was inspected. |
| Introduction and eleven chapters in book order | Supported | CUTN MARC field 505; ordered list below. |
| Complete within-chapter section inventory | **UNVERIFIED — Stage 1 residual blocker** | Accessible catalog evidence stops at chapters. Publisher preview retrieval failed “Cache miss”; Taylor & Francis/publisher direct retrieval returned 403. No section headings have been inferred. |
| Per-chapter Mathlib assessment on bakkie | Completed as a bounded source-level audit | Eleven rows below, pinned commit, exact declarations, and hypotheses. Not exhaustive theorem coverage. |
| Scaffold requirements and candidate dependency pin | Documented, not implemented or tested | Lean 4.34.1; candidate Mathlib commit below. No book Lake project was created. |
| Milestones and effort/risk | Proposed, judgment-based | Representative pilot estimates only; no whole-book completion estimate. |
| Exercise inventory | **Stage 2 pending — source-gated** | Requires coordinator/Derek-supplied authorized text; no alternate copy used. |
| Compilation, axiom audit, formalization, independent acceptance | Not performed | No Lean code, builds, or tests were run for this report. |

## Bibliographic evidence and its limits

The coordinator supplied the following verified bibliographic findings for integration into this report. This author did not independently retrieve the catalogs in this local Mathlib audit.

- [WorldCat, OCLC 7491](https://search.worldcat.org/title/Introduction-to-commutative-algebra/oclc/7491) identifies M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, Reading, Massachusetts, 1969.
- The search-indexed [Routledge publisher listing](https://www.routledge.com/Introduction-To-Commutative-Algebra/Atiyah-MacDonald/p/book/9780429493638) says first edition / copyright 1969. Direct retrieval returned **403**. This is a current electronic-format listing, not inspection of an original 1969 printing.
- [CUTN library MARC record 39898](https://library.cutn.ac.in/cgi-bin/koha/opac-MARCdetail.pl?biblionumber=39898), field **505**, supplies the ordered chapter contents below. Field **260** records the 1969 imprint, but field **020** contains the later-format ISBN **9781138329607**. These fields must not be conflated into evidence that an original printing or a particular physical copy was inspected.

The bibliographic target is therefore the 1969 work, identified as first edition by the publisher’s indexed metadata. The exact authorized source file, printing/reprint, pagination, and errata baseline remain unverified. No ISBN has been promoted to an exact-copy identifier, and no edition substitution is authorized by this report.

### Published chapter inventory

The following order comes from [CUTN MARC field 505](https://library.cutn.ac.in/cgi-bin/koha/opac-MARCdetail.pl?biblionumber=39898). These are chapter titles, not a reconstructed section inventory.

| Order | Published title | Within-chapter section inventory |
|---|---|---|
| Introduction | Introduction | UNVERIFIED |
| 1 | Rings and Ideals | UNVERIFIED |
| 2 | Modules | UNVERIFIED |
| 3 | Rings and Modules of Fractions | UNVERIFIED |
| 4 | Primary Decomposition | UNVERIFIED |
| 5 | Integral Dependence and Valuations | UNVERIFIED |
| 6 | Chain Conditions | UNVERIFIED |
| 7 | Noetherian Rings | UNVERIFIED |
| 8 | Artin Rings | UNVERIFIED |
| 9 | Discrete Valuation Rings and Dedekind Domains | UNVERIFIED |
| 10 | Completions | UNVERIFIED |
| 11 | Dimension Theory | UNVERIFIED |

**What resolves the Stage 1 residual blocker:** a complete, authorized publisher/library table of contents or coordinator-supplied source pages establishing the within-chapter headings and their order; if a chapter has no formal section divisions, evidence of that fact. Catalog snippets cannot establish completeness. The coordinator owns source acquisition under the [split ruling](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6457673203). The earlier failed book URL was not fetched again for this report.

## Local Mathlib evidence baseline

The declaration audit used the existing bakkie checkout at:

```text
~/rudin-lanes/rudin-ch08-complete/rudin/.lake/packages/mathlib
```

Observed Git HEAD was **d13f23b723b8a846827a245b89c10fc7d3f11612**, with no tracked working-tree changes. Its `lean-toolchain` and the containing project both specify **leanprover/lean4:v4.34.1**; the containing `lakefile.toml` and `lake-manifest.json` pin that same Mathlib commit. Four other existing Rudin-lane dependency checkouts were also found at the same revision and toolchain. These are local inspection results, not claims about latest upstream Mathlib.

The main Rudin workshop had a matching manifest but no dependency checkout, so it was not used as a source substitute. The chosen existing checkout supplied the actual declarations. All links below are immutable source links at the inspected commit, with exact file/line anchors. Signatures, namespaces, and surrounding hypotheses were read; similar names alone were not counted. The source files cited by the chapter audit were verified as tracked.

The target repository’s current [README](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/README.md) requires Lean 4.34.1 with pinned Mathlib. At the remote baseline **9d34e88295d55a034455e4158eba66ef396059f5**, `books/` contained only its README, so there was no Atiyah–Macdonald project pin to validate. The audited Mathlib revision is a **candidate future scaffold pin**, not an already adopted dependency or evidence of a successful book build. The local capability descriptor reports 4.35.0 while its instruction file and these project pins say 4.34.1; future authorized execution must select the project pin explicitly. No toolchain was changed or executable invoked.

## Revision-specific coverage matrix

“Present” here means an inspected library statement supports the named topic under its own hypotheses. It does **not** mean all statements of the corresponding book chapter have been matched. The Introduction has no theorem-coverage claim. Risk labels are engineering judgments about the displayed representation/hypothesis differences.

| Chapter | Inspected declarations and immutable file/line evidence | Scope, qualification, and translation risk |
|---|---|---|
| 1. Rings and Ideals | [`Ideal.Quotient.isDomain_iff_prime`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/Quotient/Basic.lean#L94); [`Ideal.Quotient.maximal_ideal_iff_isField_quotient`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/Quotient/Basic.lean#L164); [`Ideal.quotientInfRingEquivPiQuotient`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/Quotient/Operations.lean#L248); [`Ideal.radical_eq_sInf`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/Operations.lean#L934). | Quotient-domain/field characterizations, finite Chinese remainder theorem, and radical as intersection of containing prime ideals have direct statements. CRT requires a finite index type and pairwise coprime ideals. The quotient-domain statement has a two-sided-ideal context, supplied for commutative rings. Preserve proper-ideal and zero-ring cases. Low-to-medium representative-wrapper risk. |
| 2. Modules | [`LinearMap.quotKerEquivRange`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/Isomorphisms.lean#L39); [`Submodule.quotientQuotientEquivQuotient`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/Isomorphisms.lean#L179); [`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Finiteness/Nakayama.lean#L28); [`rTensor_exact`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean#L397). | Isomorphism theorems, a Nakayama form, and tensor right-exactness are present. Nakayama requires finite generation and N ≤ I • N. Tensor exactness requires an exact pair and surjectivity of its second map; it does not assert arbitrary preservation of injections. The exact tensor declaration is root-level, not TensorProduct.rTensor_exact. Low-to-medium risk from quotient representations and finiteness hypotheses. |
| 3. Rings and Modules of Fractions | [`IsLocalization.lift`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Localization/Defs.lean#L488) and [`IsLocalization.lift_unique`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Localization/Defs.lean#L563); [`IsLocalization.orderIsoOfPrime`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Localization/Ideal.lean#L236); [`IsLocalizedModule.map_exact`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Module/LocalizedModule/Exact.lean#L56). | Localization universal property and uniqueness, correspondence with primes disjoint from denominators, and module-localization exactness are present. Medium risk: reconcile concrete Localization S with abstract IsLocalization instances, scalar towers, and differently typed localized-map APIs. |
| 4. Primary Decomposition | [`Submodule.isLasker`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Lasker.lean#L275); [`Submodule.IsMinimalPrimaryDecomposition`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Lasker.lean#L103); [`Submodule.IsMinimalPrimaryDecomposition.image_radical_eq_associated_primes`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Lasker.lean#L128); [`Submodule.IsMinimalPrimaryDecomposition.comap_localized₀_eq_iInf`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Lasker.lean#L198). | Finite primary decomposition is supplied for Noetherian modules. Both uniqueness results are present; their comments identify A–M 4.5 and 4.10. The second identifies intersections selected by a lower set of associated primes, not uniqueness of every embedded component. Medium risk: module-to-ideal specialization and associated-prime conventions. See the qualification below. |
| 5. Integral Dependence and Valuations | [`Algebra.IsIntegral.trans`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean#L502); [`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/GoingUp.lean#L329); [`Ideal.exists_ideal_le_liesOver_of_le`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/GoingDown.lean#L50); [`ValuationRing.iff_isInteger_or_isInteger`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Valuation/ValuationRing.lean#L348). | Integral towers, going-up/down interfaces, and valuation-ring characterization by a fraction-field element or its inverse belonging to the base-ring image are supported. Here IsInteger means membership in that image, not algebraic integrality. Going-down needs its explicit normal-domain/injectivity assumptions; see the instance below. Medium risk from scalar towers and valuation conventions. |
| 6. Chain Conditions | [`monotone_stabilizes_iff_noetherian`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Noetherian/Defs.lean#L156); [`monotone_stabilizes_iff_artinian`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Artinian/Module.lean#L139); [`isFiniteLength_iff_isNoetherian_isArtinian`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/FiniteLength.lean#L73); [`Module.length_eq_add_of_exact`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Length.lean#L170). | Ascending/descending-chain stabilization, finite length iff both chain conditions, and length additivity for a short exact sequence are present. Descending chains use the order dual. Module.length takes values in ℕ∞, so finite natural-number counting needs hypotheses. Composition-series/Jordan–Hölder formulations were not exhaustively audited. Low-to-medium translation risk. |
| 7. Noetherian Rings | [`Polynomial.isNoetherianRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/Basic.lean#L758); [`MvPolynomial.isNoetherianRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/Basic.lean#L934); [`Algebra.FiniteType.isNoetherianRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/FiniteType.lean#L183); [`IsLocalization.isNoetherianRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Localization/Submodule.lean#L82). | Polynomial, finite-type-algebra, and localization closure properties have direct support. The multivariable theorem requires a finite variable type. Finite generation as an algebra, finite generation as a module, and finitely many polynomial variables are distinct requirements. Low direct-wrapper risk; medium risk for source-specific formulations. |
| 8. Artin Rings | [`isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/HopkinsLevitzki.lean#L176); [`IsArtinianRing.isNilpotent_nilradical`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Artinian/Ring.lean#L63); [`IsArtinianRing.isPrime_iff_isMaximal`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Artinian/Module.lean#L549); [`IsArtinianRing.quotNilradicalPowEquivPi`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Artinian/Module.lean#L620). | Strong structure support. The product equivalence directly decomposes the quotient by a nilradical power. A decomposition of R itself needs a nilpotence exponent and quotient-by-zero transport. Local-factor properties and n = 0 need explicit handling. Low-to-medium wrapper risk. |
| 9. Discrete Valuation Rings and Dedekind Domains | [`IsDiscreteValuationRing.TFAE`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean#L210); [`isDedekindDomain_iff_isDiscreteValuationRing_atPrime`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DedekindDomain/Dvr.lean#L129); [`Ideal.uniqueFactorizationMonoid`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean#L431); [`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean#L338). | DVR equivalences, the Dedekind localization criterion, ideal-factorization infrastructure, and uniformizer decomposition are present. The DVR characterization assumes a Noetherian local domain that is not a field. Localizations in the Dedekind criterion are at nonzero primes. Medium risk from field/zero/unit exclusions and turning the generic ideal UFM into a book-facing uniqueness theorem. |
| 10. Completions | [`Ideal.exists_pow_inf_eq_pow_smul`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L388); [`Ideal.Filtration.Stable.of_le`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L367); [`AdicCompletion.map_exact`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Exactness.lean#L184); [`AdicCompletion.isAdicComplete`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Completeness.lean#L184); [`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L328). | Artin–Rees, stable filtrations, finite-module exactness, completeness, and tensor description are present. Exactness requires Noetherian base, finite middle module, and an injective/exact/surjective sequence. Completeness requires I.FG. Noetherianity of the completed ring and preservation of Krull dimension were not located in the scoped search; absence is not established. Medium-to-high chapter risk. |
| 11. Dimension Theory | [`ringKrullDim`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/KrullDimension/Basic.lean#L29); [`Ideal.height_le_card_of_mem_minimalPrimes_span_finset`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean#L239); [`Polynomial.ringKrullDim_of_isNoetherianRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/KrullDimension/Polynomial.lean#L107); [`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/KrullDimension/Regular.lean#L195); [`IsRegularLocalRing.iff_finrank_cotangentSpace`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/RegularLocalRing/Defs.lean#L75). | Prime-chain dimension, height bounds, polynomial dimension, regular-sequence dimension drop, and cotangent characterization are supported. ringKrullDim takes values in WithBot ℕ∞. Graded-module Hilbert polynomials are an explicit TODO; Hilbert–Samuel statements were not located. This is the highest-risk chapter; existing polynomial-coefficient results do not establish its missing bridges. |

### Primary decomposition: what is resolved

The source explicitly documents both uniqueness results in [Lasker.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Lasker.lean#L125). The minimal-decomposition structure records intersection equality, primary components, distinct radical-colon ideals, and irredundancy. The second uniqueness theorem needs a lower set of associated primes and a matching subset of components; arbitrary embedded components are not asserted unique.

The associated-prime definition is module-oriented and uses radical of a colon ideal: [`Submodule.IsAssociatedPrime`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean#L62). The Noetherian equivalence [`Submodule.isAssociatedPrime_iff`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean#L75) removes that radical. Any comparison with an annihilator-based presentation must account for this. Book theorem numbers in Mathlib comments are evidence of the library author’s intended reference, not an independent comparison with the unavailable book text.

### Integral/valuation and dimension conventions

The going-down instance at [IntegralClosure/GoingDown.lean:48](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/IntegralClosure/GoingDown.lean#L48) requires a domain extension, faithful scalar action, integrality, and an integrally closed base. Scalar-tower and injectivity conditions must remain in any specialization.

Mathlib’s [DVR definition](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean#L58) excludes fields; its [Dedekind-domain definition](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/DedekindDomain/Basic.lean#L144) permits dimension at most one and hence fields. The source’s conventions must be reconciled before choosing wrappers. Likewise [`Module.length`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Length.lean#L32) is extended-natural-valued and [`ringKrullDim`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/KrullDimension/Basic.lean#L29) is valued in `WithBot ℕ∞`; finite natural-number formulas need explicit reductions and cannot silently erase degenerate or infinite cases.

### Artin–Rees and completion: what is resolved

[`Ideal.exists_pow_inf_eq_pow_smul`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L388) gives, for Noetherian commutative base ring and finite module, an index k such that the intersection of the nth ideal-power multiple with a submodule is obtained from the kth intersection by multiplication by the (n−k)th power for all n ≥ k. [`Ideal.Filtration.Stable.of_le`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L367) and [`Ideal.Filtration.Stable.inter_right`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L375) provide subordinate/intersection stable-filtration results under those finiteness hypotheses. A blanket assertion that general good-filtration Artin–Rees is missing is unsupported by this revision.

Further inspected anchors:

- [`Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Filtration.lean#L415) supplies Krull intersection with the ideal contained in the Jacobson radical.
- [`AdicCompletion.map_surjective`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Exactness.lean#L72) preserves surjections without the Noetherian/finite-module assumptions needed by the later injection/exactness statements.
- [`AdicCompletion.map_injective`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Exactness.lean#L92) requires Noetherian base and finite codomain. [`AdicCompletion.map_exact`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Exactness.lean#L184) uses a finite middle module and an injective/exact/surjective original sequence; it does not claim exactness for arbitrary modules.
- [`AdicCompletion.flat_of_isNoetherian`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L379) proves flatness of the completed ring as a base-ring module.
- [`AdicCompletion.isLocalRing_of_fg`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/LocalRing.lean#L78) needs a local ring with finitely generated maximal ideal. [`AdicCompletion.residueField_map_bijective`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/LocalRing.lean#L151) preserves the residue-field map under its Noetherian/local hypotheses.

The file [AdicCompletion/Noetherian.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/AdicCompletion/Noetherian.lean#L1) was inspected: its presence does not itself establish that the completed ring is Noetherian. That conclusion and dimension preservation were not located in the bounded search.

### Dimension theory: explicit gap versus search limits

[`Polynomial.hilbertPoly`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L117) and [`Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L173) concern eventual coefficients of a rational power series of the form p/(1−X)^d over characteristic-zero fields. [`Polynomial.existsUnique_hilbertPoly`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L203) proves uniqueness of that eventual coefficient polynomial.

The same file explicitly lists **Hilbert polynomials of finitely generated graded modules over Noetherian rings as TODO** at [line 40](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/HilbertPoly.lean#L40). The displayed polynomial signatures do not assert module-length or degree-equals-Krull-dimension results. No Hilbert–Samuel function/polynomial or the relevant degree/dimension bridge was located by scoped searches. This is an investigation gap, not a proof that no equivalent development exists elsewhere.

The [`IsRegularLocalRing`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/RegularLocalRing/Defs.lean#L51) definition uses equality of maximal-ideal span rank and Krull dimension. Its cotangent characterization does not establish a Hilbert–Samuel characterization. That file also lists localization of regular local rings as a [TODO](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/RegularLocalRing/Defs.lean#L38).

Search scope included all Mathlib for Hilbert–Samuel/HilbertSeries/HilbertFunction names and completion/Noetherian or completion/Krull-dimension co-occurrences, then RingTheory/LinearAlgebra for Hilbert–dimension connections. Search misses remain explicitly non-exhaustive.

## Scaffold requirements — design only

The [repository standard](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/README.md) and [books layout](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/books/README.md) require one independent Lake project per book, an immutable toolchain/dependency choice, chapter-organized sources, a root import module, progress/queue records, statement fidelity, standard axioms, and independent hostile review before “done.” No scaffold files are delivered by this report.

Candidate future layout, subject to the accepted source contract:

```text
books/atiyah-macdonald-introduction-to-commutative-algebra/
  SCOPING.md
  lakefile.toml
  lean-toolchain
  lake-manifest.json
  AtiyahMacdonald.lean
  AtiyahMacdonald/
    Chapter01.lean
    ...
    Chapter11.lean
  PROGRESS.md
  QUEUE.md
```

Requirements:

1. Pin `lean-toolchain` to **leanprover/lean4:v4.34.1**. Candidate Mathlib revision: **d13f23b723b8a846827a245b89c10fc7d3f11612**. Record exact transitive dependency revisions in a generated lock manifest when scaffold work is authorized; do not float versions mid-book.
2. Use `CommRing` as the ordinary ring baseline and add nontriviality/domain/local/Noetherian/finite-generation conditions only when the verified source or specialization requires them. Preserve quotient, scalar-tower, order-dual, and extended-dimension conventions documented above.
3. Maintain a source-to-declaration ledger with verified source location, hypotheses, exact Mathlib declaration or new wrapper, and verification state. Do not populate unknown sections or exercise statements from memory.
4. Keep short source statements only; do not copy proofs or extended exposition, per the [copyright and fidelity requirements](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/README.md).
5. Later implementation acceptance requires end-to-end kernel/build verification, no `sorry`, the repository’s allowed standard axioms, statement-fidelity checking, and independent review. None of those execution gates is satisfied by this document.
6. Add the catalogue entry with edition/scope and a dated landscape check before starting implementation, as required by [books/README.md](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/books/README.md) and [CATALOGUE.md](https://github.com/derekblair/formalize-everything/blob/9d34e88295d55a034455e4158eba66ef396059f5/CATALOGUE.md). This partial scoping document does not assert that an updated landscape search has been completed.

## Proposed milestones and judgment-based effort/risk

The [ticket](https://github.com/derekblair/formalize-everything/issues/4) specifies scaffold plus the first numbered chapter as the first implementation milestone. The grouping below is a proposal, not authorization to start implementation or lift any source hold.

| Milestone | Proposed scope | Evidence-based risk / gate |
|---|---|---|
| S1 | Finish section inventory; revise this partial report; independent Stage 1 review | Complete section-level source evidence is the explicit residual blocker. No acceptance is claimed. |
| M1 | Scaffold plus Chapter 1 | Direct quotient/radical/CRT APIs support a small pilot. Exact book statement ledger and candidate-pin compilation still need validation; no Lean scaffold exists yet. |
| M2 | Chapters 2–4 | Existing module, localization, and primary-decomposition results reduce new-foundation risk; quotient/scalar-tower/associated-prime translations need explicit statement checks. |
| M3 | Chapters 5–9 | Strong direct support; normal-domain, finite-type versus finite-module, order-dual, and DVR/Dedekind convention differences are the major translation risks. |
| M4 | Chapter 10 | Artin–Rees and completion exactness are available under precise hypotheses; completed-ring Noetherianity/dimension links need further investigation. |
| M5 | Chapter 11 | Investigate graded-module/Hilbert–Samuel links before committing to implementation scope. Existing dimension APIs do not close that gap. |
| S2 | Exercise-by-exercise inventory | Separate source-gated stage; authorized book must be supplied. No exercise count, statements, or completion estimate is asserted. |

**Estimates are planning judgments, not measurements or whole-chapter promises.** For representative API/wrapper pilots, Chapter 2 looks like **½–1 focused day**, Chapter 3 **1–2 days**, Chapter 4 **1–3 days**, and Chapter 10 **1–3 days**. Those ranges reflect the specific quotient, localization, lower-set, and finite-module constraints in the linked declarations. Chapter 11 needs a **2–5 day investigation pilot** to settle representations and search for equivalent graded-module/Hilbert–Samuel developments before estimating implementation. Chapters 1 and 5–9 currently support qualitative low-to-medium direct-wrapper risk; a numeric whole-chapter estimate would require an audited statement count.

These estimates exclude source acquisition, full book/section reconciliation, exercise inventory, reviewer time, and any newly discovered mathematics. No sum is offered as a whole-book estimate.

**Provisional decision:** reuse the existing foundational algebra rather than duplicate it. Whether an entire book-ordered formalization adds only an index, or also substantive wrappers/results, is not established by sampled topic support. In particular, the Chapter 11 TODO and the unresolved source-level inventory prevent an “all covered” or “index only” verdict.

## What this does NOT show

- It does not complete Stage 1: within-chapter section inventory remains UNVERIFIED.
- It does not inspect an original printing, establish a particular source copy/ISBN/pagination/errata baseline, or authorize an edition substitution.
- It does not reproduce, verify, count, or formalize the exercises. **Stage 2 pending** remains a source gate.
- It does not match every definition, proposition, theorem, corollary, or example to the unavailable book text. Chapter-topic support is not exact node equivalence or a coverage percentage.
- It does not prove library-wide absence from search misses, or infer textbook coverage from similar names.
- It does not establish that the book is wholly formalized elsewhere, that no such project exists, or that a new landscape check has been completed.
- It does not provide a Lean scaffold, compiled wrappers, end-to-end build, executable/version test, axiom audit, or independent review PASS.
- It does not mark #4 accepted or release #5’s hold. Only the coordinator can disposition the draft under the existing review gates.

## Verification and handoff record

The local audit read applicable machine/project/capability instructions, target-repository README/layout requirements, Git revision/manifests/toolchain text, declaration bodies and surrounding hypotheses, and the named TODOs. It reconciled current issue/PR state; no overlapping #4 scoping PR was found before draft preparation. Existing GitHub issue state, not BOARD/CLAIM/STATUS files, remained the tasking source.

No book URL was retried, no alternate copy was used, and no builds, tests, installs, toolchain changes, Lean invocation, or credentials changes were performed. The only intended repository change is this documentation file. Publication of a draft, if linked on #4, records a reviewable partial deliverable only; it is not proof acceptance or independent review. No self-review or self-merge is permitted.
