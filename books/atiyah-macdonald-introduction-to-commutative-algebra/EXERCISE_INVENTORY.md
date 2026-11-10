# Atiyah-Macdonald: Stage 2 exercise inventory

**Status: DRAFT for independent review. Inventory assembled; no acceptance or formalization claimed.**

Assignment: [formalize-everything #4](https://github.com/derekblair/formalize-everything/issues/4). Author: Cleveland (Bunny). Source verification and inventory date: 2026-11-10.

The [coordinator's source handoff](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6759460063) supplied the authorized private copy and released the Stage 2 source gate. This document continues the same scoping assignment. [Stage 1 PR #65](https://github.com/derekblair/formalize-everything/pull/65) independently passed and was merged under the [coordinator's disposition](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6759663275). This inventory is a new review unit; the earlier PASS does not cover it.

## Source identity and verification

All page references below identify **source S1**, the coordinator-supplied private `AtiyahMacDonald.pdf`. The PDF itself is not included in the repository.

- Title page, PDF page 2: *Introduction to Commutative Algebra*, M. F. Atiyah and I. G. Macdonald, Addison-Wesley Publishing Company. The series is identified on PDF page 1.
- Copyright page, PDF page 3: copyright 1969, Addison-Wesley Publishing Company, Inc.; printed in Great Britain; Library of Congress Catalog Card No. 72-79530.
- The inspected title/copyright pages match the assigned title, authors, publisher, and 1969 work. They do not identify a separate printing number or establish an errata baseline. No other edition was substituted.
- Physical PDF page count: **137**. Byte length: **2,883,599**.
- MD5: `3d724a93438d0241af74b52e1abf0f33`, matching the coordinator's handoff.
- SHA-256: `eb93f14a0c77bc549db18f448b6e9ab856022532f16270e1b88a7bd0d2f1c943`.
- Contents: printed pages v-vi, PDF pages 4-5. In the numbered body, printed page p is physical PDF page p + 9; printed page 1 is PDF page 10.
- The source was read from the supplied local file on bakkie. No source URL was retried and no alternate scan was downloaded. The PDF, extracted source text, and page images are not part of this deliverable.

The title, copyright, and both contents pages were visually inspected. Text extraction was used to enumerate the exercise headings and starting pages. All chapter-ending exercise pages and the detected numbering ambiguities were checked against rendered page images. This verifies the inventory and its references, not statement fidelity of a future formalization.

## Inventory convention

There are **217 numbered exercise units**, in source order. An ID such as **Ex. 3.12** means Exercise 12 in Chapter 3, not Proposition 3.12. Roman-numbered subparts, follow-on questions, hints, and continuations belong to their parent numbered exercise and are not counted separately. Unnumbered introductory text and chapter results are excluded.

Each row records the exercise's **starting** printed page and physical PDF page in S1. Exercises may continue onto later pages. The brief labels are editorial navigation aids, not verbatim titles, full statements, solutions, or proof specifications. A future statement ledger must read every part and preserve its hypotheses; these labels are not a substitute for that work.

## Chapter totals

| Chapter | Title | Numbered exercises | Exercise pages in S1 | PDF pages |
|---|---|---:|---|---|
| 1 | Rings and Ideals | 28 (1-28) | 10-16 | 19-25 |
| 2 | Modules | 28 (1-28) | 31-35 | 40-44 |
| 3 | Rings and Modules of Fractions | 30 (1-30) | 43-49 | 52-58 |
| 4 | Primary Decomposition | 23 (1-23) | 55-58 | 64-67 |
| 5 | Integral Dependence and Valuations | 35 (1-35) | 67-73 | 76-82 |
| 6 | Chain Conditions | 12 (1-12) | 78-79 | 87-88 |
| 7 | Noetherian Rings | 27 (1-27) | 84-88 | 93-97 |
| 8 | Artin Rings | 6 (1-6) | 91-92 | 100-101 |
| 9 | Discrete Valuation Rings and Dedekind Domains | 9 (1-9) | 99 | 108 |
| 10 | Completions | 12 (1-12) | 113-115 | 122-124 |
| 11 | Dimension Theory | 7 (1-7) | 125-126 | 134-135 |
| **Total** | | **217** | | |

The counts follow continuous exercise-number sequences in the 11 exercise blocks, not estimates from contents listings.

## Source reconciliation with Stage 1

The supplied contents pages (S1, printed v-vi / PDF 4-5) corroborate the 36 unnumbered topic headings already reported by the coordinator. They also supply direct source evidence that was unavailable when PR #65 was prepared.

One detail differs from the [November 8 coordinator description](https://github.com/derekblair/formalize-everything/issues/4#issuecomment-6724755965): **Chapter 1 and its topic lines do have printed page numbers** in S1. Chapter 1 starts at 1; its seven topic starts are 1, 2, 2, 3, 5, 6, and 9; its Exercises block starts at 10. The count and order of topics are unchanged. This finding is recorded explicitly here and in the updated scoping report. It was not part of the head independently reviewed for Stage 1.

The earlier report's "source-gated" status describes the state before the November 10 handoff. Source access is now verified for this Stage 2 inventory. Independent review and coordinator acceptance remain separate gates.

## Exercise-by-exercise inventory

### Chapter 1: Rings and Ideals

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 1.1 | 10 | 19 | Units shifted by nilpotents |
| Ex. 1.2 | 10 | 19 | Polynomial units, nilpotents, zero-divisors, and primitive products |
| Ex. 1.3 | 11 | 20 | Several-variable polynomial analogues |
| Ex. 1.4 | 11 | 20 | Radicals of a polynomial ring |
| Ex. 1.5 | 11 | 20 | Formal power series: units, nilpotence, radicals, and ideals |
| Ex. 1.6 | 11 | 20 | Idempotents outside the nilradical |
| Ex. 1.7 | 11 | 20 | Elementwise power identities and maximal primes |
| Ex. 1.8 | 11 | 20 | Existence of minimal prime ideals |
| Ex. 1.9 | 11 | 20 | Radical ideals as intersections of primes |
| Ex. 1.10 | 11 | 20 | Rings with a unique prime ideal |
| Ex. 1.11 | 11 | 20 | Boolean rings and their ideals |
| Ex. 1.12 | 11 | 20 | Idempotents in local rings |
| Ex. 1.13 | 11 | 20 | Artin's algebraic-closure construction |
| Ex. 1.14 | 12 | 21 | Prime ideals inside the zero-divisors |
| Ex. 1.15 | 12 | 21 | Zariski closed sets and the prime spectrum |
| Ex. 1.16 | 12 | 21 | Examples of prime spectra |
| Ex. 1.17 | 12 | 21 | Basic opens and quasi-compactness |
| Ex. 1.18 | 13 | 22 | Point closures and closed points of spectra |
| Ex. 1.19 | 13 | 22 | Irreducibility of the prime spectrum |
| Ex. 1.20 | 13 | 22 | Irreducible components of topological spaces |
| Ex. 1.21 | 13 | 22 | Contravariance and topology of spectral maps |
| Ex. 1.22 | 13 | 22 | Spectrum of a finite product |
| Ex. 1.23 | 14 | 23 | Clopen sets in Boolean spectra |
| Ex. 1.24 | 14 | 23 | Boolean lattices and Boolean rings |
| Ex. 1.25 | 14 | 23 | Stone representation |
| Ex. 1.26 | 14 | 23 | Continuous-function rings and maximal spectra |
| Ex. 1.27 | 15 | 24 | Affine varieties and coordinate rings |
| Ex. 1.28 | 16 | 25 | Regular maps and coordinate-ring homomorphisms |

### Chapter 2: Modules

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 2.1 | 31 | 40 | Coprime cyclic groups and tensor products |
| Ex. 2.2 | 31 | 40 | Tensoring with a quotient ring |
| Ex. 2.3 | 31 | 40 | Vanishing tensor products over local rings |
| Ex. 2.4 | 31 | 40 | Flatness of direct sums |
| Ex. 2.5 | 32 | 41 | Flat polynomial algebras |
| Ex. 2.6 | 32 | 41 | Polynomial modules and scalar extension |
| Ex. 2.7 | 32 | 41 | Extension of prime ideals to polynomials |
| Ex. 2.8 | 32 | 41 | Tensor products and transitivity of flatness |
| Ex. 2.9 | 32 | 41 | Finite generation in exact sequences |
| Ex. 2.10 | 32 | 41 | Surjectivity detected modulo the Jacobson radical |
| Ex. 2.11 | 32 | 41 | Invariant basis number |
| Ex. 2.12 | 32 | 41 | Kernels of surjections onto finite free modules |
| Ex. 2.13 | 32 | 41 | Scalar extension and split embeddings |
| Ex. 2.14 | 32 | 41 | Construction of module direct limits |
| Ex. 2.15 | 33 | 42 | Elements and vanishing in direct limits |
| Ex. 2.16 | 33 | 42 | Universal property of direct limits |
| Ex. 2.17 | 33 | 42 | Directed unions of submodules |
| Ex. 2.18 | 33 | 42 | Morphisms of direct systems |
| Ex. 2.19 | 33 | 42 | Exactness of direct limits |
| Ex. 2.20 | 33 | 42 | Tensor products and direct limits |
| Ex. 2.21 | 34 | 43 | Direct limits of rings |
| Ex. 2.22 | 34 | 43 | Nilradicals and domains under direct limits |
| Ex. 2.23 | 34 | 43 | Infinite tensor products of algebras |
| Ex. 2.24 | 34 | 43 | Flatness characterized by Tor |
| Ex. 2.25 | 34 | 43 | Flatness in short exact sequences |
| Ex. 2.26 | 35 | 44 | Flatness tested using quotient modules |
| Ex. 2.27 | 35 | 44 | Characterizations of absolutely flat rings |
| Ex. 2.28 | 35 | 44 | Examples and consequences of absolute flatness |

### Chapter 3: Rings and Modules of Fractions

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 3.1 | 43 | 52 | Vanishing of finitely generated localizations |
| Ex. 3.2 | 43 | 52 | Localization proof of Nakayama's lemma |
| Ex. 3.3 | 43 | 52 | Successive localizations |
| Ex. 3.4 | 44 | 53 | Localization through a ring homomorphism |
| Ex. 3.5 | 44 | 53 | Local detection of reducedness |
| Ex. 3.6 | 44 | 53 | Maximal multiplicative sets and minimal primes |
| Ex. 3.7 | 44 | 53 | Saturated multiplicative sets |
| Ex. 3.8 | 44 | 53 | Equivalent multiplicative sets for localization |
| Ex. 3.9 | 44 | 53 | Zero-divisors and minimal primes |
| Ex. 3.10 | 44 | 53 | Local characterization of absolute flatness |
| Ex. 3.11 | 44 | 53 | Zero-dimensional spectra and separation properties |
| Ex. 3.12 | 45 | 54 | Torsion submodules |
| Ex. 3.13 | 45 | 54 | Localization and torsion-freeness |
| Ex. 3.14 | 45 | 54 | Vanishing at selected maximal ideals |
| Ex. 3.15 | 45 | 54 | Generating sets of finite free modules |
| Ex. 3.16 | 45 | 54 | Faithful flatness criteria |
| Ex. 3.17 | 46 | 55 | Descent of flatness |
| Ex. 3.18 | 46 | 55 | Surjectivity between local spectra under flatness |
| Ex. 3.19 | 46 | 55 | Support of a module |
| Ex. 3.20 | 46 | 55 | Extension/contraction and spectral maps |
| Ex. 3.21 | 46 | 55 | Spectra of localizations and fibers |
| Ex. 3.22 | 47 | 56 | Local spectra as intersections of neighborhoods |
| Ex. 3.23 | 47 | 56 | Structure presheaf on basic opens |
| Ex. 3.24 | 47 | 56 | Gluing of sections on basic-open covers |
| Ex. 3.25 | 48 | 57 | Spectral images of tensor products |
| Ex. 3.26 | 48 | 57 | Spectral images of algebra direct limits |
| Ex. 3.27 | 48 | 57 | Infinite tensor products and constructible closed sets |
| Ex. 3.28 | 48 | 57 | Constructible topology and clopen basic opens |
| Ex. 3.29 | 49 | 58 | Closed continuous maps in the constructible topology |
| Ex. 3.30 | 49 | 58 | Equality of Zariski and constructible topologies |

### Chapter 4: Primary Decomposition

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 4.1 | 55 | 64 | Primary decomposition and irreducible components |
| Ex. 4.2 | 55 | 64 | Embedded primes of radical ideals |
| Ex. 4.3 | 55 | 64 | Primary ideals in absolutely flat rings |
| Ex. 4.4 | 55 | 64 | A primary ideal not equal to a prime power |
| Ex. 4.5 | 55 | 64 | Explicit primary decomposition with an embedded component |
| Ex. 4.6 | 55 | 64 | Decomposability in continuous-function rings |
| Ex. 4.7 | 55 | 64 | Polynomial extension of ideals |
| Ex. 4.8 | 55 | 64 | Primary powers of coordinate prime ideals |
| Ex. 4.9 | 55 | 64 | Zero-divisors and associated primes |
| Ex. 4.10 | 55 | 64 | Kernels of prime localizations |
| Ex. 4.11 | 56 | 65 | Smallest primary ideals at minimal primes |
| Ex. 4.12 | 56 | 65 | Saturation of ideals |
| Ex. 4.13 | 56 | 65 | Symbolic powers of prime ideals |
| Ex. 4.14 | 56 | 65 | Maximal colon ideals and associated primes |
| Ex. 4.15 | 56 | 65 | Isolated primary components via localization |
| Ex. 4.16 | 56 | 65 | Preservation of decomposability under localization |
| Ex. 4.17 | 56 | 65 | Primary intersections under condition L1 |
| Ex. 4.18 | 57 | 66 | Finite primary decomposition and conditions L1/L2 |
| Ex. 4.19 | 57 | 66 | Prescribing associated primes under an intersection condition |
| Ex. 4.20 | 57 | 66 | Radicals of submodules |
| Ex. 4.21 | 57 | 66 | Primary submodules and module zero-divisors |
| Ex. 4.22 | 58 | 67 | Primary decomposition of submodules |
| Ex. 4.23 | 58 | 67 | Module analogues of primary-decomposition results |

### Chapter 5: Integral Dependence and Valuations

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 5.1 | 67 | 76 | Integral maps induce closed spectral maps |
| Ex. 5.2 | 67 | 76 | Extending maps to algebraically closed fields |
| Ex. 5.3 | 67 | 76 | Base change of integral maps |
| Ex. 5.4 | 67 | 76 | Localization and integrality: counterexample question |
| Ex. 5.5 | 67 | 76 | Units and Jacobson radicals under integral extensions |
| Ex. 5.6 | 67 | 76 | Finite products of integral algebras |
| Ex. 5.7 | 67 | 76 | Multiplicative complements and integral closure |
| Ex. 5.8 | 67 | 76 | Monic factors and integral closure |
| Ex. 5.9 | 68 | 77 | Integral closure and polynomial extension |
| Ex. 5.10 | 68 | 77 | Going-up/down and spectral topology |
| Ex. 5.11 | 68 | 77 | Going-down for flat maps |
| Ex. 5.12 | 68 | 77 | Integrality over finite-group invariants |
| Ex. 5.13 | 68 | 77 | Orbits of primes above invariant subrings |
| Ex. 5.14 | 69 | 78 | Integral closure under finite Galois extensions |
| Ex. 5.15 | 69 | 78 | Finiteness of primes above a fixed prime |
| Ex. 5.16 | 69 | 78 | Noether normalization |
| Ex. 5.17 | 69 | 78 | Nonempty affine varieties and Nullstellensatz |
| Ex. 5.18 | 70 | 79 | Zariski's algebraic-field lemma |
| Ex. 5.19 | 70 | 79 | Deriving the affine nonemptiness result |
| Ex. 5.20 | 70 | 79 | Relative normalization after localization |
| Ex. 5.21 | 70 | 79 | Extending field-valued maps after localization |
| Ex. 5.22 | 70 | 79 | Vanishing Jacobson radicals in finite-type extensions |
| Ex. 5.23 | 71 | 80 | Characterizations of Jacobson rings |
| Ex. 5.24 | 71 | 80 | Closure properties of Jacobson rings |
| Ex. 5.25 | 71 | 80 | Field-algebra criterion for Jacobson rings |
| Ex. 5.26 | 71 | 80 | Very dense subsets and Jacobson spectra |
| Ex. 5.27 | 72 | 81 | Dominating local rings and valuation rings |
| Ex. 5.28 | 72 | 81 | Linearly ordered ideals in valuation rings |
| Ex. 5.29 | 72 | 81 | Overrings of valuation rings |
| Ex. 5.30 | 72 | 81 | Ordered value group of a valuation ring |
| Ex. 5.31 | 72 | 81 | Valuations and their valuation rings |
| Ex. 5.32 | 72 | 81 | Isolated value subgroups and prime ideals |
| Ex. 5.33 | 72 | 81 | Constructing prescribed value groups |
| Ex. 5.34 | 73 | 82 | Closed spectral maps over valuation rings |
| Ex. 5.35 | 73 | 82 | Universal closedness and integrality |

### Chapter 6: Chain Conditions

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 6.1 | 78 | 87 | Injective/surjective endomorphisms under chain conditions |
| Ex. 6.2 | 78 | 87 | Maximal finitely generated submodules |
| Ex. 6.3 | 78 | 87 | Chain conditions for quotient intersections |
| Ex. 6.4 | 78 | 87 | Annihilator quotients of Noetherian modules |
| Ex. 6.5 | 79 | 88 | Noetherian spaces and their subspaces |
| Ex. 6.6 | 79 | 88 | Quasi-compactness criteria for Noetherian spaces |
| Ex. 6.7 | 79 | 88 | Finite irreducible decomposition of Noetherian spaces |
| Ex. 6.8 | 79 | 88 | Noetherian rings and their spectra |
| Ex. 6.9 | 79 | 88 | Finiteness of minimal primes |
| Ex. 6.10 | 79 | 88 | Support of a Noetherian module |
| Ex. 6.11 | 79 | 88 | Going-up and closed spectral maps |
| Ex. 6.12 | 79 | 88 | Ascending chains of primes in Noetherian spectra |

### Chapter 7: Noetherian Rings

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 7.1 | 84 | 93 | Maximal non-finitely-generated ideals |
| Ex. 7.2 | 84 | 93 | Nilpotent formal power series over Noetherian rings |
| Ex. 7.3 | 84 | 93 | Irreducible primary ideals and saturation |
| Ex. 7.4 | 84 | 93 | Noetherianity examples from function rings |
| Ex. 7.5 | 84 | 93 | Finite generation of finite-group invariants |
| Ex. 7.6 | 84 | 93 | Finitely generated fields as rings |
| Ex. 7.7 | 85 | 94 | Finite defining equations for affine varieties |
| Ex. 7.8 | 85 | 94 | Noetherianity descending from polynomial rings |
| Ex. 7.9 | 85 | 94 | A local criterion with finite maximal support |
| Ex. 7.10 | 85 | 94 | Noetherian polynomial modules |
| Ex. 7.11 | 85 | 94 | Limits of local tests for Noetherianity |
| Ex. 7.12 | 85 | 94 | Faithfully flat descent of Noetherianity |
| Ex. 7.13 | 85 | 94 | Noetherian fibers of finite-type spectral maps |
| Ex. 7.14 | 85 | 94 | Strong Nullstellensatz |
| Ex. 7.15 | 86 | 95 | Finite flat modules over Noetherian local rings |
| Ex. 7.16 | 86 | 95 | Local freeness and flatness |
| Ex. 7.17 | 86 | 95 | Primary decomposition of Noetherian modules |
| Ex. 7.18 | 86 | 95 | Associated primes and prime filtrations |
| Ex. 7.19 | 86 | 95 | Uniqueness data for irreducible decompositions |
| Ex. 7.20 | 87 | 96 | Constructible subsets and Boolean operations |
| Ex. 7.21 | 87 | 96 | Constructibility criterion in Noetherian spaces |
| Ex. 7.22 | 87 | 96 | Openness criterion in Noetherian spaces |
| Ex. 7.23 | 87 | 96 | Constructible images under finite-type maps |
| Ex. 7.24 | 87 | 96 | Going-down and open spectral maps |
| Ex. 7.25 | 87 | 96 | Openness of flat finite-type spectral maps |
| Ex. 7.26 | 88 | 97 | Grothendieck groups of finite modules |
| Ex. 7.27 | 88 | 97 | Grothendieck rings of finite flat modules |

### Chapter 8: Artin Rings

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 8.1 | 91 | 100 | Varying embedded primary components via symbolic powers |
| Ex. 8.2 | 92 | 101 | Artinian rings and discrete spectra |
| Ex. 8.3 | 92 | 101 | Finite-type Artinian algebras over fields |
| Ex. 8.4 | 92 | 101 | Finite maps and discrete or finite fibers |
| Ex. 8.5 | 92 | 101 | Finite covering in normalization |
| Ex. 8.6 | 92 | 101 | Lengths of chains of primary ideals |

### Chapter 9: Discrete Valuation Rings and Dedekind Domains

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 9.1 | 99 | 108 | Localization and ideal class groups |
| Ex. 9.2 | 99 | 108 | Gauss's lemma for polynomial contents |
| Ex. 9.3 | 99 | 108 | Noetherian valuation rings and DVRs |
| Ex. 9.4 | 99 | 108 | A DVR criterion using a principal maximal ideal |
| Ex. 9.5 | 99 | 108 | Flatness and torsion-freeness over Dedekind domains |
| Ex. 9.6 | 99 | 108 | Structure of finite torsion modules |
| Ex. 9.7 | 99 | 108 | Two generators for ideals |
| Ex. 9.8 | 99 | 108 | Distributivity of ideal operations |
| Ex. 9.9 | 99 | 108 | Compatible congruences and Chinese remainders |

### Chapter 10: Completions

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 10.1 | 113 | 122 | Failure of right exactness for general completion |
| Ex. 10.2 | 114 | 123 | Inverse-limit exactness and derived limits |
| Ex. 10.3 | 114 | 123 | Krull intersections and support of completion |
| Ex. 10.4 | 114 | 123 | Regular elements and domain questions after completion |
| Ex. 10.5 | 114 | 123 | Successive completions at two ideals |
| Ex. 10.6 | 114 | 123 | Zariski rings and closed maximal ideals |
| Ex. 10.7 | 114 | 123 | Faithful flatness of completion |
| Ex. 10.8 | 115 | 124 | Convergent and formal power series |
| Ex. 10.9 | 115 | 124 | Hensel factor lifting |
| Ex. 10.10 | 115 | 124 | Simple-root lifting and formal implicit functions |
| Ex. 10.11 | 115 | 124 | Failure of converse Noetherianity for completion |
| Ex. 10.12 | 115 | 124 | Faithful flatness of formal power series |

### Chapter 11: Dimension Theory

| Exercise | Printed start page (S1) | PDF start page (S1) | Editorial topic label |
|---|---:|---:|---|
| Ex. 11.1 | 125 | 134 | Hypersurface nonsingularity and regular local rings |
| Ex. 11.2 | 125 | 134 | Complete local rings over power-series subrings |
| Ex. 11.3 | 126 | 135 | Dimension theorem over nonclosed fields |
| Ex. 11.4 | 126 | 135 | Nagata's infinite-dimensional Noetherian domain |
| Ex. 11.5 | 126 | 135 | Hilbert theory in the Grothendieck group |
| Ex. 11.6 | 126 | 135 | Polynomial-ring dimension bounds |
| Ex. 11.7 | 126 | 135 | Polynomial dimension over Noetherian rings |

## Validation and remaining work

Author-side documentation checks:

- Verified the source byte length, 137-page count, MD5 handoff match, and SHA-256.
- Matched all 217 rows to continuous per-chapter sequences, with no missing or duplicate exercise IDs.
- Checked each starting page falls inside its chapter's exercise block and that physical page references differ by nine.
- Visually resolved OCR errors at Ex. 1.5 (S1 printed 11 / PDF 20), Ex. 3.12 (45 / 54), Ex. 10.5 (114 / 123), and Ex. 11.5 (126 / 135). The OCR read some 5s as "S" and Ex. 3.12 as "11"; the inventory follows the printed page images.
- Visually checked every chapter's final exercise page: printed 16, 35, 49, 58, 73, 79, 88, 92, 99, 115, and 126.
- No Lean code, scaffold, build, proof test, dependency change, or exercise solution was created.

Coordinator review should verify the source identity, exercise boundaries and page references, the interpretation of numbered units, and the Stage 1 source reconciliation. The earlier Mathlib audit remains revision-specific and does not become an exercise-by-exercise coverage assessment merely because this inventory exists.

## What this does NOT show

- It does not provide full exercise statements, hints, solutions, or a reproduction of the book.
- It does not count each subpart as a separate exercise or certify every mathematical clause as a formalization target.
- It does not prove any exercise, validate a Lean translation, or assign Mathlib coverage to each exercise.
- It does not establish a particular printing number, an errata baseline, or equivalence with every later edition.
- It does not accept Stage 1 or Stage 2, close #4, reopen retired #5, or authorize implementation.
- It does not constitute independent review. The coordinator appoints the independent reviewer and retains merge control; the author must not review or merge this PR.
