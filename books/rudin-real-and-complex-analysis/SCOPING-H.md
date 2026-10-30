# RCA cluster H: independent printed-scope check

Checked 2026-10-29. Independent inventory by the cluster H implementation lane; this is not a programme review.

## Finding

The third-edition printed chapters do not match issue #44's descriptive titles or headline nodes. The chapter numbers are unambiguous in both the publisher's contents and the printed book. This discrepancy must be disclosed before treating either interpretation as the authorized formalization scope.

| Chapter | Printed title | Printed text pages, before exercises | Top-level numbered nodes |
|---|---|---:|---:|
| 18 | Elementary Theory of Banach Algebras | 356–368 | 18.1–18.21: **21** |
| 19 | Holomorphic Fourier Transforms | 371–383 | 19.1–19.11: **11** |
| 20 | Uniform Approximation by Polynomials | 386–394 | 20.1–20.5: **5** |
| Total | | | **37** |

These counts include numbered definitions, examples, setup, and expository passages, not only labelled theorems. Chapter 18 additionally has three locally numbered corollaries attached to 18.4; retain these separately in any coverage matrix. The complete Chapter 19–20 inventory and pinned-Mathlib claims check are in [SCOPING-H-19-20.md](SCOPING-H-19-20.md).

Issue #44 instead calls these chapters Phragmen–Lindelof applications, entire functions, and boundary behavior, with Hadamard and Fatou/Riesz headlines. The original skeleton's PROGRESS.md repeated those titles. Neither represents printed Chapters 18–20 of the verified third edition. Chapter 19 does use Phragmen–Lindelof in its proofs, but that does not resolve the contradictory chapter names or headline scope.

## Source evidence

1. [McGraw Hill publisher contents, explicitly third edition](https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india).
2. [Printed title page and contents scan](https://www.gbv.de/dms/hebis-darmstadt/toc/28104803.pdf).
3. [Full printed third-edition scan](http://downloads.tuxfamily.net/openmathdep/analysis_complex/Real_and_Complex_Analysis-Rudin.pdf). The scan identifies Third Edition, International Edition 1987, ISBN 0-07-054234-1 / ordering ISBN 0-07-100276-6. The file has 430 PDF pages, 6,569,655 bytes, SHA-256 `fde4a952137aaa406ffb1e3e35dfc99a2dada5c51b10d27eed71ad7bfa820358`.
4. [Issue #44](https://github.com/derekblair/formalize-everything/issues/44), compare its Scope and Headline nodes paragraphs.

PDF page numbering: printed page `p` is physical PDF page `p + 13` (one-based). Formula checks used rendered pages where text extraction lost mathematical notation; in particular, physical page 371 confirms the quantitative statement on printed page 358. The copyrighted scan and local extraction are not part of this repository.

## Complete Chapter 18 inventory

The page intervals include discussion/proof belonging to each top-level node. Topic labels below are research paraphrases, not transcribed statements.

| Node | Printed kind | Pages | Mathematical coverage |
|---|---|---:|---|
| 18.1 | Definitions | 356–357 | Complex normed/Banach algebras; unit; inverses; spectrum |
| 18.2 | Exposition | 357 | Algebra, topology, and holomorphy connections |
| 18.3 | Theorem | 357–358 | Neumann expansion and quadratic remainder |
| 18.4 | Theorem | 358 | Invertibility under perturbation; remainder bound |
| 18.5 | Theorem | 359 | Scalarized resolvent holomorphy and decay |
| 18.6 | Theorem | 359 | Spectrum compactness and nonemptiness |
| 18.7 | Theorem | 359–360 | Complex Banach division algebra isometric classification |
| 18.8 | Definition | 360 | Spectral radius |
| 18.9 | Theorem | 360–361 | Spectral-radius limit formula |
| 18.10 | Remarks | 361 | Ambient-algebra spectrum comparison and spectral-radius invariance |
| 18.11 | Example | 361–362 | Circle functions versus disc algebra; coordinate spectra |
| 18.12 | Definition | 362 | Ideals, maximality, homomorphisms, kernels |
| 18.13 | Theorem | 362 | Maximal-ideal existence and closedness |
| 18.14 | Quotient discussion | 362–363 | Quotients; kernels; maximal ideals and quotient fields |
| 18.15 | Quotient-norm discussion | 363–364 | Quotient norm, completeness, Banach algebra structure |
| 18.16 | Setup | 364 | Nonzero multiplicative functionals / characters |
| 18.17 | Theorem, five parts | 364–365 | Characters, maximal ideals, spectra, invertibility, norm bounds |
| 18.18 | Theorem | 365–366 | Finite disc-algebra Bezout identity |
| 18.19 | Exposition with claims | 366 | Disc-algebra maximality; Fourier characterization |
| 18.20 | Theorem | 366–367 | Uniform density after adjoining a negative-Fourier-mode function |
| 18.21 | Theorem | 367–368 | Wiener's reciprocal theorem for absolutely summable Fourier coefficients |

There are **11 labelled top-level theorems**: 18.3, 18.4, 18.5, 18.6, 18.7, 18.9, 18.13, 18.17, 18.18, 18.20, 18.21. The remaining ten top-level nodes still require coverage accounting. There are **three additional local corollaries**, all following 18.4:

| Local node | Pages | Mathematical coverage |
|---|---:|---|
| 18.4 Corollary 1 | 358 | Units form an open set; inversion is a self-homeomorphism |
| 18.4 Corollary 2 | 358 | Derivative of inversion sends h to −x⁻¹hx⁻¹ |
| 18.4 Corollary 3 | 358–359 | Compact spectrum and the norm bound on spectral values |

Exercises begin at printed page 369 and are excluded. The top-level-node count is 21, or 24 coverage rows if the three local corollaries receive separate rows; these are different counting conventions, not a discrepancy.

## Statement fidelity notes for Chapter 18

- Throughout the invertible-elements section: complex Banach algebra, unit of norm one; commutativity is not assumed. From the ideals/homomorphisms section onward, commutativity is explicitly assumed. Do not silently strengthen all earlier statements to commutative algebras.
- 18.3 includes the infinite series formula **and** the estimate `‖(1+x)⁻¹ − 1 + x‖ ≤ ‖x‖²/(1−‖x‖)` under `‖x‖ < 1`.
- The image-verified 18.4 bound is `‖(x+h)⁻¹ − x⁻¹ + x⁻¹hx⁻¹‖ ≤ β²/(α²(α−β))`, where `‖x⁻¹‖ = 1/α` and `β = ‖h‖ < α`. OCR omits this displayed formula.
- 18.7 claims an **isometric** algebra isomorphism, not merely algebraic surjectivity of the scalar map.
- 18.10(b)'s shared-metric setting matters: its spectral-radius statement concerns a subalgebra with the inherited Banach-algebra norm.
- 18.14 and 18.15 are numbered constructions with substantive assertions; classifying them as non-theorems must not drop their field/maximality or completeness content.
- 18.17's five labelled parts should be tracked individually inside its single top-level node. In particular its character functional is initially algebraic; continuity follows from the bound.
- 18.18 assumes no common zero on the **closed** unit disc and produces disc-algebra coefficients for a pointwise Bezout identity. The proof additionally identifies all characters/maximal ideals as evaluations; account for that if proof-level auxiliary claims are within the inventory policy.
- 18.19 records both maximality and the vanishing-negative-Fourier-coefficient characterization; it is not empty prose.
- 18.21's summability and pointwise reciprocal conclusion are essential. A theorem only about continuous nowhere-zero functions being invertible in `C(T)` would not cover it.

Confidence: high for all chapter identities and top-level counts, verified directly against the printed scan and its complete numbered-heading sequence; Chapter 18 formulas noted above were additionally inspected in the rendered page when OCR failed. This file does not claim Stage 2 completion or authorize choosing between the conflicting issue descriptions and chapter numbers.

## Working interpretation

The lane disclosed this mismatch and asked the owner for steering. Pending any
contrary steering, it follows the printed numeric scope 18–20 as required by the
brief's printed-text inventory instruction. This is a disclosed working
interpretation, not an assertion of owner approval or a change to the ticket.
Neither Hadamard factorization nor Fatou/Riesz boundary theory is counted as a
Chapter 18–20 result. No work is assigned to other chapters.
