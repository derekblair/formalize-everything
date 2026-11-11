# Cluster B: printed-text scope and disclosures

Authority: [issue 38](https://github.com/derekblair/formalize-everything/issues/38),
under [umbrella 36](https://github.com/derekblair/formalize-everything/issues/36).

Source: Walter Rudin, *Real and Complex Analysis*, third edition, Chapters 4–5,
printed pp. 76–115 (including the exercise pages, which are excluded).
The chapter scan is hosted by
[Università Roma Tre](https://www.mat.uniroma3.it/users/chierchia/VARIE/rdin_re-com-an-4-5.pdf).
The numbered main-text nodes are **4.1–4.26 (26)** and **5.1–5.25 (25)**.
These counts come from a new enumeration of the printed text; no earlier
research-lane inventory was present or used.

## Statement conventions and corrections

- Inner products in this book are complex-linear in the first argument.
  `rudinInner x y := inner ℂ y x` preserves that convention. Using Mathlib's
  inner product without reversing its arguments would change the assertions.
- **4.2:** the printed inequality assumes only the semidefinite axioms,
  not positive definiteness. The formal `schwarz` statement deliberately uses
  `SeminormedAddCommGroup`. The additional `schwarz_from_axioms` and
  `triangle_from_axioms` statements derive both inequalities directly from
  `PreInnerProductSpace.Core`, without assuming a preexisting norm or triangle inequality.
- **4.7:** closure under addition and scalar multiplication alone also holds
  for the empty set, which is not a vector subspace. The formal corrected
  criterion adds nonemptiness. `empty_set_not_subspace` proves the counterexample;
  `subspace_criterion` proves the corrected equivalence. This is disclosed
  explicitly rather than silently inserting a premise.
  The same paragraph's bounded-by-one non-example requires a nonempty domain:
  for the empty domain every function is the zero function. The formal
  `unit_bounded_not_subspace` states that necessary condition explicitly.
- **4.20:** the printed claim that all finite-radius open discs about the origin
  form a maximal chain of open subsets of the plane needs a correction:
  the whole plane can be added to that chain. `originDiscChain_extend_by_univ`
  and `originDiscChain_not_maximal` prove the counterexample; the printed
  maximality assertion is explicitly rejected, not treated as proved.
- **4.24:** `trigonometricSystem_complete` (`RudinRCA/Chapter04.lean:1373-1375`)
  establishes trigonometric completeness in `L²(T)` via Mathlib's
  `span_fourierLp_closure_eq_top`, not by reconstructing Rudin's specific
  polynomial-kernel proof (`Q_k(t) = c_k((1+cos t)/2)^k`). As recorded in
  [CHAPTER04-COVERAGE.md](CHAPTER04-COVERAGE.md) and [CLAIMS-B.md](CLAIMS-B.md),
  `Q_k` is a proof route to the density and 4.25 uniform-approximation
  endpoints rather than an additional claimed theorem.
- **5.11:** `lebesgueConstant_printed_lower` proves Rudin's p.102 strict
  estimate `(4/pi^2) * H_n < lebesgueConstant n`. The normalized measure is
  exactly `dt/(2*pi)` on `[-pi,pi]`, and `dirichletKernel n` uses frequencies
  `-n,...,n`. The formal sum over `range n` of `1/(k+1)` is H_n; there is no
  index shift. The proof also covers n = 0. The original
  `lebesgueConstant_harmonic_lower` remains unchanged and gives only the weaker
  nonstrict `(1/(2*pi)) * H_(n+1)` bound. It alone did not cover the printed
  quantitative assertion; F1 is closed by the new strict theorem, with
  [normalization/provenance](evidence/f1-normalization.md) and
  [build/axiom evidence](evidence/f1-gates.md).
- **5.7 / 5.13:** nonemptiness is needed for the corresponding nonmeagreness /
  uncountability conclusions. Empty spaces are admitted in Lean.
  `complete_space_not_first_category` and `countable_dense_not_gdelta` prove
  the corrected nonempty statements; `empty_complete_space_first_category`
  and `empty_countable_dense_gdelta` prove the empty-space counterexamples.
  The generic category definitions and countable-set meagreness statement
  do not assume completeness. The attached perfect-subset conclusion retains
  complete-metric generality without separability or local compactness.
- The ticket's headline mentions closed graph consequences, but the closed graph
  theorem is Exercise 16 of Chapter 5, outside the numbered-body v1 scope.
  No exercise is silently added to or counted in the 51-node body inventory.

## Current completion policy

All assertions within each numbered item, including examples and unnumbered
corollaries attached to it, must be accounted for before the item is marked
complete. Imported Mathlib results may discharge assertions when they have the
same hypotheses and conclusions. A partial family does not count as a completed
node. Build and audit evidence are recorded in the lane STATUS.md / REPORT.md.
