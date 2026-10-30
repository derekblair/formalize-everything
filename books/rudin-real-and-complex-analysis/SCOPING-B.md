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
- **5.7 / 5.13:** nonemptiness is needed for the corresponding nonmeagreness /
  uncountability conclusions. Empty spaces are admitted in Lean. These cases
  require explicit corrected statements and counterexamples before certification.
- The ticket's headline mentions closed graph consequences, but the closed graph
  theorem is Exercise 16 of Chapter 5, outside the numbered-body v1 scope.
  No exercise is silently added to or counted in the 51-node body inventory.

## Current completion policy

All assertions within each numbered item, including examples and unnumbered
corollaries attached to it, must be accounted for before the item is marked
complete. Imported Mathlib results may discharge assertions when they have the
same hypotheses and conclusions. A partial family does not count as a completed
node. Build and audit evidence are recorded in the lane STATUS.md / REPORT.md.
