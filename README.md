# formalize-everything

Lean 4 formalizations of books and other texts — many things, one standard.

The idea: take a text worth trusting — a textbook, a classic paper, a reference work — and rebuild its results in Lean until the kernel itself vouches for them. One book at a time, node by node: every definition, every theorem, in order.

## The standard

A formalization counts only when all of these hold:

- **Zero sorrys.** `lake build` passes end to end.
- **Standard axioms only** — `propext`, `Classical.choice`, `Quot.sound`. No admitted axioms, no `native_decide` trust exceptions smuggled into headline results; any exception is disclosed in the catalogue entry, in plain sight.
- **Statement fidelity.** The Lean statement must faithfully encode the source statement — same hypotheses, same quantifiers, same conclusion. A theorem whose hypotheses are vacuous, or which assumes the hard part, does not count, however cleanly it builds. (This rule is written in the blood of an earlier audit; see the sibling repo [math-proofs](https://github.com/derekblair/math-proofs) deep reviews of October 2026.)
- **Hostile review before "done."** Every chapter/target passes an adversarial review pass — gaps, unstated assumptions, edge cases, counterexample attempts — before it is marked complete here.
- **Copyright discipline.** Theorem statements only, kept brief. Never reproduce a source text's proofs or extended exposition.

Toolchain: Lean 4.34.1 + pinned Mathlib. Never float versions mid-book.

## Layout

Each target gets its own directory and its own Lake project, so books never block each other:

```
books/<slug>/     one book (or text) per directory: lakefile, toolchain, sources
papers/           standalone papers and shorter texts, same pattern
software/         software specifications and correctness proofs, same pattern
CATALOGUE.md      the index: every target, its status, and where it lives
```

## Sibling repos

- [rudin-lean](https://github.com/derekblair/rudin-lean) — Rudin's *Principles of Mathematical Analysis*, the flagship book formalization (Chapters 1–7 complete). It keeps its own repo and history; new books live here.
- [math-proofs](https://github.com/derekblair/math-proofs) — the research program's original results and preprints. Discoveries live there; faithful reconstructions of existing texts live here.

See [CATALOGUE.md](CATALOGUE.md) for what's underway and what's queued.
