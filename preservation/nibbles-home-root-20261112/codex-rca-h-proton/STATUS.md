# RCA cluster H — lane status

Last check: 2026-10-29 18:55 UTC. Work is active; the cluster is not complete.

| Printed chapter | Inventory | Checked coverage | Build state | Last check |
|---|---:|---|---|---|
| 18 — Elementary Theory of Banach Algebras | 21 top-level + 3 local corollaries | 7 development-checked nodes (18.12–17 CLI; 18.21 LSP family); 0 chapter-gated | All remaining mathematical statements have drafts; serial validation in progress | 2026-10-29 18:05 UTC |
| 19 — Holomorphic Fourier Transforms | 11 top-level | 0 | Inventoried; implementation waits for Chapter 18 | 2026-10-29 18:05 UTC |
| 20 — Uniform Approximation by Polynomials | 5 top-level | 0 | Inventoried; implementation waits for Chapter 19 | 2026-10-29 18:05 UTC |

PR: none. No review arranged and no merge performed. No completion or clean-chapter-build claim.

## Reproducible setup

- Fresh clone `formalize-everything/`, base `e1ba718834930c62c75331aa4cd8c6626ce3c141`, branch `rca-h-stage2-proton`.
- SSH clone failed host-key verification; HTTPS clone succeeded without SSH changes.
- Already-installed Lean v4.34.1; Mathlib exact pin `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- `lake exe cache get` exited 0 and decompressed 8,907 cached artifacts (`evidence/cache-get.log`). No installations or removals performed.
- Authority read in full: issue #44 and umbrella #36; snapshots in `evidence/issue-44.txt` and `evidence/issue-36.txt`.
- No Stage 1 lane inventory was supplied. Independent printed inventory: 37 top-level nodes plus 3 local corollaries, in `SCOPE-CHECK.md`, `INVENTORY-19-20.md`, and pinned-source claims map `MATHLIB-CLAIMS.md`.

## Scope discrepancy and disclosed working interpretation

Issue #44, its headline examples, and the skeleton describe Chapters 18–20 as Phragmén–Lindelöf applications / Entire Functions / Boundary Behavior. Printed third-edition Chapters 18–20 instead have the titles in the table above. Verified against publisher contents (https://www.mheducation.co.in/real-and-complex-analysis-9789355326119-india), printed contents (https://www.gbv.de/dms/hebis-darmstadt/toc/28104803.pdf), and full printed scan (source/hash in `SCOPE-CHECK.md`). Local contents evidence is `evidence/source/third-edition-toc.pdf` and `evidence/source/toc-chapters-18-20.png`.

The owner was asked which scope governs. After a reasonable opportunity to reply, the working interpretation was explicitly disclosed: follow printed chapter numbers 18–20 because the brief requires printed enumeration and discrepancy reporting. Silence has not been treated as approval. Hadamard factorization and Fatou/Riesz boundary theory are not claimed as these printed chapters. Adjust if the owner steers otherwise.

## Validation and active work

- **Passed:** `work/Chapter18Ideals.lean`, covering 18.12–17, exit 0; all 35 printed theorem-family axiom audits limited to `propext`, `Classical.choice`, `Quot.sound`. Evidence: `evidence/ch18-ideals-check-04.log`, metadata maintained alongside the check. This is a fragment pass, not a clean chapter gate.
- **Core:** `work/Chapter18Core.lean`, 18.1–10 plus local corollaries. Check3 found two localized elaboration errors, both repaired in source; check4 pending. Previous failed checks do not count as passes.
- **Disc:** `work/Chapter18Disc.lean`, 18.11 and 18.18, with closed boundary algebra and Fourier adapter. Second pass exited 1 (`evidence/disc-check-2.log`); source repairs are ready for combined validation.
- **Wiener:** `work/Chapter18Wiener.lean`, full 18.21. Completed combined LSP `all-02` reports zero errors in this fragment and only permitted axioms for its printed families. Evidence: `evidence/lean-lsp-20261029T183138Z-3834474.v0001.all-02.Chapter18Wiener.diagnostics.txt` and source snapshot/line map. This is development evidence within an overall failing combined check, not a clean CLI chapter build.
- **Fourier characterization:** `work/Chapter18Fejer.lean`, full positive-kernel/Cesàro/dense-Fourier proof, and `work/Chapter18BoundaryCharacterization.lean`, the 18.19 boundary and maximality statements. Awaiting validation.
- **Maximality/density:** `work/Chapter18Maximality.lean`, full 18.20 finite polynomial family approximation. Awaiting validation.

Only one Lean checker runs in this lane (`-j1`) because measured host usage is about 29/30 GiB RAM and essentially all 15 GiB swap. Initial parallel scratch checks were deliberately interrupted and are not passing evidence. After the failed individual disc/Wiener checks were repaired, one persistent built-in Lean LSP worker is checking the combined scratch source `work/Chapter18All.lean` (all seven fragments). Initial combined check `all-01` stopped in setup-file on the nonexistent `Mathlib.Tactic.Omega` import, before checking proofs. That import was removed; every remaining import path was verified against the pinned Mathlib sources. Corrected session `lean-lsp-20261029T183138Z-3834474`, completed check `all-02`, reports 32 errors: Core 2, Ideals 0, Disc 5, Fejer 13, Maximality 7, BoundaryCharacterization 5, Wiener 0. All reported errors have source repairs prepared. Check `all-03` (version 2) is running against their integration. Its current partial result is Core 1, Ideals 0, Disc 1, Fejer 0, Maximality 2; Boundary and Wiener completion remains pending. All four reported errors have prepared fixes. Fejer has printed all 13 family audits with permitted axioms; the pass has not yet reached its completion barrier. Completed diagnostics and mapped per-fragment axiom results are in `evidence/all-02-map.json` and the linked snapshots. Its import header stays fixed so later edits reuse imported dependencies. Driver and assembly scripts are in `work/`; exact snapshots, source hashes, line maps, protocol, diagnostics and axiom outputs are saved under `evidence/`. This is development validation only; the final clean CLI build remains required. No chapter module is integrated or counted at the programme gate until the combined source and axiom audit pass.

Additional source-fidelity finding (research only): the arbitrary-positive-sequence regularization assertion in 19.6 has a candidate counterexample using Mₙ=exp(−n²) and f(x)=exp(ix). The argument and missing-hypothesis limitation are recorded in `INVENTORY-19-20.md` and repository `SCOPING-H-19-20.md`; no Lean counterexample or Chapter19 implementation is claimed yet.
