# RCA cluster D — live status

Last check: 2026-10-29T18:48:18Z. Authority: derekblair/formalize-everything issues #40 and #36, read in full.

| Chapter | Numbered nodes | Formalization | Build/audit | State |
|---|---:|---|---|---|
| 8 — Integration on Product Spaces | 18 (8.1–8.18) | All 18 present in the passing integrated module; 2,794 lines, 177 public declarations | Integrated full Lake build exit 0; fresh-cache retrieval exit 0; clean-slate full build running; final audit pending | Source frozen for final gate |
| 9 — Fourier Transforms | 23 (9.1–9.23) | 0/23 | Not started | Printed inventory and pinned-library research prepared; implementation follows Chapter 8 gate |

Cluster count: 41 numbered nodes, excluding exercises. No separately produced Stage 1 inventory was received or assumed. No numeric ticket discrepancy established. The reconstructed inventory and exact statement mapping are in `formalize-everything/books/rudin-real-and-complex-analysis/SCOPING-D.md`; research evidence and local source scan remain in this lane.

## Verified evidence

- `evidence/ch08-integrated-build1.log` and receipt: full build exit 0 at 2026-10-29T18:32:10Z, 2838 jobs, freshly compiled Chapter08 and umbrella. Source SHA-256 `90c3978cf0d53e1093c674e9283823919d134a759c0248a11f6893c1e056ddb3`.
- `evidence/ch08-clean-state.json`: entire old `.lake` renamed to `evidence/lake-before-clean-ch08`; original path confirmed absent. No removal.
- `evidence/ch08-clean-cache-get.log` and receipt: fresh pinned checkout/cache retrieval exit 0 at 18:38:01Z, 8907 cached files restored.
- `evidence/ch08-final-build.log`: clean-slate full build currently running, captured with the Chapter08 `.olean` required absent at invocation. Shared memory contention causes heavy paging; only one Lean compiler runs in this lane.
- `evidence/Ch08Audit.lean` and `.names.json`: 177 distinct expected public declarations. Preliminary source scan finds no forbidden proof placeholders or added axioms. Final compiler-backed audit and mechanical gate remain pending.

Pins remain Lean `leanprover/lean4:v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Fresh HTTPS clone on `rca-d-stage2-proton`, base/main `e1ba718834930c62c75331aa4cd8c6626ce3c141` (remote main reconfirmed during final build). No installations or removals performed. No commit, PR, review or merge yet. No all-gates-passed chapter claim before the clean build and full audit finish.

Faithfulness accounting retains completed sigma algebras, the exact interval examples, conditional CH as a hypothesis, extended values/local absolute continuity in layer-cake, and the actual centered ball maximal function. The displayed maximal constant is proved with dimension constant A=5^k, and both limits are included. Chapter 9 normalization is explicitly researched as dx/sqrt(2*pi) with exp(-ixt); its finite-difference and arbitrary-L1 Fourier-series obligations are recorded, with exercises and recalled earlier-chapter results distinguished.

Publication preparation: GitHub connector search confirms no existing PR for `rca-d-stage2-proton`. Local `gh pr list` ultimately returned HTTP 401; native SSH probing stalled and was stopped. A missing GitHub known-host entry was filled in the native `~/.ssh/known_hosts` using the Ed25519 host key and SHA-256 fingerprint published by GitHub over HTTPS. No user credential was copied or exposed. The working GitHub connector is available for publication with the prepared body-file content if native CLI authentication remains unusable.
