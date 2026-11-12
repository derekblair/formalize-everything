# Cluster F Stage 2 status

Last check: 2026-10-29 18:40 UTC; committed Chapter 13 and umbrella build exit 0 (48 allowed-axiom audits). First aggregate completed with errors; second check covers 25 corrected/new sources.

Authority: derekblair/formalize-everything issues #42 and #36, both read in full.
Branch: `rca-f-stage2-proton`, fresh clone of main at `e1ba718834930c62c75331aa4cd8c6626ce3c141`.
Pins required: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

| Chapter | Printed numbered nodes | Fully formalized nodes | Build | Axiom audit |
|---|---:|---:|---|---|
| 13 — Approximation by Rational Functions | 12 (13.1–13.12) | 1 fully implemented (13.12); 0 through chapter clean-slate gate | Expanded Chapter13 + umbrella build exit0; clean-slate check pending | 48 declarations, only permitted axioms |
| 14 — Conformal Mapping | 22 (14.1–14.22) | 0 | Not run | Not run |

Stage 1 inventories have not been supplied. The lane is independently enumerating the printed text and checking the pinned Mathlib. No completion or PR gate is claimed.

Setup: requested SSH clone failed host-key verification; authenticated HTTPS clone succeeded without changing host trust. Lean v4.34.1 was already present. `lake exe cache get` completed; evidence: `evidence/cache-get.log`. Independent chapter inventories and pinned-library claims check are complete.

Cache fetch completed: 8,907 cached files decompressed; exit 0 (`evidence/cache-get.log`). Baseline skeleton build exit 0 (`evidence/baseline-build.log`); this is not a chapter-module completion check. All 34 node Mathlib claims checks are recorded in `evidence/mathlib-claims.md` and copied into the branch's `SCOPING-F.md`. No pins changed.

Proof development: topology/infinity chart, bounded removability at infinity, algebraic partial fractions, and entire functions meromorphic at infinity. The host is under heavy shared RAM/swap pressure; new lane Lean invocations use a lane-local `flock` and `-j1` to avoid adding simultaneous compiler pressure. Other lanes are untouched.

First verified Stage 2 assertion: bounded holomorphic exterior function has a finite limit at infinity and an analytic inverse-chart extension. `evidence/InfinityRemovable.check.log` records Lean exit 0 and axiom output `[propext, Classical.choice, Quot.sound]`. Integrated into `RudinRCA/Chapter13.lean` with umbrella import; full module build pending. This discharges one assertion of 13.1, not the entire numbered node.

Further 13.1 assertions verified: positive-radius infinity discs form the neighborhood basis; finite-chart open embedding; compactness and homeomorphism to the sphere; the exact book stereographic coordinates (not just an abstract sphere equivalence); and the strip example's disconnected planar complement versus connected spherical complement. `evidence/sphere-combined-2.log` records successful compilation and only the permitted axioms for all printed audits. Integrated into Chapter13; polynomial principal parts and entire nonpolynomial essential singularities are still being checked.

## Ticket discrepancy (printed source controls chapter scope)

`evidence/inventory-ch13.md` independently inventories printed pp.266–276 from the third edition. Runge is 13.6 (compact version) / 13.9 (open-set version), whereas 13.10 is Mittag-Leffler. 13.12 concerns harmonicity of `log |f|` for zero-free holomorphic `f`. Mergelyan is 20.5, outside Chapters 13–14 and therefore not undertaken here. The nine-way equivalence 13.11 explicitly depends forward on Riemann mapping 14.8.

`evidence/inventory-ch14.md` independently inventories printed pp.278–293: 22 nodes. Riemann mapping 14.8 matches the ticket. The complete cluster contains 34 numbered nodes. Exercises excluded.

## Current proof evidence (2026-10-29 18:03 UTC)

- Opening Chapter13 plus umbrella build: exit 0, `evidence/chapter13-opening-build.log` (not a clean-slate chapter gate).
- Polynomial principal part with exact degree, zero constant term, analytic remainder and finite limit: exit 0, `evidence/InfinityPrincipalPart.check.log`.
- Entire functions meromorphic in the inverse chart are polynomials; entire nonpolynomials therefore have essential singularities at infinity: exit 0, `evidence/infinity-polynomial-check.log`.
- Full printed 13.12 log-modulus harmonicity assertion: exit 0, `evidence/log-modulus-2.log`; not yet counted until expanded module is verified.
- Rational partial fractions (13.2), compact exhaustion including spherical component condition (13.3), and balanced directed-edge cycle decomposition (13.4): complete draft statements and proofs written, final compiler checks pending.
- Combined expanded module: queued under the lane compile lock, `evidence/chapter13-consolidated-build.log`. Heavy shared host memory/swap pressure makes individual Lean runs slow; other lanes/processes remain untouched.

Remaining full nodes: 13.5–13.11 and all 22 nodes of Chapter14; 13.1–13.4 await final integrated validation. No PR or clean-slate gate claimed.

PR gate clarification from the umbrella issue: #36 requires “every numbered node proved” for every chapter/PR. The passing opening module is not a license for a partial Stage2 PR. A normal Stage2 PR awaits all12 Chapter13 nodes plus clean-slate build and audit; no review or merge will be arranged by this lane.

## Latest checkpoint (2026-10-29 18:21 UTC)

The source module compiled successfully in526seconds (`evidence/chapter13-consolidated-build.log`, first line). Its48 declaration audits pass (`evidence/chapter13-consolidated-axioms.json`), with no unexpected axioms. The corresponding source snapshot/hash is `evidence/Chapter13.consolidated.snapshot.lean` / `evidence/chapter13-consolidated-build.metadata.json`; umbrella build exit is not yet claimed. Full 13.12 is now integrated and checked. 13.1 has all main analytic/topological assertions, with inverse-chart isolation equivalence and exact strip component enumeration awaiting the aggregate check.

For performance, ten waiting compiler commands belonging only to this lane were stopped and replaced by one aggregate check of eleven frozen sources. No active compiler or other lane was stopped. Evidence: `evidence/aggregate-waiter-transition.json`; source hashes/line mappings: `evidence/all-pending-sources.json`; combined check log: `evidence/all-pending-check-1.log`. This includes13.2,13.3,13.4,13.8 polynomial obstruction, 13.6 countability/analytic helpers, rectangle Cauchy formula, and several13.11 implications. They remain pending, not counted complete.

Inventory/claims checkpoint committed and pushed as `75211e2` on `rca-f-stage2-proton`. No PR exists; no review or merge requested.

Expanded Chapter13 plus umbrella build now completed successfully (2856jobs), exit0; `evidence/chapter13-consolidated-build.log` and metadata record the result. The aggregate scratch compiler has acquired the lane lock.

## Second compiler batch (2026-10-29 18:40 UTC)

Committed and pushed expanded module: `933712e` (branch `rca-f-stage2-proton`). The source and umbrella both build successfully. The first scratch aggregate exited 1; its exact frozen source, hashes, diagnostics, and result are `evidence/AllPending.check1.snapshot.lean`, `evidence/all-pending-check1-sources.json`, `evidence/all-pending-check-1.log`, and `evidence/all-pending-check1-result.json`. Within that pass, partial fractions (13.2), compact exhaustion (13.3), balanced cycles (13.4), infinity-chart bridges, strip component enumeration, and holomorphic logarithm construction compiled with permitted axioms. They await integrated module validation and do not increase the chapter completion count.

Errors in other sources were corrected or isolated. The second aggregate covers 25 sources, including rational-function witnesses for Runge, explicit conditional approximation assembly, contour continuity and path bridges, grid cover geometry, and further 13.11 implications. Log: `evidence/all-pending-check-2.log`; frozen source map: `evidence/all-pending-sources.json`. The finite contour existence proof remains under development; conditional Runge lemmas are not counted as full 13.6 or 13.7. No clean-slate completion or PR gate claimed.

## Mathematical qualification under review

The literal unrestricted reading of the final necessity sentence in13.8 has a candidate singleton exception: on `K={0}`, every function is represented exactly by the constant rational function `R=f(0)`, with no finite or infinite poles, so an empty allowed-pole set suffices. `evidence/RungeNecessityException.lean` contains the proposed formal counterexample and connected-complement check; compiler verification is pending. The main13.8 obstruction under its disconnected-complement hypothesis remains unaffected. The contextual interpretation of the closing sentence is being independently checked; no false-main-theorem claim is made.

Proof drafts now include full finite Cauchy representation and actual polygonal cycle packaging for13.5, conditional13.6/13.7/13.9/13.10 assemblies, and remaining13.11 paths/primitive constructions. A six-file adaptation of the public Riemann mapping proof is drafted for the explicit13.11(j)→(a) forward dependency and14.8, preserving source attribution; see `evidence/riemann-pr33505-adaptation-notes.md`. These are unverified drafts. No completion count or PR gate changes.

Independent source review (2026-10-29 18:56 UTC): the final13.8 sentence can naturally retain the preceding disconnected-complement premise. The singleton draft is therefore an interpretation check against an unrestricted converse, not a refutation of the context-qualified printed claim. The bounded omitted-component rational obstruction is drafted in `evidence/RationalObstruction.lean`; transfer of the unbounded component by spherical inversion remains under development.
