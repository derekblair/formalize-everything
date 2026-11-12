# Cluster G Stage 2 status

Last check: 2026-10-29T18:57:34.294457+00:00. Authority: issue #43 and umbrella #36.

| Chapter | Printed nodes | Kernel-checked full nodes | Clean-slate module build | State |
|---|---:|---:|---|---|
| 15 — Zeros of Holomorphic Functions | 27 (15.1–15.27) | 2 in checked scratch (15.3, 15.4) | Pending | Build3 exit1: three15.9/10proof sites corrected; build4 running |
| 16 — Analytic Continuation | 22 (16.1–16.22) | 0 | Not started | Follows Chapter15 |
| 17 — Hp-Spaces | 26 (17.1–17.26) | 0 | Not started | Follows Chapter16 |

No chapter is complete. No PR opened, review arranged, or merge performed.

Fresh clone: `formalize-everything`, branch `rca-g-stage2-proton`, original main `e1ba718834930c62c75331aa4cd8c6626ce3c141`. Requested SSH clone failed host-key verification; same GitHub repository cloned over HTTPS using existing gh authentication. Host-key checks were not disabled and credentials were not copied.

Pins retained: installed Lean v4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Initial `lake exe cache get` exited 0 (8907 cached files decompressed); `evidence/cache-initial.log`.

Independent printed inventory: `INVENTORY.md`, mirrored in book `SCOPING-G.md`; no existing Stage1 inventory was assumed. Full count is 75. Chapter15 Mathlib map: `MATHLIB-CLAIMS.md`.

Ticket discrepancy: F. and M. Riesz is **17.13**, printed pp.341–342, not 17.11 as issue43 says. Printed17.11 boundary convergence remains in scope. Book numbering is preserved.

Verified: 15.3 finite-product inequalities (Lean exit0, three standard-axiom audits; `evidence/chapter15-15.3-axioms.log`, exact checked source snapshot). 15.4 exact arbitrary-set uniform-product theorem including zeros and permutations (Lean exit0, six standard-axiom audits; `evidence/uniform-product-first-check.md` and associated snapshot/log/hash/exit).

Current integrated Chapter15 includes these, product definitions,15.5,15.7, and the full15.6 assembly. The combined check finished with exit1 and exactly one simplifier error in15.7, now corrected but not rerun (`evidence/chapter15-integrated-check1.log`, exact source snapshot and JSON exit/hash/timestamps). All other audited declarations, including15.5 and the full15.6 assembly, showed only the permitted axioms. Conservative full-node counts remain at the two independently successful scratch checks until the combined module passes. Three initial holomorphic/order helpers separately passed (`evidence/holomorphic-product-initial-check.md`).

Latest completed combined check: build3 finished18:49:22UTC, actual exit1 (`evidence/chapter15-build3.{lean,log,json}`). All56 audits appeared;52 showed only permitted axioms. Three error sites were confined to new15.9/10 code: a missing exponent argument, a beta-reduction rewrite mismatch, and a reversed equality condition. Four dependent theorem-family audits showed `sorryAx` from failed elaboration and are rejected. All49 previous base families now audit with permitted axioms, including the repaired finite-fiber/zero-enumeration proof. Finite primary products, the majorant-series choice, and origin-zero removal also audited successfully. Corrections are applied to root and draft sources. Build4 started18:52:17UTC,56families, sourceSHA `f37b406d6ee6965b19df0151271dec0168c10292990f7b2cb8ec4301ce421df0`, session60622 (`evidence/chapter15-build4.{lean,log,json}`). No successful combined build yet.

Further unverified drafts: full15.9 entire products,15.10 infinite and finite factorizations plus removal of the origin zero,15.11 sphere charts and normalized boundary-pole products,15.12 pole-data and quotient assembly (depends on15.11),15.17/18 Jensen,15.20 growth,15.21 Blaschke products, 15.22 Nevanlinna definitions/inclusion,15.23 zero restrictions, and15.25/27 span/removal algebra. Actual15.13 principal-part/interpolation construction and15.15 finite-ideal assembly are drafted in dependent stages. Root LogMeansWork develops15.19 including origin correction, angular-null-zero bridge, and the Fatou step; actual radial-limit existence remains under construction. BlaschkeMeansWork contains numerical log-sum limit and finite boundary-modulus helpers for15.24, not its completed infinite theorem. Drafts are not completion evidence.15.11 retains the full sphere scope. No later chapter has been started.

Machine contention: checks use one Lean worker and are serialized in this lane after initial concurrent checks encountered shared-host RAM/swap pressure. No software installed/removed. See `WORKPLAN.md` for current queue and scratch ownership.

Inventory correction (2026-10-29): direct inspection of printed p.315 found numbered15.27 Remark before the exercises. Chapter15 has27 nodes and clusterG has75, replacing the initial26/74 count. The remark’s generalized-power minimality/removal assertions are in scope; see `rudin-scan-p315.webp`. Chapter16 end p.332 and Chapter17 end pp.351–352 were visually rechecked; counts22 and26 are confirmed.

Repair tooling: `lean_lsp_driver.py` and `LSP-NOTES.md` use the installed Lean server with fixed-header incremental diagnostics and an explicit versioned completion barrier. Driver syntax/help checked; no server launched yet. It is a repair aid; actual build/audit/clean-slate gates remain unchanged.
