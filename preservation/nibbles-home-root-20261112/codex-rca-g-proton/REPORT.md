# RCA cluster G Stage 2 report — work in progress

The requested end-to-end formalization is not complete. This file is a live report, not a completion assertion.

Authority: GitHub issue #43 and umbrella #36, captured in `evidence/issue-43.txt` and `evidence/issue-36.txt`.
Fresh clone: `formalize-everything`, branch `rca-g-stage2-proton`, initial main commit `e1ba718834930c62c75331aa4cd8c6626ce3c141`.

| Module | Printed nodes | Verified full nodes | Axiom audit | Clean-slate build | PR |
|---|---:|---:|---|---|---|
| Chapter15 | 27 | 2 in scratch (15.3, 15.4); integrated validation pending | Checked families use only permitted axioms | Pending | None |
| Chapter16 | 22 | 0 | Not started | Not started | None |
| Chapter17 | 26 | 0 | Not started | Not started | None |

Independent node enumeration: `INVENTORY.md`, reproduced as book `SCOPING-G.md`. Mathlib claims research: `MATHLIB-CLAIMS.md`. There was no pre-existing Stage 1 inventory in the clone.

The exact Lean/Mathlib pins are retained. The installed Lean toolchain is v4.34.1. Initial `lake exe cache get` exited 0; see `evidence/cache-initial.log` (8907 cached files decompressed).

The ticket's F. and M. Riesz reference 17.11 is a numbering error: the printed third edition labels that result 17.13. The actual 17.11 boundary-convergence theorem remains in scope. See `INVENTORY.md`, Chapter 17, with printed-page evidence.

No PR has been opened: the brief requires a complete first chapter with clean-slate build and axiom audit first. No reviews have been arranged and no merges performed.

Verified scratch evidence: 15.3 (`evidence/chapter15-15.3-axioms.log`, exact checked source snapshot) and 15.4 (`evidence/uniform-product-first-check.md` plus its log/snapshot/hash). No clean-slate chapter build or complete chapter is claimed.

Inventory correction (2026-10-29): direct inspection of printed p.315 found numbered15.27 Remark before the exercises. Chapter15 has27 nodes and clusterG has75, replacing the initial26/74 count. The remark’s generalized-power minimality/removal assertions are in scope; see `rudin-scan-p315.webp`. Chapter16 end p.332 and Chapter17 end pp.351–352 were visually rechecked; counts22 and26 are confirmed.

Latest combined validation: build2 exit1, one finite-fiber set-equality error;47 of49 family audits had only standard axioms, two dependent failed declarations had `sorryAx` and are rejected. Evidence: `evidence/chapter15-build2.{lean,log,json}`. Source is corrected; integrated15.9/10 remains unverified.

Build3 finished18:49:22UTC with exit1:52 of56 family audits used only standard axioms; four dependent failed declarations are rejected. Three15.9/10 proof sites were corrected. Build4 is running from18:52:17UTC. Exact sources, hashes, actual exits, and logs are `evidence/chapter15-build3.*` and `evidence/chapter15-build4.*`. No completed chapter or successful combined build is claimed.
