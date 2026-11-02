# F1 printed Dirichlet-kernel bound: gate evidence

`lebesgueConstant_printed_lower` proves `(4/pi^2) * H_n < lebesgueConstant n`,
including the printed n ≥ 1 case. It also holds at n = 0. The formal H_n is
`∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)`; the kernel still uses frequencies
-n through n. Eight new helper theorems supply evenness, half-period
normalization, the lobe integral estimates, and strict positivity of the final
tail. Existing theorems are unchanged. See the [normalization and provenance
record](f1-normalization.md) and [new-family axiom output](f1-new-axioms.log).

All commands ran from `books/rudin-real-and-complex-analysis/`, on Lean
`v4.34.1` and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The base was `653e691f67b3d48afacf3c153d6540f1e58ada9d` on
`f1-printed-bound-main`, with an initially clean working tree.

| Gate | Exact command | Exit | Evidence |
| --- | --- | ---: | --- |
| Pinned cache | `lake exe cache get` | 0 | [cache log](f1-cache.log) |
| Full book build | `LEAN_NUM_THREADS=1 lake build` | 0 | [build log](f1-build.log), 3197 jobs |
| Chapter 4 axiom audit | `python3 evidence/check_axiom_audit.py RudinRCA/Chapter04.lean evidence/f1-build.log` | 0 | [172 declarations / 172 records](f1-Chapter04-axioms.log) |
| Chapter 5 axiom audit | `python3 evidence/check_axiom_audit.py RudinRCA/Chapter05.lean evidence/f1-build.log` | 0 | [182 declarations / 184 records](f1-Chapter05-axioms.log) |
| Proof-token scan, both chapters | Scan for `sorry`, `admit`, `axiom`, `native_decide` | 0 | [zero matches](f1-proof-scan.json) |

Both audits report `Missing records: []`, `Disallowed axioms: {}`, and observed
union `['Classical.choice', 'Quot.sound', 'propext']`. The two extra Chapter 5
records are the existing audited instances. Every theorem and lemma, including
all nine new declarations, has an explicit `#print axioms` record.

Builds were sequential, with `LEAN_NUM_THREADS=1` and the existing project
`weakLeanArgs = ["-j1"]`. A fresh lane `.lake` was populated by the pinned cache.
Chapter 4 compiled during the initial build attempt and was replayed in the
successful full build; Chapter 5 and the book umbrella compiled in the
successful build. Two earlier development builds exited 1 while the new proof
was being completed; their logs remain in the lane workdir and are not gate
passes. Existing unrelated linter warnings are present in the successful log.

Full build log SHA-256: `1c31a5740541a45d8329413789d15ebe6c4847f63fbdb2d893d9033bf33d12a3`.

Chapter05 source SHA-256: `3ac16b5d68358a2a1e7e7609b154bfbe13ffa6ac5a70c17ab17a48ec492d7b4c`.

Cache log SHA-256: `31a59f2c1632616d8bfc588daa8a059bbcdf793634e8fb36b512bb1c99d5344c`.

All source/pin/audit/log hashes and the check timestamp are in [machine-readable metadata](f1-gates.json).

Shared-file scope: only the Chapter 5 row of the `PROGRESS.md` branch-gate table changed. The coordinator owns any reconciliation when sibling PR #49 is rebased; this lane has not changed sibling branches, arranged review, or merged.

Shared-file overlap check: the current PR #49 diff also touches `PROGRESS.md`, changing Chapter 6–7 inventory rows and appending a Cluster C paragraph after the chapter table. This fix changes only the separate Chapter 5 branch-gate row. The overlap is flagged for the coordinator's evening rebase; no sibling merge or rebase was attempted.
