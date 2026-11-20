# Crossed Codex review — FE PR #64: RCA AuditA module-inventory fix

You are the independent crossed reviewer for formalize-everything PR #64
("Fix RCA AuditA module-inventory mismatch: relocate 79 orphan .lean
files"). You did NOT author this change. The author pool is
chatgpt-live (bakkie Codex); you run on chatgpt-proton (dominic Codex).
Your verdict decides whether this PR merges — verify everything from the
artifacts, never from the author's claims alone.

## The change under review

- Branch: `coordinator/fix-rca-audita-inventory`, head `4d386ef60cebf2479c4d8d50ecb101d71205ed93`
- Base: main `3cd1541c5970c0f099cac2c2626be1ba8381c588`
- PR: https://github.com/derekblair/formalize-everything/pull/64 (DRAFT)
- Claim: all 79 orphan `.lean` files in the RCA package tree moved
  byte-for-byte to `research/rudin-real-and-complex-analysis-work/`, and
  `RudinRCA.Chapter08/13/15` added to AuditA `expectedModules` — the only
  content edit. `lake build` exit 0; AuditA passed for 1379 declarations
  across 9 audited modules with axioms exactly
  [propext, Classical.choice, Quot.sound].

## Workdir

You are inside `/root/review-fe-audita-fix`, a fresh clone at the PR head
(verify `git rev-parse HEAD` = `4d386ef...` and `git status` clean before
starting; if it is not, STOP and say so in your report).

## Verify, in order

1. **Head and base.** Confirm merge-base with main is `3cd1541` and the
   diff is exactly 80 files: 79 renames + `RudinRCA/AuditA.lean`.
2. **Byte identity of every move.** For EACH of the 79 renamed files,
   compare SHA-256 of the file at the PR head against its blob at
   `3cd1541` (the old path). Every pair must match. Confirm no content
   was deleted: the archive directory holds exactly those 79 files, no
   symlinks, and no original source path still exists in the package.
3. **The one content edit.** Diff `RudinRCA/AuditA.lean` against base:
   the ONLY change must be the three names added to `expectedModules`.
   Enforcement, axiom allowlist, and all other bytes unchanged. The nine
   other retained Lean files must be byte-identical to their base blobs.
4. **Inventory, independently.** Walk the package tree (excluding
   `.lake`), follow the import graph, and confirm
   DISCOVERED = EXPECTED = AUDITED ∪ {RudinRCA.AuditA}: 10 discovered,
   10 expected, 9 audited, 0 actionable orphans.
5. **Clean-slate build (required — the author's build was warm-cache).**
   In `books/rudin-real-and-complex-analysis`: run `lake exe cache get`
   then `lake build` from a cold state (no pre-existing `.lake` build
   artifacts for this package in your clone). Record exit code, job
   count, the full AuditA output line verbatim, and any error/warning.
   The build must exit 0 and the audit must report exactly the three
   permitted axioms.
6. **Programme bar.** Grep the whole diff for `sorry`, `admit`,
   `native_decide`, `decide!`: zero allowed (comments naming them are
   fine only if no such token is live code). `git diff --check` must
   exit 0.
7. **Scope honesty.** The PR body says Chapter06 import is a follow-up,
   not part of this PR. Confirm Chapter06 is NOT in the audited graph
   at this head and the PR body does not claim otherwise.

## Report

Write your report to `/root/review-fe-audita-fix-report.md` (and leave a
copy at `/root/review-fe-audita-fix/REVIEW-REPORT.md`). End with exactly
one verdict line: `VERDICT: PASS` | `VERDICT: PASS WITH ISSUES` (list
each issue as blocking or non-blocking) | `VERDICT: FAIL` (list each
failure with the exact evidence). Include every hash, count, and build
line you verified — the coordinator re-checks them.

## HARD GATES (standing programme rules — they bind you)

- Review ONLY. No edits to the branch or the clone's tracked files, no
  commits, no push, no PR, no merge, no GitHub comments.
- You NEVER arrange your own review and never review your own work.
- No installs or removals on this machine. No Lean on xavier (not
  applicable — you are on dominic).
- Lean pin 4.34.1 (already installed; `lake --version` confirms).
- If the build fails, report FAIL with the exact error. Do NOT fix it,
  do NOT weaken any statement, do NOT touch AuditA.
- When the report is written, STOP. The coordinator harvests it.
