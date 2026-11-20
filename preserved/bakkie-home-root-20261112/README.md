# Preserved: bakkie home-root work products — 2026-11-12

Preservation-only snapshot. **Do not merge.** This branch exists so the
home-root copies on bakkie could be removed under the never-discard rule
(spec-conformance 2026-11-12 run: 13 home-root violations on bakkie).

Source machine: bakkie (100.90.9.115), user `derekblair`, home root
`/home/derekblair/`. Fetched to desk 2026-11-12 and verified byte-for-byte
against bakkie md5s (see `bakkie-pr56-set.md5`; both review reports match
the md5s recorded on bakkie before removal).

## What is here

- `review-fe-pr56-report.md` — crossed Codex review of FE PR #56
  (head `9e2224e`, branch `texts/sonnet-form`), md5
  `0894641bab6e7d84e9ef4a3ded1cc105`. This report lived ONLY on bakkie;
  the desk had no copy.
- `review-fe-pr56-rereview-report.md` — crossed Codex re-review of FE
  PR #56, verdict PASS, md5 `d26b5476682fd04a83570a20750764a4`. Also
  retained on desk at
  `~/workspace/formalization/review-reports/review-fe-pr56-rereview-report.md`
  (same md5).
- `pr56-evidence.md5` (75 files) and `pr56-rereview-evidence.md5`
  (99 files) — md5 manifests of the two review-evidence directories.
  The full evidence bytes (~85 MB of logs/JSON/screenshots) were NOT
  pushed here; they were moved on bakkie to
  `~/projects/formalize-everything/review-evidence/review-fe-pr56-evidence/`
  and `.../review-fe-pr56-rereview-evidence/` (same filesystem, bytes
  preserved) and attested by these manifests. No password-SFTP path
  exists for bakkie (Tailscale SSH), so a desk fetch of the 85 MB was
  not practical through the RUN channel.
- `audita-fix/` — the three untracked lane reports from
  `~/audita-fix-fe-main` (formalize-everything clone, branch
  `coordinator/fix-rca-audita-inventory` @ `4d386ef`):
  COMPLETION-REPORT.md, FIX-REPORT.md, REPAIR-REPORT.md.
- `rebase-fe-pr58/` — the four untracked lane reports from
  `~/rebase-fe-pr58-codex` (branch `books/rca-holomorphic` @ `dd97d72`)
  plus the full `rebase-evidence-20261109/` directory (47 files).

## Why the home-root copies could go

All three clones' tracked code is on `main` via merged PRs, verified
live 2026-11-12 before removal:

- FE PR #56 (`texts/sonnet-form`) — MERGED 2026-11-10T01:31:08Z,
  merge commit `3cd1541c5970c0f099cac2c2626be1ba8381c588`. The
  review-clone HEADs (`9e2224e`, incl. the nested `fresh/` clone) are
  ancestors of `origin/main`.
- FE PR #58 (`books/rca-holomorphic`) — MERGED 2026-11-10T07:00:45Z,
  merge commit `808f64d1b41e1e07a45cd4de717f5efe95f0f60e`. Local HEAD
  `dd97d72` is an ancestor of `origin/main`.
- AuditA fix (`coordinator/fix-rca-audita-inventory` @ `4d386ef`) —
  merged as FE PR #64, and the HEAD is an ancestor of `origin/main`.

The only unpreserved content in each clone was the untracked reports
above, now preserved on this branch. The `.lake` build caches
(~15.5 GB across the two big clones) were regenerable and were not
preserved.

## Disposition of the other bakkie home-root entries (same run)

Left in place as exception candidates / standing, NOT removed:

- `bin/` (`with-ledger.sh`) — referenced by absolute path in
  `~/automations/conformance-{full,lightweight}/automation.yaml`.
- `blenderkit_data/` — BlenderKit addon data dir (addon installed at
  `~/.config/blender/5.2/scripts/addons/blenderkit/`); standard
  tool-home location.
- `lean-cache/` — the shared Mathlib golden cache per Derek's
  2026-11-10 order (`mathlib-d13f23b7/packages`, read-only 0555);
  deliberate standard location.
- `workspace/semantic-search/` — retired runtime per bakkie AGENTS.md,
  BUT it still holds the newest `formalization.npz` (Nov 12 04:26,
  989,461 bytes vs the canonical Nov 7 copy, 615,707 bytes) and the
  nightly writer (not a bakkie cron/timer) still targets the old path.
  Left standing until the job is repointed to
  `~/.local/state/semantic-search/data/threads` and the newer bytes
  are synced to the canonical location.
- `fleet-harness-repo/` — moved (not deleted) to
  `~/projects/fleet-ops/preserved/fleet-harness-repo-20261112/`
  (clean clone of MiomboAI/fleet-harness @ `9fba708`, HEAD in main per
  cached ref; unreferenced — live conformance runs from
  `~/projects/fleet-ops/fleet-harness/`).

Full per-entry disposition:
`~/workspace/projects/fleet-ops/files/violations-fix-20261112/bakkie.md`
(on the coordinator desk).
