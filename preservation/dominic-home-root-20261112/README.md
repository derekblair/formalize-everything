# Preservation: dominic /root home-root cleanup, 2026-11-12

Unique work products removed from `/root/` on dominic (100.92.68.4) during the
2026-11-12 spec-conformance home-root fix (28 violations). Bytes verified by
md5 against the dominic originals before removal; see md5s below.

## Contents

- `review-fe-pr59/` — crossed Codex review of formalize-everything PR #59
  ("RCA A: Chapter 1 proofs, Chapter 2 foundations, and Chapters 1–3
  inventory"), completed on dominic 2026-11-08. Verdict: **PASS**.
  PR #59 MERGED 2026-11-09T23:26:06Z, merge commit
  `1d89d0b117bff6deabbd80d7629c0d5795f30b61`.
  - `report.md` — the Codex review report (this copy was the ONLY copy;
    the desk harvest held only the Argon files).
  - `brief.md`, `run-review-pr59-codex.sh`, `codex-clone.log`,
    `codex.raw.log` — brief, launcher, clone log, raw Codex session log.
  - `evidence-20261108/` — 36 verification log files (build, diff, audit,
    preflight). Aggregate per-file md5 `3546816e2ce74fbe5deefe5665ff61bc`.
- `review-fe-audita-fix/` — crossed Codex review of formalize-everything
  PR #64 ("Fix RCA AuditA module-inventory mismatch: relocate 79 orphan
  .lean files"). PR #64 MERGED 2026-11-10T04:14:57Z, merge commit
  `2da3dc6f4e2993aeb670fa099a7e4ea508d2e466`.
  - `brief.md`, `run-review-fe-audita-fix.sh`, `codex.raw.log`.
- `cbor-fix/cbor-fix-build.log` — Lean build log for the CBOR RFC 8949
  Boundary-OOM fix verification (2026-11-10).
- `apostol-v5-fix-evidence.tar.gz` — evidence bundle for the Apostol v5 fix
  (dossiers v2–v4 + reviews, brief, sidecar, check-manifest.py, run.sh).
  The fix PASSED review. md5 `b1bd42e285cd032238b4f9aebe4f859d`.

## Deliberately NOT preserved here (reproducible from GitHub)

The review workdirs were plain clones at merged PR heads, clean trees, and
were removed without copying their contents:

- `/root/review-fe-pr59-codex` (7.7G) — clone at PR #59 head
  `f319087865f3d19e64c107eb1edae937973c7adf`, incl. untracked
  `independent-clone-20261108/` (clean). Commit exists on GitHub.
- `/root/review-fe-audita-fix` (22M) — clone at PR #64 head
  `4d386ef60cebf2479c4d8d50ecb101d71205ed93`, clean. Commit exists on GitHub.
- `/root/cbor-fix-verify-20261110` (17M) — clone on branch `cbor-m1-build`
  at `8f91e1aeaadc63d72ff5432386fe235e20083595`; branch `cbor-m1-build`
  exists on origin at the same commit. Clean tree.

## Source md5s (dominic originals)

- review-fe-pr59-report.md `e29e02dba4ed64e2621844314d28b44f`
- review-fe-pr59-brief.md `ae796d06f4ed9e2f7c08bd098c3d56c0`
- run-review-pr59-codex.sh `c3cff3d05f8056eb20b8dd310dff4f12`
- review-fe-pr59-codex-clone.log `6821b68bc88df9282ae74136c4ad24bc`
- review-fe-pr59-codex.raw.log `a443cc62994b419d3a4119f53c1cc9c8`
- review-fe-audita-fix-brief.md `3b3a71620698137831a745d8f3eb0fc5`
- run-review-fe-audita-fix.sh `9082f642eb526f95bc3ccbacca1439a6`
- review-fe-audita-fix-codex.raw.log `106a9b9e96925a0c0ea7da6b417e8cc8`
- cbor-fix-build.log `33efc7eb6886e93cbe739b311caf2ce4`
- apostol-v5-fix-evidence.tar.gz `b1bd42e285cd032238b4f9aebe4f859d`
