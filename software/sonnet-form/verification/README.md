# Verification evidence chronology

The current exhaustive theorem census is `axiom-audit.json` and its full Lean
output is `axiom-audit.txt`. The November 10 forward-fix verification records
are in `forward-fix-2026-11-10/`: each stage has the six exact commands, exit
statuses, elapsed times, complete logs, and SHA-256 hashes in `results.json`.
Log paths in those records are relative to their stage directory; `original_log`
retains the author machine's task path.

The root `checks.json`, `checks.txt`, `clean-build.json`, and `clean-build.txt`
are historical baseline evidence from the original implementation. The
`resume-2026-11-01/` directory is also historical. Their counts and theorem
names describe those earlier models, not the November 10 changes. They are
retained as provenance and must not be cited as current verification.

The command `python3 tools/audit_axioms.py --write` refreshes the deterministic
current census after a successful build. Ordinary verification uses the same
command without `--write` and writes its output into the stage log.

For this forward-fix run, `phase2-final-retry/` is the successful final six-command
record. `phase2-final/` retains an earlier attempt: Lean build and source import
passed, but generator freshness failed after a preparation renderer exception.
The catalogue renderer was corrected, regenerated, and checked in the final retry.
All source-changing model stages before it have separate successful six-command
records. No Lean build failed. `phase2-final-retry/fidelity.json` verifies frozen
file/pin identity, and `verdict-changes.json` records all affected lines, including
two newly failing licensed-meter lines rather than concealing them in net counts.
