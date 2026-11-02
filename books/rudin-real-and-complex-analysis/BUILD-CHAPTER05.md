# Chapters 4–5 build and axiom evidence

Chapter 5 covers numbered body nodes **5.1–5.25 (25)**. Chapter 4 covers
**4.1–4.26 (26)** and is rebuilt in this clean gate. Prose and proof-only nodes
retain their documented dispositions. See [the inventory](INVENTORY-B.md) and
[statement corrections](SCOPING-B.md). Exercises are excluded. This is
implementation evidence; coordinator-appointed crossed review remains required.

- Lean: `leanprover/lean4:v4.34.1`; Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Clean gate began `2026-11-01T09:17:18.688546+00:00` and finished `2026-11-01T09:22:39.801693+00:00`.
- The entire prior `.lake` was moved aside. Fresh pinned `lake exe cache get`
  exited **0**; ordinary full `lake build` exited **0**. No previous chapter
  artifacts or incremental snapshots were used.
- The lane-local lock serializes checks. `LEAN_NUM_THREADS=1` configures Lake;
  `weakLeanArgs = ["-j1"]` supplies chapter compilers with the actual `-j1` flag.
- Both axiom checkers exited **0**. Every theorem/lemma has an explicit audit;
  every explicit audit has its exact fully qualified record. Chapter counts
  exclude other chapters' records. Any disallowed axiom anywhere in the full
  build log, missing command/record, or conflicting duplicate audit fails.
- Both modules were scanned for `sorry`, `admit`, `axiom`, and `native_decide`:
  **zero matches**.

| Module | Theorem/lemma declarations | Scoped audit records | Audit exit | Evidence |
| --- | ---: | ---: | ---: | --- |
| `Chapter04` | 172 | 172 | 0 | [audit summary](evidence/chapter05-clean-continuation1-Chapter04-axioms.log) |
| `Chapter05` | 173 | 175 | 0 | [audit summary](evidence/chapter05-clean-continuation1-Chapter05-axioms.log) |

Observed Chapter 4 axiom union: `['Classical.choice', 'Quot.sound', 'propext']`.
Observed Chapter 5 axiom union: `['Classical.choice', 'Quot.sound', 'propext']`.

Source SHA-256 values:

- `RudinRCA/Chapter04.lean`: `d71fb2f7202629914f1773382b9a8448c462a29d27fc1ff300ff8f17100c4b45`.
- `RudinRCA/Chapter05.lean`: `9655bf06c393ec7c2236d4ef0b48180ee1247829f106b1aa2f7272b77580e253`.
- `lakefile.toml`: `5891835867714a57568c217bcae78911549ea06bd0896de174d2bdb13eeab5b6`.

The [fresh cache log](evidence/chapter05-clean-continuation1-cache.log), [full build log](evidence/chapter05-clean-continuation1-build.log),
[portable metadata](evidence/chapter05-clean-metadata.json), and
[audit checker](evidence/check_axiom_audit.py) accompany the module. The
[separate Chapter 4 gate](BUILD-CHAPTER04.md) passed before Chapter 5 compilation.

The `lakefile.toml` compiler flag, `RudinRCA.lean` umbrella, and `PROGRESS.md`
edits are branch-local shared-file changes. Reconciliation with sibling cluster
branches belongs to the coordinator. No review or merge is authorized by these
implementation checks.
