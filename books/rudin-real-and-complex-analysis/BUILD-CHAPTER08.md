# Chapter 8 build and axiom evidence

The module [RudinRCA/Chapter08.lean](RudinRCA/Chapter08.lean) covers all 18 printed nodes `8.1`–`8.18`, with the printed inventory and statement disclosures in [SCOPING-D.md](SCOPING-D.md) and declaration map in [CHAPTER08-COVERAGE.md](CHAPTER08-COVERAGE.md). Clean-slate compilation and all-declaration axiom verification were executed independently at `main` commit `aba161c6229b4d973144597bc99958b8fe6f1eb0` by both the Chapter 8 audit lane (`carbon-rca-ch08-audit-20261111`, report SHA-256 `d64125ad63c251561504eb412c4ca4a5ebd827dc22810cb4b469142e2bba4888`) and the coordinator-appointed crossed Carbon review (`carbon-review-rca-clusterd-20261111`, verdict `PASS WITH ISSUES`, `0` blocking findings, `NB-1`–`NB-3`, review SHA-256 `f4d891365a78abc620ba5484ae672c6e0ca740b935a516d2305bd97de19d5210`, [FE #40](https://github.com/derekblair/formalize-everything/issues/40) comment `6806962135`).

- **Lean toolchain:** `leanprover/lean4:v4.34.1` (`Lean version 4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`; `Lake version 5.0.0-src+5045d00`; `lean-toolchain` blob `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`).
- **Mathlib:** `d13f23b723b8a846827a245b89c10fc7d3f11612` (`d13f23b7` in `lakefile.toml` and `lake-manifest.json`; prebuilt upstream golden cache at `/root/lean-cache/mathlib-d13f23b7/packages`, containing no prebuilt copy of any `RudinRCA` project module).
- **Clean-slate pre-build cleanup:** `rm -rf .lake/build` inside `books/rudin-real-and-complex-analysis/`; no prior project `.olean` artifact or incremental snapshot was present before compilation.
- **Clean-slate build command:** `lake build` (executed from `books/rudin-real-and-complex-analysis/` with `/root/.elan/bin` prepended to `PATH`; audit gate ran `2026-11-11T20:14:22Z`–`2026-11-11T20:16:02Z`, and crossed review §4.1 re-ran a fresh clean-slate `lake build` independently).
- **Clean-slate build result:** exit **0**, **8,938 jobs** (`Build completed successfully (8938 jobs).`), **0** `error:` lines across `1,202` log lines (`Built RudinRCA.Chapter08`, `Built RudinRCA`, `Built RudinRCA.AuditA`). All 37 `warning:` diagnostics on `RudinRCA.Chapter08` are benign linter/deprecation/unused-variable/`Try this:` messages (`NB-3`), with **0** `sorry` warnings.
- **Transitive `AuditA` environment audit:** `RUDIN_RCA_AUDIT_VERBOSE=1 lake env lean RudinRCA/AuditA.lean` exited **0**, auditing **1,576** project declarations (including `private`/generated constants) across **13** imported project modules (`14` project modules in the source tree), including all **274** constants in `RudinRCA.Chapter08` (`223` using `[propext, Classical.choice, Quot.sound]`, `26` using `[propext]`, `2` using `[propext, Quot.sound]`, and `23` axiom-free `[]`).
- **Chapter-scoped `#print axioms` allowlist checker:** `python3 evidence/check_axiom_audit.py RudinRCA/Chapter08.lean <clean-slate-build.log>` exited **0** — **136** `theorem`/`lemma` declarations (`98` public `theorem` + `2` `private theorem` + `36` `lemma`), **140** explicit `#print axioms` audit records (`136` theorems/lemmas plus `4` named instances), **zero missing records (`[]`)**, **zero disallowed axioms (`{}`)**.
- **Observed axiom union:** strictly `{propext, Classical.choice, Quot.sound}` (`['Classical.choice', 'Quot.sound', 'propext']`).
- **Forbidden-tactic and kernel-primitive verification:** **0** occurrences of `sorry`, `admit`, `native_decide`, `bv_decide`, `decide!`, or active-code `axiom` / `unsafe` / `implemented_by` / `extern` across all `2,934` lines of `RudinRCA/Chapter08.lean`; transitive compiled kernel constant-graph traversal from all `274` `RudinRCA.Chapter08` constants (`48,749` unique kernel constants visited) found **0** occurrences of `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`.

## Verbatim build and audit summaries

Clean-slate `lake build` completion and embedded `AuditA` summary (from `04-clean-slate-build.log`, SHA-256 `c7899e3cb2c66d2487e6b8f7dc0fe09e611190973d10aa4d48cb6af2cd46056c`; matching `build-ch08-clean-slate.log`, SHA-256 `1184455d87e0b2f5befa5ccc18adf82317934e0f7f816c3a28a3e4737b045bb2`):

```text
⚠ [8931/8938] Built RudinRCA.Chapter08 (12s)
...
✔ [8936/8938] Built RudinRCA (3.7s)
ℹ [8938/8938] Built RudinRCA.AuditA (14s)
info: RudinRCA/AuditA.lean:64:0: Axiom audit passed for 1576 project declarations (including private/generated) across 13 audited project modules; the package source tree holds 14 project modules, all imported into the audited graph and all present in the expected inventory; used: [propext,
 Classical.choice,
 Quot.sound].
Build completed successfully (8938 jobs).
```

Chapter-scoped `#print axioms` summary ([evidence/chapter08-clean-axioms.log](evidence/chapter08-clean-axioms.log) and `04-chapter08-print-axioms.log`, SHA-256 `0707171f7a6df09ab4ed1b53f8e002a7d151b28da6ceb95f4c614d38de7c9dd0`):

```text
Theorem/lemma declarations: 136; audit records: 140
Missing records: []
Disallowed axioms: {}
Observed axiom union: ['Classical.choice', 'Quot.sound', 'propext']
```

## Source and evidence digests (`HEAD = aba161c6229b4d973144597bc99958b8fe6f1eb0`)

- `RudinRCA/Chapter08.lean` (blob `6d08f6abcf0f41eb9a9a872e4b391475f217e89c`, `2,934` lines): SHA-256 `aace6d8d9347662bc82a28fe44f793f2556cd26cd182874102e41c2c7e803184`.
- `RudinRCA/AuditA.lean` (blob `80a4728ad31c3b73c9d63153a223017b0d66c9cd`, `203` lines): SHA-256 `83e524ed914d719411961e344f771c3b9806b267e7a72910113f08cacb67e61e`.
- `RudinRCA.lean` (blob `6b944a85b6c2c7205c75a375e40b6995b4772062`, `35` lines): SHA-256 `eb0bb9f9e4c6e15555ad0a5c122affa63bc99887f80ae2bb9ba0db901977dc3c`.
- `lakefile.toml` (blob `0ee56b96afb9e88f571c3ab183a34eb5573a5b2b`): SHA-256 `ea7a7793831d416c91ede7ecfb98ee9120c577ea38507337ba19b5f9be81bb3f`.
- `lake-manifest.json` (blob `b1e3854068fe1164962caaea60055b591e69b028`): SHA-256 `3d3476c312fb2220e92334726052c3b23080ad1f97c3db6cfceedc9a90466d1b`.
- Verbose `AuditA` log (`audit-ch08.log` / `04-audita-verbose.log`, `1,597` lines): SHA-256 `afd5a33a46b1c78b820c588c92115722685d658bf92303a82f859b1f8ceb4870`.
- Kernel constant-graph check (`04-kernel-tactic-check.log`): SHA-256 `442886c4b8959ad3f283724a2253cade55e38cc13269c71dc62a499b1178207d`.

In-repository artifacts from the earlier Chapter 8 branch gate ([evidence/chapter08-clean-cache.log](evidence/chapter08-clean-cache.log), [evidence/chapter08-clean-build.log](evidence/chapter08-clean-build.log) at `3,231` branch-local jobs, and [evidence/chapter08-clean-axioms.log](evidence/chapter08-clean-axioms.log)) and [evidence/check_axiom_audit.py](evidence/check_axiom_audit.py) are retained alongside the `main`-head `8,938`-job full-book clean-slate build and `1,576`-declaration `AuditA` evidence recorded above.
