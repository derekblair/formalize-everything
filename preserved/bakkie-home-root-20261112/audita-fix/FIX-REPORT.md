# RCA AuditA inventory diagnosis — stopped for chapter disposition

**Outcome: main failure reproduced; no fix applied. FE #58 remains blocked.**

The unchanged main tree fails with the reported `BlaschkeMeansWork` inventory error. The full census finds **79 actionable orphan modules**, including a substantive **442-line Chapter06 with 43 named declarations**, and **three imported chapters missing from `expectedModules`**. Chapter06 and its development bundle are documented as unfinished work. This meets the brief's explicit stop condition: “If the fix needs judgment beyond this brief … a whole chapter's worth of modules are orphaned … STOP and report the options instead of guessing.” No import, source move, deletion, proof change, inventory edit, or commit was made.

## Scope, branch and verified pins

- Repository: `derekblair/formalize-everything`; fresh clone: `/home/derekblair/audita-fix-fe-main`.
- Branch: `coordinator/fix-rca-audita-inventory`.
- Base and current head: `3cd1541c5970c0f099cac2c2626be1ba8381c588`. Main plus **zero** new commits.
- Task/evidence directory: `/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109` / `/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence`.
- Runner header and session turn metadata identify `gpt-6-astra`, effort `ultra`; native configuration sets `service_tier = "fast"`. The runner has no model/effort/tier override. This is a configuration/readback verification, not an independent server billing-tier assertion. [001-pins.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/001-pins.log)
- Repo `lean-toolchain`: `leanprover/lean4:v4.34.1`; live Lake reports Lean 4.34.1. `lakefile.toml`, manifest, and actual dependency checkout agree on Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. [004-repository-pins.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/004-repository-pins.log), [009-live-toolchain.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/009-live-toolchain.log), [015-mathlib-checkout.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/015-mathlib-checkout.log)
- The user explicitly requested this home-root clone; all task logs and scripts live in the provided workshop task directory. No installation or system reconfiguration was performed beyond the explicitly requested repository dependency/cache preparation.

## Mandatory reproduction on untouched main

Both commands ran in `/home/derekblair/audita-fix-fe-main/books/rudin-real-and-complex-analysis`, on the fix branch at the pinned base, with no source edits. `record_command.py` records argv, exact cwd, UTC start/end, combined stdout/stderr, exit status and output SHA-256. The full build was allowed to finish.

| Command | Exit | Start UTC | Finish UTC | Complete output |
|---|---:|---|---|---|
| `lake exe cache get` | 0 | 2026-11-10T02:38:31.292997+00:00 | 2026-11-10T02:40:45.059898+00:00 | [006-cache-before.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/006-cache-before.log) |
| `lake build` | 1 | 2026-11-10T02:41:00.660447+00:00 | 2026-11-10T02:43:45.822038+00:00 | [014-build-before.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/014-build-before.log) |

Cache log SHA-256: `42ebc73609c550eb6bbe502f02f89259d6fd7d139c3b74f0b2a046b03ad75e5a`.

Build log SHA-256: `1ab982c9a2667ebe447fca00cfc19ab4a824c87aac3a6ea67d651bc9aa44dc72`.

Failure:

```text
RudinRCA/AuditA.lean:64:0: Axiom audit module-inventory mismatch: source module BlaschkeMeansWork belongs to this package (present in the package source tree) but is not imported into the audited import graph
```

This reproduces on main independently of #58. The failed build is evidence of a real main defect, not an inference from the rebased PR. The first failing orphan masks additional orphan and stale-expected failures.

## Complete three-way inventory

All 201 lines of AuditA were read. The unchanged walk resolves the audit source's physical grandparent as package root, recursively visits **all** descendants (including symlink directories), skips entries named `.lake`, and maps every `.lean` file by relative path. A package-local `scratch/`, `archive/`, or `evidence/` directory remains inventoried.

The import graph was enumerated from source, including `public import`, and independently confirmed by a read-only Lean environment probe outside the package. The probe imports exactly AuditA's three imports and prints `env.header.moduleNames`; intersecting those names with DISCOVERED gives the same nine modules. It does not execute, modify or bypass AuditA. Probe command: `lake env lean /home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/InventoryEnvironment.lean`, cwd `/home/derekblair/audita-fix-fe-main/books/rudin-real-and-complex-analysis`, exit 0. [017-environment.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/017-environment.log)

The exact invariant, including the existing intentional self-entrypoint exception, is:

```text
DISCOVERED = EXPECTED = AUDITED ∪ {RudinRCA.AuditA}
```

| Set / discrepancy | Count |
|---|---:|
| DISCOVERED | 89 |
| AUDITED (actual imported project modules) | 9 |
| EXPECTED | 7 |
| Literal DISCOVERED − AUDITED | 80 |
| Permitted self-entrypoint absent from its own environment | 1 |
| Actionable orphans: DISCOVERED − AUDITED − {AuditA} | **79** |
| AUDITED − EXPECTED | **3** |
| EXPECTED − AUDITED − {AuditA} | 0 |
| DISCOVERED − EXPECTED | 82 |

The full DISCOVERED file list is the union of the 79-row orphan table below, the following nine audited files, and `RudinRCA/AuditA.lean` (the self-entrypoint). No source file is omitted. [Complete machine-readable file/module/import mapping](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/review-inventory-data.json)

| Audited module | File relative to package | In current EXPECTED? |
|---|---|---|
| `RudinRCA` | `RudinRCA.lean` | Yes |
| `RudinRCA.Chapter01` | `RudinRCA/Chapter01.lean` | Yes |
| `RudinRCA.Chapter02` | `RudinRCA/Chapter02.lean` | Yes |
| `RudinRCA.Chapter03` | `RudinRCA/Chapter03.lean` | Yes |
| `RudinRCA.Chapter04` | `RudinRCA/Chapter04.lean` | Yes |
| `RudinRCA.Chapter05` | `RudinRCA/Chapter05.lean` | Yes |
| `RudinRCA.Chapter08` | `RudinRCA/Chapter08.lean` | No |
| `RudinRCA.Chapter13` | `RudinRCA/Chapter13.lean` | No |
| `RudinRCA.Chapter15` | `RudinRCA/Chapter15.lean` | No |

Current EXPECTED (all seven entries): `RudinRCA`, `RudinRCA.Chapter01`, `RudinRCA.Chapter02`, `RudinRCA.Chapter03`, `RudinRCA.Chapter04`, `RudinRCA.Chapter05`, `RudinRCA.AuditA`.

## Audited but absent from EXPECTED — all 3 modules

Each module is imported directly by the umbrella. Their presence is not hypothetical; the native environment probe confirms all three. The last substantive inventory update was `f4c45e85d636dfea778ee3787dd45679fd888cd2`, adding chapters 4–5, before these later main integrations. The allowed axioms and enforcement need no change.

| Module / file | First-add commit; author date | Main integration; date; PR | Reference evidence |
|---|---|---|---|
| `RudinRCA.Chapter08` / `RudinRCA/Chapter08.lean` | `f1ea85da08c45f54ee0e1a8ac342538f2dffec5f`; 2026-10-30T15:27:52-07:00 | `fa8bcd6f97aa0f78c392f9fc0565022ee11eb922`; 2026-11-09T15:39:56-08:00; #50 | `RudinRCA.lean:6` imports it; full repo name occurrences in `016-extra-history.log` |
| `RudinRCA.Chapter13` / `RudinRCA/Chapter13.lean` | `adac5946b1a363f1c861e0c583a329fb7a1e8c7c`; 2026-10-29T11:21:40-07:00 | `34a7ea8e45c0005494904b55a4d39384c69500d7`; 2026-11-09T16:35:53-08:00; #51 | `RudinRCA.lean:7` imports it; full repo name occurrences in `016-extra-history.log` |
| `RudinRCA.Chapter15` / `RudinRCA/Chapter15.lean` | `9d0527485279c0a86bdbcb90cb66440720620e59`; 2026-10-30T15:27:55-07:00 | `c302bb0a7fe5671d75d5187765059fd897805520`; 2026-11-09T17:04:46-08:00; #52 | `RudinRCA.lean:8` imports it; full repo name occurrences in `016-extra-history.log` |

Full history and reference commands: [010-extra-module-history.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/010-extra-module-history.log), [011-first-parent-history.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/011-first-parent-history.log), [016-extra-history.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/016-extra-history.log), [extra-module-history-data.json](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/extra-module-history-data.json).

## Orphan provenance classes and disposition

These are **recommendations for the coordinator's decision**, not applied changes. Dates distinguish original development from actual main integration; the brief's October 30 date is the checkpoint author date, not its main merge date.

| Class | Files | First add / author time | Main merge / time / PR | Disposition and reason |
|---|---:|---|---|---|
| C: Chapter06 | 1 | `d92130e9f3ce0715941e3c3579d919c1b04c6d38`; 2026-10-30T15:27:50-07:00 | `34098c7573b62ae7de730573b255057a55459c31`; 2026-11-09T16:02:30-08:00; #49 | **Hold for coordinator:** genuine partial book chapter, 442 lines/43 named declarations. It must either be intentionally included and audited or explicitly deferred outside the package. Cannot classify as dead scratch. |
| C: Scratch chapter-6 development | 32 | Same C commit/time | Same C merge/time/#49 | Preserve together outside package if confirmed development; mutual imports, overlapping declarations and aggregate references rule out blind wiring or deletion. |
| C: `DevelopmentAggregate` and `DevelopmentImports` | 2 | Same C commit/time | Same C merge/time/#49 | Preserve outside package with development material. The generator explicitly calls the aggregate development evidence rather than the delivered chapter. Imports file declares no named mathematical content. |
| G: Chapter-15 working drafts, check and snapshot | 44 | `9d0527485279c0a86bdbcb90cb66440720620e59`; 2026-10-30T15:27:55-07:00 | `c302bb0a7fe5671d75d5187765059fd897805520`; 2026-11-09T17:04:46-08:00; #52 | Preserve together outside package. They form a draft dependency graph; some theorem families were separately integrated in Chapter15. The snapshot has proof differences, so deletion as an exact duplicate is unsupported. |

The rebased committer times are 2026-11-09T23:58:17Z (C) and 2026-11-10T00:59:35Z (G). Both original commit messages expressly describe WIP checkpoints, “draft, not for merge.” By lexical filename class, the 79 orphans are **32 Scratch files, 42 `*Work.lean` files, four other root files, and Chapter06**. The four other root files are `DevelopmentAggregate.lean`, `DevelopmentImports.lean`, `ElementaryFactorWork.check1.snapshot.lean`, and `JensenZeroGrowthCheck.lean`.

## Full orphan file and reference table — all 79

All file paths below are relative to `/home/derekblair/audita-fix-fe-main/books/rudin-real-and-complex-analysis`. The module name is that path with `/` mapped to name components and `.lean` removed. For the dotted snapshot basename, AuditA creates one name component `«ElementaryFactorWork.check1.snapshot»`, not three directory components. C/G identify the exact add/landing commits, dates and PRs in the class table above; every row repeats its abbreviated add/merge and PR for easy review.

Declaration searches use repo-wide `git grep` on all extracted named declarations, excluding the file itself, and retain complete matching lines. Counts are **lexical matching lines**, not resolved Lean dependencies. The column `chapter / draft / other` separates chapter/audit source, other working Lean files, and documents/scripts/historical records. Chapter source includes the orphan Chapter06. Duplicate definitions, comments, unrelated same-basename identifiers and logs can match. No module in the actual nine-module audited graph imports any orphan. “Module hits” includes filename/module-name text, independent of declaration searches. “Inventory hits” covers PROGRESS, QUEUE, INVENTORY and SCOPING; interpretation follows the table.

| File | Class; added → main merge; PR | Named declarations | External declaration-name lines (chapter / draft / other) | External module hits | Inventory hits |
|---|---|---:|---|---:|---:|
| `BlaschkeMeansWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 5 | 0 / 0 / 0 | 0 | 0 |
| `BlaschkeNecessityWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 14 | 0 / 1 / 0 | 2 | 0 |
| `BlaschkeWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 18 | 0 / 6 / 0 | 1 | 0 |
| `BoundaryProductGeometryWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 6 | 0 / 31 / 0 | 3 | 0 |
| `BoundaryProductWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 22 | 0 / 102 / 0 | 2 | 0 |
| `Chapter15QuotientInterpolationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 69 | 0 / 290 / 59 | 3 | 0 |
| `DevelopmentAggregate.lean` | C; `d92130e9` → `34098c75`; #49 | 203 | 110 / 689 / 870 | 163 | 2 |
| `DevelopmentImports.lean` | C; `d92130e9` → `34098c75`; #49 | 0 | 0 / 0 / 0 | 4 | 0 |
| `ElementaryFactorWork.check1.snapshot.lean` | G; `9d052748` → `c302bb0a`; #52 | 13 | 102 / 101 / 13 | 0 | 0 |
| `ElementaryFactorWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 13 | 102 / 101 / 13 | 14 | 0 |
| `EntireLogWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 10 | 34 / 5 / 0 | 1 | 0 |
| `EntireProductWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 4 | 12 / 3 / 0 | 1 | 0 |
| `FactorizationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 3 | 6 / 0 / 0 | 0 | 0 |
| `FiniteProductWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 3 | 7 / 0 / 4 | 0 | 1 |
| `HolomorphicBezoutWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 12 | 0 / 4 / 0 | 1 | 0 |
| `HolomorphicIdealAssemblyWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 2 | 0 / 1 / 0 | 1 | 0 |
| `HolomorphicIdealTheoremWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 2 | 0 / 0 / 0 | 0 | 0 |
| `HolomorphicIdealsWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 0 / 3 / 0 | 1 | 0 |
| `HolomorphicProductWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 10 | 32 / 9 / 0 | 0 | 0 |
| `InterpolationLocalWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 5 | 0 / 21 / 4 | 4 | 0 |
| `InterpolationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 6 | 0 / 21 / 5 | 11 | 0 |
| `JensenWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 0 / 27 / 0 | 2 | 0 |
| `JensenZeroGrowthCheck.lean` | G; `9d052748` → `c302bb0a`; #52 | 33 | 0 / 147 / 0 | 0 | 0 |
| `LogMeansWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 32 | 0 / 0 / 0 | 1 | 0 |
| `MellinFunctionalWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 13 | 0 / 4 / 0 | 1 | 0 |
| `MeromorphicPoleDataWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 11 | 0 / 56 / 9 | 3 | 0 |
| `MeromorphicQuotientAssemblyWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 3 | 0 / 8 / 3 | 3 | 0 |
| `MeromorphicQuotientWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 4 | 0 / 12 / 4 | 3 | 0 |
| `MittagLefflerInfinityWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 9 | 0 / 40 / 7 | 5 | 0 |
| `MittagLefflerKernelWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 0 / 56 / 7 | 4 | 0 |
| `MittagLefflerSeriesWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 14 | 0 / 82 / 13 | 4 | 0 |
| `MittagLefflerSetWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 4 | 0 / 18 / 3 | 4 | 0 |
| `MuntzConclusionsWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 0 / 0 / 0 | 0 | 0 |
| `MuntzDistanceWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 11 | 0 / 1 / 0 | 2 | 0 |
| `MuntzNonDensityWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 17 / 2 / 0 | 1 | 0 |
| `MuntzSzaszWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 23 | 1 / 52 / 0 | 8 | 0 |
| `NevanlinnaWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 5 | 0 / 8 / 0 | 1 | 0 |
| `NormalizedInterpolationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 5 | 0 / 20 / 4 | 4 | 0 |
| `PrescribedZerosWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 3 | 0 / 14 / 0 | 2 | 0 |
| `RadialBoundaryWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 25 | 0 / 0 / 0 | 0 | 0 |
| `RudinRCA/Chapter06.lean` | C; `d92130e9` → `34098c75`; #49 | 43 | 0 / 109 / 335 | 783 | 1 |
| `Scratch61.lean` | C; `d92130e9` → `34098c75`; #49 | 2 | 7 / 7 / 8 | 0 | 0 |
| `Scratch610Discussion.lean` | C; `d92130e9` → `34098c75`; #49 | 18 | 0 / 73 / 21 | 11 | 0 |
| `Scratch610Exhaustion.lean` | C; `d92130e9` → `34098c75`; #49 | 1 | 0 / 0 / 0 | 1 | 0 |
| `Scratch611Completed.lean` | C; `d92130e9` → `34098c75`; #49 | 7 | 0 / 28 / 0 | 4 | 0 |
| `Scratch611Example.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 23 / 18 | 9 | 0 |
| `Scratch614Signs.lean` | C; `d92130e9` → `34098c75`; #49 | 1 | 0 / 0 / 0 | 1 | 0 |
| `Scratch615General.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 0 / 0 | 1 | 0 |
| `Scratch615GeneralSupport.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 0 / 0 | 2 | 0 |
| `Scratch615Infinity.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 0 / 0 | 1 | 0 |
| `Scratch616.lean` | C; `d92130e9` → `34098c75`; #49 | 11 | 0 / 50 / 27 | 29 | 0 |
| `Scratch616B.lean` | C; `d92130e9` → `34098c75`; #49 | 2 | 0 / 8 / 12 | 29 | 0 |
| `Scratch616C.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 30 / 48 | 13 | 0 |
| `Scratch616D.lean` | C; `d92130e9` → `34098c75`; #49 | 4 | 0 / 13 / 18 | 43 | 0 |
| `Scratch616E.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 20 / 9 | 16 | 0 |
| `Scratch616F.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 21 / 27 | 20 | 0 |
| `Scratch616G.lean` | C; `d92130e9` → `34098c75`; #49 | 1 | 0 / 3 / 3 | 6 | 0 |
| `Scratch616H.lean` | C; `d92130e9` → `34098c75`; #49 | 2 | 0 / 6 / 9 | 22 | 0 |
| `Scratch616I.lean` | C; `d92130e9` → `34098c75`; #49 | 1 | 0 / 4 / 3 | 18 | 0 |
| `Scratch616J.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 18 / 0 | 5 | 0 |
| `Scratch617.lean` | C; `d92130e9` → `34098c75`; #49 | 3 | 7 / 7 / 8 | 0 | 0 |
| `Scratch618Extension.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 15 / 18 | 19 | 0 |
| `Scratch618Final.lean` | C; `d92130e9` → `34098c75`; #49 | 2 | 0 / 7 / 3 | 6 | 0 |
| `Scratch618Polar.lean` | C; `d92130e9` → `34098c75`; #49 | 1 | 0 / 5 / 6 | 9 | 0 |
| `Scratch619Assembly.lean` | C; `d92130e9` → `34098c75`; #49 | 7 | 0 / 37 / 0 | 4 | 0 |
| `Scratch619Clip.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 23 / 15 | 8 | 0 |
| `Scratch619Density.lean` | C; `d92130e9` → `34098c75`; #49 | 3 | 0 / 9 / 9 | 8 | 0 |
| `Scratch619PositivePart.lean` | C; `d92130e9` → `34098c75`; #49 | 23 | 2 / 88 / 99 | 86 | 1 |
| `Scratch619Regular.lean` | C; `d92130e9` → `34098c75`; #49 | 3 | 0 / 10 / 9 | 12 | 0 |
| `Scratch619Uniqueness.lean` | C; `d92130e9` → `34098c75`; #49 | 5 | 0 / 16 / 21 | 22 | 0 |
| `Scratch63.lean` | C; `d92130e9` → `34098c75`; #49 | 6 | 0 / 14 / 6 | 12 | 0 |
| `Scratch64.lean` | C; `d92130e9` → `34098c75`; #49 | 16 | 39 / 39 / 87 | 1 | 0 |
| `Scratch69.lean` | C; `d92130e9` → `34098c75`; #49 | 26 | 0 / 90 / 151 | 27 | 0 |
| `SpherePrescribedZerosWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 98 | 0 / 594 / 0 | 0 | 0 |
| `SphereWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 49 | 0 / 473 / 0 | 3 | 0 |
| `UniformProductWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 6 | 17 / 3 / 7 | 0 | 1 |
| `ZeroGrowthWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 25 | 0 / 120 / 0 | 2 | 0 |
| `ZeroMultiplicityEnumerationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 8 | 0 / 80 / 0 | 2 | 0 |
| `ZeroSetNormalizationWork.lean` | G; `9d052748` → `c302bb0a`; #52 | 10 | 0 / 65 / 0 | 3 | 0 |

Full names, SHA-256 per source, every matching file/line, importers and provenance are retained in [work-inventory.json](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/work-inventory.json) (46 root files) and [scratch-history.json](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/scratch-history.json) (32 Scratch files and Chapter06). Human-readable expanded tables and reasoning: [work-history.md](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/work-history.md), [scratch-history.md](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/scratch-history.md), [scratch-conclusions.md](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/scratch-conclusions.md). Work `v2` logs and `scratch-003-diagnosis-complete.log` are authoritative; older command logs are retained as superseded search passes, not omitted or rewritten.

Reference and inventory findings:

- **BlaschkeMeansWork:** all five theorem names have zero occurrences outside the source. Its file/module name has no external occurrence either. This confirms the specific observation in the brief.
- **Chapter06 and scratch:** `Scratch61`, `Scratch64`, and `Scratch617` contain names separately defined/used in Chapter06; Chapter06 does not import those files. Other scratch names occur in the draft graph, DevelopmentAggregate or historical evidence. `Scratch619PositivePart.Values` also matches the English word “Values” in chapter comments and SCOPING-D:24; those are false dependencies.
- **Chapter-15 drafts:** elementary factors, entire logarithms/products, factorization, finite/uniform products and holomorphic products have versions integrated separately in Chapter15. Their grep hits do not make the original working modules dependencies. `MuntzNonDensityWork.intervalToL2` and Chapter04's same basename are independent declarations; `MuntzSzaszWork.UnitInterval` matches a Mathlib import token.
- **PROGRESS/QUEUE/inventories:** no orphan filename/module name is explicitly mentioned in these inventory documents. PROGRESS:59 does describe Chapter 6 implementation as in progress with no complete Stage 2 gate; SCOPING-C inventories its 19 numbered nodes; QUEUE has no Chapter-6 entry. SCOPING-G:135 names the finite/uniform-product theorem families and :137 records integration in Chapter15. The `FiniteProductWork` and `UniformProductWork` inventory hits are thus meaningful family mentions. The two DevelopmentAggregate hits are incidental (`SignedMeasure.totalVariation` in SCOPING-C:93 and English “Values” in SCOPING-D:24); Chapter06's `totalVariation` hit is the same distinct Mathlib identifier. No genuine inventory identifier references were found for the scratch files. These topic-level records do not authorize deleting or silently accepting the chapter.
- **Working infrastructure:** `evidence/assemble-development.py`, `evidence/run-development.py`, `evidence/check-chapter06.sh`, and `assemble_quotient_interpolation.py` refer to development paths. Moving only Lean files may leave development scripts pointing at old locations. Preserve the material and record archival status; make any future runnable-path changes deliberately rather than regenerate theorem content in this repair. No development scripts were executed here.

## Concrete options requiring the coordinator's ruling

1. **Include the existing partial Chapter06.** Import `RudinRCA.Chapter06` from the umbrella, add Chapter06/08/13/15 to `expectedModules`, and relocate the 78 top-level development files outside the package with byte-for-byte preservation. Expected/source inventory would be 11 modules, audited imports 10. Run the full cache/build and unchanged axiom audit. This does not claim completed Chapter-6 coverage. If its existing code does not build/audit, theorem/proof repair is outside this brief and requires separate scope.
2. **Explicitly defer Chapter06 with its WIP material.** Preserve Chapter06 and the 78 top-level development files outside the package; keep the existing umbrella imports and add Chapter08/13/15 to EXPECTED. Expected/source inventory would be 10 modules, audited imports 9. This changes the delivered book boundary and needs an explicit coordinator decision, even though all proof bytes can be preserved.

A concrete external archive candidate for either option is repository-root `research/rudin-real-and-complex-analysis-work/`, preserving the original relative layout and with **no symlink back from the package**. It is not a descendant of `books/rudin-real-and-complex-analysis/`; the unchanged root-anchored walk cannot visit it. A subdirectory inside the package would fail, and `.lake` is a build/cache directory, not a proof archive. No deletion is necessary; git also preserves the original file content and provenance. None of these options was executed or claimed validated.

In either option, keep AuditA's enforcement logic and allowed axiom list (`propext`, `Classical.choice`, `Quot.sound`) byte-identical; change only the explicit expected list, intended imports and authorized source placement. The final explicit list must equal the actual imported project set **plus AuditA**, exactly as the existing entrypoint exception requires.

## Fix diff, final verification and post-fix build

**No fix diff or new commit exists.** Head remains `3cd1541c5970c0f099cac2c2626be1ba8381c588` on `coordinator/fix-rca-audita-inventory`. The branch contains main plus zero commits. All 89 discovered Lean files are byte-identical to the pinned main blobs; tracked diff and cached diff are empty, and `git diff --check` exits 0. The report copy in the clone is the sole intended untracked deliverable. Verification: [018-unchanged.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/018-unchanged.log), [020-final-tree.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/020-final-tree.log).

**Post-fix `lake exe cache get` / `lake build`: not run**, because the required chapter-disposition stop condition prevented applying a fix. There is no post-fix success status, log hash, or new head to claim. FE #58 remains blocked pending the coordinator ruling and subsequent authorized repair/build.

The #58 branch and `/home/derekblair/rebase-fe-pr58-codex/` were not accessed, reset, built, modified or used as a cache source. All Git mutations were the requested fresh clone and new fix branch; no push, PR, message to an external service, or change to another checkout was performed.

## Evidence and integrity

- This report is copied byte-for-byte to `/home/derekblair/audita-fix-fe-main/FIX-REPORT.md`.
- [SHA256SUMS](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/SHA256SUMS) hashes frozen logs, command metadata, supporting inventories/reviews, task scripts and this report. Verify from `/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109` using `sha256sum -c evidence/SHA256SUMS`.
- Each recorded command has `.json` metadata and a full combined-output `.log`; scripts that issue multiple Git commands also record their nested argv/cwd/status/output. Metadata log hashes are independently checked during finalization. No output was truncated in evidence files; only interactive previews were shortened.
- [COMMAND-INDEX.json](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/COMMAND-INDEX.json) collects every recorded command's metadata for navigation. [final-report-review.md](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/final-report-review.md) records the independent report/inventory review.
- The mutable runner transcript `run-fix.log` and SHA256SUMS itself are deliberately excluded from the digest manifest. Model verification extracts only non-secret pin metadata; no runtime credentials are collected.
- Read-only local `session_gate.py audit` returned registration-schema/coverage findings for the pre-existing runner registration ([003-session-audit.log](/home/derekblair/projects/math/tasks/codex-fix-fe-audita-20261109/evidence/003-session-audit.log)). This task did not reconfigure live lanes or claim fleet conformance; actual model/effort and configured tier were separately read back above.
