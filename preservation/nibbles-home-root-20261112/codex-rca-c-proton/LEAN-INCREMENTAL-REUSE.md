# Lean 4.34.1 incremental CLI reuse

Inspected the installed source, without running a compiler or changing the toolchain:

- `/home/derekblair/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Lean/Elab/Frontend.lean`, especially lines 151–232 and 269–380.
- `Lean/Language/Lean.lean`, especially lines 82–137, 365–510, and 814–850.
- `Lean/CompactedRegion.lean`, lines 70–113.

## Recommendation for this lane

Use **header-only reuse first**, since import processing is the measured bottleneck and full snapshots retain substantially more elaborator metadata. Keep the aggregate's header and command-line options fixed across development passes. Include the anticipated final 6.19 imports before creating the snapshot.

On the next required aggregate compilation, add:

```sh
lake env lean -j1 --incr-header-save=evidence/ch06-header-v1.incr DevelopmentAggregate.lean
```

On subsequent passes with changed theorem bodies and the same header:

```sh
lake env lean -j1 --incr-load=evidence/ch06-header-v1.incr DevelopmentAggregate.lean
```

The first command creates **both** `ch06-header-v1.incr` and `ch06-header-v1.incr.deps`; preserve both. An optional separate seed source can consist only of the exact aggregate import header, but that costs a separate import pass, so adding the flag to the next already-needed aggregate is cheaper. Loading a header saved from a different filename is explicitly supported: the loader corrects `mainModule` and the private auxiliary-name prefix.

If imports change, a mismatched header causes normal import processing rather than reusing the old imported environment. Save a new header under a new versioned filename in that run, then use it thereafter. Compare the exact header, not merely its unordered import set: reuse checks syntax plus source positions (`eqWithInfo`), ignoring trailing header whitespace only.

## What it saves

Loading **does bypass constructing/merging the imported environment and its extensions** when the header matches. It does **not** leave a running process in memory or avoid all I/O: `loadIncrSnapshot` still reads the `.deps` JSON, mmaps every dependent `.olean`/`.ir` region and the snapshot, and reruns the subset of imported modules' initializers with recorded init work. It avoids the large repeated environment-building walk and skips initializer work for other modules. Heavy swapping can therefore still hurt, and actual speed must be measured locally.

`LEAN_IMPORT_WORKERS` controls snapshot dependency-region loading; the default is up to four workers, independently of the elaboration `-j1` setting. No override is necessary. Under current memory pressure, keep the default initially and avoid asserting the source-comment benchmark as a measured result on this machine.

## Full snapshots, if later useful

```sh
lake env lean -j1 --incr-save=evidence/ch06-pass3.incr DevelopmentAggregate.lean
lake env lean -j1 --incr-load=evidence/ch06-pass3.incr --incr-save=evidence/ch06-pass4.incr DevelopmentAggregate.lean
```

Full snapshots preserve the command/proof snapshot tree. Unchanged prefixes can be reused; changed syntax invalidates subsequent command state, with finer reuse available inside incremental tactics. They automatically default `internal.cmdlineSnapshots` to **false**, retaining the metadata required for reuse. **Do not pass `-Dinternal.cmdlineSnapshots=true` with full saves.** No `Elab.inServer` flag, LSP process, plugin, or installation is required.

A header-only seed normally records `internal.cmdlineSnapshots=true`. If transitioning from such a seed to full snapshots, use a fresh full-snapshot seed or deliberately seed the header with `-Dinternal.cmdlineSnapshots=false`; merely adding `--incr-save` while loading an old header does not clearly replace the saved header's options. The header-reuse branch reuses its saved command state without rerunning setup. For the same reason, keep CLI `-D` settings, trust settings, setup metadata and plugins fixed while reusing; make normal development option changes with `set_option` commands in the source, where syntax invalidation sees them.

## Errors and correctness boundaries

- Saves occur **before** `if hasErrors then return none`. Ordinary theorem/elaboration errors therefore do not prevent snapshots when Lean reaches a final command state. Import/header failure or abnormal termination may prevent saving. A snapshot's existence does not mean the check succeeded.
- Full snapshots can contain errored declarations and their diagnostics. Reuse does not certify those declarations; fixing the source invalidates the relevant state, and a passing run still needs exit 0 and the axiom audit.
- The `.deps` file records artifact paths; this frontend does not check their source hashes or mtimes when deciding reuse. Use snapshots only with unchanged Lean/runtime/shared libraries, pinned Mathlib, and unchanged imported build artifacts. If dependencies are rebuilt or the pin changes, seed again.
- The format permits serialized closures. `CompactedRegion.lean` explicitly requires **identical executables and dependent libraries** between save and load. Only load our own local snapshots.
- The loader calls initializer restoration a central experimental “HACK” and notes possible behavior divergence for unusual side-effectful initializers. Treat this as a development accelerator, not a substitute for the required ordinary clean build and axiom audit.
- Use **different versioned paths** for loaded and newly saved full snapshots. The loaded region is memory-mapped, and no same-path atomic-overwrite guarantee was established from the available Lean source. Versioned paths also preserve evidence without removals.
- Never use snapshot-assisted runs as the clean-slate evidence. The final accepted check should run with no `--incr-load`.

No commands in this note have been executed by this research subagent.
