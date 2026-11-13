# Persistent Lean repair session

Status: driver implemented and Python syntax parsed; **no Lean server has been
launched or tested yet**. Respect the parent's serialized compile slot.

The installed Lean 4.34.1 implementation supports retaining imports and earlier
declarations when a document body is edited. This should avoid repeating the
heavy import paging on every repair, but measured performance is still pending.

## Verified installed implementation

All paths below are relative to
`/home/derekblair/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/`.

- `Lean/Language/Lean.lean:397`: unchanged header syntax reuses the existing
  import-processing task. Line 563 similarly reuses unchanged command tasks.
- `Lean/Server/README.md:25`: the watchdog manages one worker per open file.
  Imports are retained in that worker; changing the imports restarts it. Opening
  several documents creates several heavy workers, so use one scratch document.
- `Lean/Server/FileWorker.lean:376`: a second import setup in the same worker
  explicitly exits with restart code 2 because imports cannot be unloaded.
- `lake/Lake/CLI/Serve.lean:90`: `lake serve` launches installed `lean --server`
  with the workspace environment and supplied arguments.
- `Lean/Data/Lsp/Extra.lean:24`: `textDocument/didOpen` accepts
  `dependencyBuildMode: "never"`, preventing automatic dependency builds.
- `Lean/Data/Lsp/Extra.lean:37`: `textDocument/waitForDiagnostics` takes
  `{uri,version}` and replies after all diagnostics for that version or later
  have been emitted.
- `Lean/Server/FileWorker/RequestHandling.lean:467`: the barrier waits for both
  the diagnostic reporter and all command snapshots. This is the completion
  condition, not an empty initial diagnostic or a quiet period.
- `Lean/Server/FileWorker.lean:233`: final reporting emits exact-version
  `$/lean/fileProgress` with an empty processing list, or fatal-error progress.
- `Lean/Data/Lsp/Diagnostics.lean:158`: published diagnostics include a version;
  `isIncremental` means append, otherwise replace. The driver supports both and
  ignores wrong-document or wrong-version diagnostics.

## Driver

`lean_lsp_driver.py` uses only the Python standard library. It starts exactly one
`lake serve -- -j1`, opens exactly one document, forbids import/header changes,
and rejects an update while its predecessor is processing. This makes the
barrier's "version or later" guarantee an exact-version guarantee. Local control
uses a Linux abstract Unix socket with same-UID peer checking; no control socket
file or authentication material is created.

Start when the compile slot has been released, with a new evidence directory:

```bash
python3 lean_lsp_driver.py start \
  --book /home/derekblair/lane-work/codex-rca-g-proton/formalize-everything/books/rudin-real-and-complex-analysis \
  --file /home/derekblair/lane-work/codex-rca-g-proton/formalize-everything/books/rudin-real-and-complex-analysis/Chapter15QuotientInterpolationWork.lean \
  --evidence /home/derekblair/lane-work/codex-rca-g-proton/evidence/lsp-quotient-interpolation-1
```

The start command stays running. From another shell/tool invocation, call the
same script with `status`, `update`, or `shutdown` and the same `--evidence`
argument. `update` rereads the fixed target file, records a source snapshot and
SHA256, and sends a full-content `didChange` with a strictly increasing version.

Each version records exact source bytes, diagnostics, axiom-audit messages,
progress state, barrier response, and elapsed time. All inbound/outbound LSP
frames, parsed messages, and stderr are preserved in the evidence directory.
`lsp_clean` requires the completion barrier, exact-version diagnostic and
progress notifications, no errors or fatal progress, and no `sorryAx` messages.
`incomplete_protocol_evidence` is explicitly not a pass. A shutdown requested
during processing reports that the pending version is abandoned.

LSP diagnostics are for repairs only. They do not emit the release `.olean`
artifact or satisfy the required ordinary `lake build`, clean-slate build,
and standard-axioms audit gates.
