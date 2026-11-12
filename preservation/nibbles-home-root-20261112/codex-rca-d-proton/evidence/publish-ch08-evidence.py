from pathlib import Path
import hashlib, json, shutil

lane=Path(__file__).resolve().parent.parent
book=lane/'formalize-everything/books/rudin-real-and-complex-analysis'
evidence=lane/'evidence'
gate=json.loads((evidence/'Ch08Gate.json').read_text())
assert gate['passed'] and gate['exit_statuses']=={'build':0,'audit':0}
assert gate['audit']['result_count']==177
source=book/'RudinRCA/Chapter08.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()==gate['source']['sha256']
clean=json.loads((evidence/'ch08-clean-state.json').read_text())
cache=json.loads((evidence/'ch08-clean-cache-get.receipt.json').read_text())
assert clean['new_lake_absent_after_rename'] and clean['source_sha256']==gate['source']['sha256']
assert cache['exit_status']==0
out=book/'evidence/ch08'
assert not out.exists(), 'Do not overwrite existing evidence'
out.mkdir(parents=True)
names=['Ch08Audit.lean','Ch08Audit.names.json','Ch08Gate.json','Ch08Gate.md',
 'ch08-final-build.log','ch08-final-build.receipt.json','ch08-final-audit.log',
 'ch08-final-audit.receipt.json','ch08-clean-state.json','ch08-clean-cache-get.log',
 'ch08-clean-cache-get.receipt.json','check_chapter_gate.py','test_chapter_gate.py',
 'chapter-gate-tests.log']
for name in names: shutil.copy2(evidence/name,out/name)
readme=f'''# Chapter 8 validation evidence

The full chapter source has SHA-256 `{gate['source']['sha256']}`.
The [mechanical gate](Ch08Gate.md) passed with full-build exit 0, audit exit 0,
and all 177 expected public declarations present exactly once. Every reported
axiom is one of `propext`, `Classical.choice`, and `Quot.sound`; the source scan
found no sorry/admit or added axiom declarations. The declaration inventory
includes definitions, structures and instances as well as all public theorems.
Private helper dependencies are included transitively by Lean's axiom reports.

[Clean-state preparation](ch08-clean-state.json) records that the entire previous
`.lake` directory was renamed out of the book, leaving it absent. No files were
removed. A fresh pinned checkout and [cache retrieval](ch08-clean-cache-get.log)
then succeeded before the [full build](ch08-final-build.log). The build receipt
also records that `RudinRCA/Chapter08.olean` was absent before invocation and
binds the source, umbrella, configuration and clean-state record. Both the chapter
and umbrella were freshly compiled. The [audit](ch08-final-audit.log) used
[these exact commands](Ch08Audit.lean).

The JSON receipts retain absolute paths from the originating lane as historical
provenance. Their recorded source/log hashes and command exit codes are preserved
verbatim; copied evidence is not represented as a new execution at these paths.
The mechanical gate checks source tokens, pins, command receipts, fresh target
build and the complete supplied audit list. It does not constitute independent
mathematical review or establish statement fidelity by itself. The node mapping
is in [SCOPING-D.md](../../SCOPING-D.md).

To reproduce from the book directory, retain or move an existing `.lake` outside
the project, fetch `lake exe cache get`, then run:

```bash
lake --no-ansi build
lake env lean -j1 evidence/ch08/Ch08Audit.lean
```

For new machine-readable receipts, use `check_chapter_gate.py capture` with
explicit `--book-root`, `--cwd`, `--source`, `--log`, `--receipt` paths and the
command after `--`. For the clean build, pass `--require-absent` for the target
`.olean`. For the audit, pass both the audit source and names JSON through
`--input`. Run `check` with those new receipts and explicit paths for all inputs;
use `--module RudinRCA.Chapter08`. Historical absolute-path receipts are not
portable replacements for a new capture. The included checker uses only the
Python standard library and Git; its 13 tests pass in the recorded test log.

Pins: Lean `leanprover/lean4:v4.34.1`; Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
No independent review or merge is claimed.
'''
(out/'README.md').write_text(readme)
print(json.dumps({'published_evidence':str(out),'copied_files':len(names),'source_sha256':gate['source']['sha256']}))
