# Chapter 8 mechanical gate tooling

`check_chapter_gate.py` uses only the Python standard library and Git. It installs nothing, removes nothing, and does not run Lean except when an explicit command is supplied to `capture`. All generated artifacts stay in evidence when using the commands below. This is mechanical validation, not mathematical statement checking or independent review.

The final build and audit must use the same source bytes and pinned Lean/Mathlib configuration. The audit additionally records the exact expected-name inventory and audit command source. A report fails if an input or log was changed after capture, if a command returned nonzero, if a pin differs, if a Lean error/sorry diagnostic appears, if an expected axiom result is missing/duplicated, or if an axiom other than `propext`, `Classical.choice`, or `Quot.sound` appears. Unexpected audit names and malformed/truncated axiom messages also fail.

Before the build, root prepares its authorized clean build state. The wrapper itself does not delete or move build outputs. It requires the target `.olean` to be absent before execution, and the final checker requires a fresh `Built RudinRCA.Chapter08` line plus Lake's successful-completion marker. These observations establish a fresh target-module build; they do not establish that the entire Mathlib dependency cache was deleted. Record broader clean-state preparation separately if claiming that.

From the lane root, set ordinary task variables:

```bash
RCA_GATE_BOOK="$PWD/formalize-everything/books/rudin-real-and-complex-analysis"
RCA_GATE_EVIDENCE="$PWD/evidence"
```

Capture the final build after its clean-state preparation:

```bash
python3 evidence/check_chapter_gate.py capture \
  --source "$RCA_GATE_BOOK/RudinRCA/Chapter08.lean" \
  --book-root "$RCA_GATE_BOOK" --cwd "$RCA_GATE_BOOK" \
  --log "$RCA_GATE_EVIDENCE/ch08-final-build.log" \
  --receipt "$RCA_GATE_EVIDENCE/ch08-final-build.receipt.json" \
  --require-absent "$RCA_GATE_BOOK/.lake/build/lib/lean/RudinRCA/Chapter08.olean" \
  -- lake build RudinRCA.Chapter08
```

Capture the complete axiom audit after the successful build:

```bash
python3 evidence/check_chapter_gate.py capture \
  --source "$RCA_GATE_BOOK/RudinRCA/Chapter08.lean" \
  --book-root "$RCA_GATE_BOOK" --cwd "$RCA_GATE_BOOK" \
  --input "$RCA_GATE_EVIDENCE/Ch08Audit.names.json" \
  --input "$RCA_GATE_EVIDENCE/Ch08Audit.lean" \
  --log "$RCA_GATE_EVIDENCE/ch08-final-audit.log" \
  --receipt "$RCA_GATE_EVIDENCE/ch08-final-audit.receipt.json" \
  -- lake env lean "$RCA_GATE_EVIDENCE/Ch08Audit.lean"
```

Generate the report:

```bash
python3 evidence/check_chapter_gate.py check \
  --source "$RCA_GATE_BOOK/RudinRCA/Chapter08.lean" \
  --book-root "$RCA_GATE_BOOK" \
  --names "$RCA_GATE_EVIDENCE/Ch08Audit.names.json" \
  --audit-source "$RCA_GATE_EVIDENCE/Ch08Audit.lean" \
  --build-log "$RCA_GATE_EVIDENCE/ch08-final-build.log" \
  --audit-log "$RCA_GATE_EVIDENCE/ch08-final-audit.log" \
  --build-receipt "$RCA_GATE_EVIDENCE/ch08-final-build.receipt.json" \
  --audit-receipt "$RCA_GATE_EVIDENCE/ch08-final-audit.receipt.json" \
  --output-prefix "$RCA_GATE_EVIDENCE/Ch08Gate"
```

This writes `Ch08Gate.json` (complete hashes, receipts, diagnostics, every audit entry) and `Ch08Gate.md` (readable result with the full expected-name table). Exit 0 means the requested mechanical checks passed; exit 1 means a failed gate; exit 2 means unusable/missing inputs. Capture exits 0 only when the invoked command exited 0 and tracked inputs stayed unchanged. Its receipt preserves the exact original command status, including nonzero/signal results. Capture uses an argv list and direct stdout/stderr redirection, without pipelines or shell traps.

The source lexer handles nested Lean block comments, line comments, plain/raw strings, escapes, character literals, quoted names, and escaped identifiers. It rejects explicit `sorry`, `admit`, `axiom`/`axioms` declarations and direct `sorryAx`; `#print axioms` is accepted. Interpolated strings are conservatively rejected because their antiquotations can execute Lean expressions. Unterminated lexical constructs also fail. This conservative scan is combined with the compiler and transitive axiom audit; it is not a replacement Lean parser.

Validation of the tooling: `python3 evidence/test_chapter_gate.py` passes 13 tests, including nested comments, strings, syntactic quotations, truncated/missing/duplicate audit outputs, forbidden axioms, diagnostics, pin changes, and stale hashes. `chapter-gate-tests.log` records the test run. `chapter-gate-capture-test.receipt.json` records a harmless Python capture test (exit 0); `chapter-gate-capture-failure-test.receipt.json` records a deliberately failing Python test (command exit 7, wrapper exit 1). These fixture files are explicitly not Lean build/audit evidence. No final chapter gate has been claimed by creating this tooling.
