#!/usr/bin/env bash
set -euo pipefail
lane=/home/derekblair/lane-work/codex-rca-g-proton
book="$lane/formalize-everything/books/rudin-real-and-complex-analysis"
cd "$book"
test "$(cat lean-toolchain)" = leanprover/lean4:v4.34.1
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612
if rg -n '\b(sorry|admit|axiom|native_decide)\b' RudinRCA/Chapter15.lean; then
  echo 'Disallowed proof token in Chapter15 source' >&2
  exit 1
fi
LEAN_NUM_THREADS=1 lake build RudinRCA.Chapter15
lake env lean -j1 RudinRCA/Chapter15.lean
sha256sum RudinRCA/Chapter15.lean lean-toolchain lakefile.toml lake-manifest.json
