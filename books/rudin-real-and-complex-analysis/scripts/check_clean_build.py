#!/usr/bin/env python3
"""Build a source snapshot with fresh project outputs and pinned dependency cache.

The live checkout and its outputs are preserved. The temporary snapshot is
retained for inspection. No git operation or dependency installer is invoked.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"


def inputs(book: Path) -> dict[str, bytes]:
    names = {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
    for directory, children, files in os.walk(book):
        children[:] = [name for name in children if name != ".lake"]
        for name in files:
            if name.endswith(".lean"):
                names.add(str((Path(directory) / name).relative_to(book)))
    return {name: (book / name).read_bytes() for name in sorted(names)}


def main() -> int:
    book = Path(__file__).resolve().parents[1]
    snapshot = inputs(book)
    manifest = json.loads(snapshot["lake-manifest.json"])
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != PIN or snapshot["lean-toolchain"].decode().strip() != TOOLCHAIN:
        raise RuntimeError("required Lean/Mathlib pins changed")
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("lake is not provisioned; this script does not install it")
    packages = (book / ".lake" / "packages").resolve(strict=True)
    revision = subprocess.check_output(
        ["git", "-C", str(packages / "mathlib"), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != PIN:
        raise RuntimeError("dependency checkout does not match the Mathlib pin")
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib.olean").is_file():
        raise RuntimeError("dependency cache absent; first run lake exe cache get")

    fresh = Path(tempfile.mkdtemp(prefix="rca-a-clean-build-"))
    for name, content in snapshot.items():
        destination = fresh / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
    (fresh / ".lake").mkdir()
    (fresh / ".lake/packages").symlink_to(packages, target_is_directory=True)
    hashes = {name: hashlib.sha256(content).hexdigest() for name, content in snapshot.items()}
    (fresh / "input-sha256.json").write_text(json.dumps(hashes, indent=2) + "\n")
    print(f"Snapshot: {fresh}", flush=True)
    print("Fresh project output directory: absent before build", flush=True)
    print(f"Command: {lake} build (cwd={fresh})", flush=True)
    print(f"Dependency revision: {revision}", flush=True)
    print("Input SHA256: " + json.dumps(hashes, sort_keys=True), flush=True)
    result = subprocess.run([lake, "build"], cwd=fresh, check=False)
    print(f"Build exit code: {result.returncode}", flush=True)
    if inputs(book) != snapshot:
        raise RuntimeError("live build inputs changed during validation; snapshot is no longer current")
    print("Live inputs still match the validated snapshot; snapshot retained.", flush=True)
    return result.returncode


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError, StopIteration, subprocess.CalledProcessError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
