#!/usr/bin/env python3
"""Build the book into fresh outputs without deleting any preserved work.

Uses the original sources, manifest, toolchain, and pinned dependency cache.
The temporary Lake configuration differs only in its package buildDir.
All temporary files and the complete build log are retained for inspection.
"""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib


book = Path(__file__).resolve().parents[1]
config_text = (book / "lakefile.toml").read_text()
config = tomllib.loads(config_text)
assert "buildDir" not in config, "Inspect the existing buildDir before overriding it"
assert (book / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.34.1"
pin = "d13f23b723b8a846827a245b89c10fc7d3f11612"
assert next(p for p in config["require"] if p["name"] == "mathlib")["rev"] == pin
assert subprocess.check_output(
    ["git", "-C", str(book / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
    text=True,
).strip() == pin

run = Path(tempfile.mkdtemp(prefix="rca-e-clean-build-"))
build_dir = run / "build"
assert not build_dir.exists()
temporary_config = run / "lakefile.toml"
temporary_config.write_text(f"buildDir = {json.dumps(str(build_dir))}\n" + config_text)
inputs = [book / "lakefile.toml", book / "lake-manifest.json", book / "lean-toolchain",
          book / "RudinRCA.lean", *sorted((book / "RudinRCA").glob("*.lean"))]
hashes = {str(p.relative_to(book)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
(run / "input-sha256.json").write_text(json.dumps(hashes, indent=2) + "\n")
command = ["lake", "--no-cache", "-f", str(temporary_config), "--wfail", "build"]
print(f"Fresh build output: {build_dir}", flush=True)
print(f"Evidence directory: {run}", flush=True)
print("Command: " + " ".join(command), flush=True)
with (run / "build.log").open("w") as log:
    process = subprocess.Popen(command, cwd=book, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="", flush=True)
        log.write(line)
    status = process.wait()
unchanged = all(hashlib.sha256(p.read_bytes()).hexdigest() == hashes[str(p.relative_to(book))]
                for p in inputs)
result = {"command": command, "cwd": str(book), "exit_code": status,
          "inputs_unchanged": unchanged, "fresh_build_dir": str(build_dir)}
(run / "result.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)
sys.exit(status if status else (0 if unchanged else 1))
