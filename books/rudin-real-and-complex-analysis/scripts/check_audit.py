#!/usr/bin/env python3
"""Exercise the real AuditA against isolated, minimal Lean fixture graphs.

Run from any directory with the book's pinned toolchain and dependency cache
already available:

    python3 books/rudin-real-and-complex-analysis/scripts/check_audit.py

The audits (AuditA, AuditE) and umbrella (RudinRCA) are copied unchanged.
Fixture cases use small stub chapters to test rejection behavior alongside a
clean stub baseline, and live_project compiles and audits a fresh copy of the
full live package source tree. Every case uses a fresh temporary package and
fresh project oleans. Only the existing dependency directory is shared, through
a symlink; no live source or live project build artifact is changed. No
dependency installer is invoked.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


PIN = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
CHAPTERS = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17)
MODULES = (
    *(f"RudinRCA/Chapter{chapter:02}" for chapter in CHAPTERS),
    "RudinRCA/AuditE",
    "RudinRCA",
)
LIVE_PROJECT_DECLARATIONS = 6142


@dataclass(frozen=True)
class Case:
    name: str
    injection: str = ""
    extra_source: bool = False
    live_sources: bool = False
    expected_declarations: int = len(CHAPTERS)
    expected: tuple[str, ...] = ()


CASES = (
    Case("clean_baseline"),
    Case("live_project", live_sources=True, expected_declarations=LIVE_PROJECT_DECLARATIONS),
    Case(
        "sorry_backed_declaration",
        "theorem RudinRCA.fixtureSorry : False := by sorry\n",
        expected=("depends on disallowed axiom sorryAx",),
    ),
    Case(
        "user_axiom",
        "axiom RudinRCA.fixtureUserAxiom : True\n",
        expected=("Project declares an axiom: RudinRCA.fixtureUserAxiom",),
    ),
    Case(
        "private_axiom_outside_namespace",
        "namespace OutsideBook\nprivate axiom hidden : True\nend OutsideBook\n",
        expected=("Project declares an axiom: _private.", "OutsideBook.hidden"),
    ),
    Case(
        "unimported_project_source",
        extra_source=True,
        expected=("source module Unimported", "not imported into the audited import graph"),
    ),
)


class Failure(Exception):
    pass


def invoke(lake: str, root: Path, args: list[str], timeout: float) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            [lake, "env", "lean", *args],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise Failure(f"command timed out in fixture {root.name}: {args}") from exc


def collect_live_snapshot(book: Path, base_snapshot: dict[str, bytes]) -> dict[str, bytes]:
    live = dict(base_snapshot)
    for directory, children, files in os.walk(book):
        children[:] = [name for name in children if name != ".lake"]
        for name in files:
            if name.endswith(".lean"):
                rel = str((Path(directory) / name).relative_to(book))
                live[rel] = (book / rel).read_bytes()
    return live


def write_fixture(
    root: Path,
    snapshot: dict[str, bytes],
    live_snapshot: dict[str, bytes],
    packages: Path,
    case: Case,
) -> None:
    root.mkdir()
    sources = live_snapshot if case.live_sources else snapshot
    for name, content in sources.items():
        destination = root / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
    (root / ".lake").mkdir()
    (root / ".lake" / "packages").symlink_to(packages, target_is_directory=True)
    if not case.live_sources:
        for chapter in CHAPTERS:
            source = f"theorem RudinRCA.fixtureChapter{chapter} : True := True.intro\n"
            if chapter == 1:
                source += case.injection
            (root / "RudinRCA" / f"Chapter{chapter:02}.lean").write_text(source)
    if case.extra_source:
        # Deliberately outside RudinRCA/: ownership is the source tree, not a prefix.
        (root / "Unimported.lean").write_text(
            "theorem OutsideBook.unimported : True := True.intro\n"
        )


def run_case(lake: str, root: Path, case: Case, timeout: float) -> None:
    output_root = root / ".lake" / "build" / "lib" / "lean"
    # Compile every project import explicitly. The empty, per-case output tree
    # prevents a successful audit of stale oleans from masquerading as rejection.
    for module in MODULES:
        output = output_root / f"{module}.olean"
        output.parent.mkdir(parents=True, exist_ok=True)
        result = invoke(lake, root, ["-o", str(output), f"{module}.lean"], timeout)
        if result.returncode != 0:
            raise Failure(
                f"{case.name}: fixture compilation failed before the audit ({module}); "
                f"exit {result.returncode}\n{result.stdout}"
            )
        if not output.is_file():
            raise Failure(f"{case.name}: compiler did not produce {output}")
    result = invoke(lake, root, ["RudinRCA/AuditA.lean"], timeout)
    if not case.expected:
        expected_banner = f"Axiom audit passed for {case.expected_declarations} project declarations "
        if result.returncode != 0 or expected_banner not in result.stdout:
            raise Failure(f"{case.name}: audit did not pass nonvacuously; exit {result.returncode}\n{result.stdout}")
        lines = result.stdout.splitlines()
        start = next(i for i, line in enumerate(lines) if "Axiom audit passed" in line)
        diagnostic = " ".join(line.strip() for line in lines[start:] if line.strip())
        print(f"PASS {case.name}: exit 0; {diagnostic}", flush=True)
        return
    if result.returncode == 0:
        raise Failure(f"{case.name}: audit incorrectly accepted the fixture\n{result.stdout}")
    if any(fragment not in result.stdout for fragment in case.expected):
        raise Failure(
            f"{case.name}: audit failed for an unexpected reason; exit {result.returncode}\n{result.stdout}"
        )
    diagnostic = next(line for line in result.stdout.splitlines() if case.expected[0] in line)
    print(f"PASS {case.name}: exit {result.returncode}; {diagnostic}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=120, help="maximum seconds per Lean invocation")
    args = parser.parse_args()
    book = Path(__file__).resolve().parents[1]
    packages = (book / ".lake" / "packages").resolve()
    lake = shutil.which("lake")
    if lake is None:
        raise Failure("lake is not on PATH; this harness does not install it")
    snapshot_names = (
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "RudinRCA.lean",
        "RudinRCA/AuditA.lean",
        "RudinRCA/AuditE.lean",
    )
    snapshot = {name: (book / name).read_bytes() for name in snapshot_names}
    live_snapshot = collect_live_snapshot(book, snapshot)
    manifest = json.loads(snapshot["lake-manifest.json"])
    mathlib = next((package for package in manifest["packages"] if package["name"] == "mathlib"), None)
    if mathlib is None or mathlib["rev"] != PIN or snapshot["lean-toolchain"].decode().strip() != TOOLCHAIN:
        raise Failure("book pins differ from the required toolchain/Mathlib revision")
    if not (packages / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").is_file():
        raise Failure("pinned Mathlib oleans are absent; prepare the dependency cache before running")
    with tempfile.TemporaryDirectory(prefix="rca-audit-regression-") as temporary:
        parent = Path(temporary)
        for case in CASES:
            root = parent / case.name
            write_fixture(root, snapshot, live_snapshot, packages, case)
            run_case(lake, root, case, args.timeout)
    print(
        f"PASS: 1 stub baseline ({len(CHAPTERS)} declarations), "
        f"1 live-project audit ({LIVE_PROJECT_DECLARATIONS} declarations), "
        "and 4 expected audit rejections; live sources untouched.",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (Failure, OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        sys.exit(1)
