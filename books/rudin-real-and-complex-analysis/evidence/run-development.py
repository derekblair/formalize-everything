#!/usr/bin/env python3
"""Record one serialized development check; never the clean-slate chapter gate."""
import argparse
import datetime
import hashlib
import json
import subprocess
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("pass_name")
parser.add_argument("--load-snapshot")
parser.add_argument("--save-header")
args = parser.parse_args()
book = Path(__file__).resolve().parent.parent
evidence = book / "evidence"
command = ["lake", "env", "lean", "-j1"]
if args.load_snapshot:
    command.append("--incr-load=" + args.load_snapshot)
if args.save_header:
    command.append("--incr-header-save=" + args.save_header)
command.append("DevelopmentAggregate.lean")
record = {
    "kind": "development_only",
    "command": command,
    "source_sha256": hashlib.sha256((book / command[-1]).read_bytes()).hexdigest(),
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "exit_code": None,
}
record_path = evidence / (args.pass_name + "-run.json")
record_path.write_text(json.dumps(record, indent=2) + "\n")
started = time.monotonic()
with (evidence / (args.pass_name + ".log")).open("w") as log:
    result = subprocess.run(command, cwd=book, stdout=log, stderr=subprocess.STDOUT)
record.update(
    finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    elapsed_seconds=round(time.monotonic() - started, 3),
    exit_code=result.returncode,
)
record_path.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record), flush=True)
raise SystemExit(result.returncode)
