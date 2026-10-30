#!/usr/bin/env python3
"""Translate an aggregate Lean log to the snapshotted draft's line numbers."""
import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("pass_name")
args = parser.parse_args()
evidence = Path(__file__).resolve().parent
mapping = json.loads((evidence / (args.pass_name + "-source-map.json")).read_text())
log = (evidence / (args.pass_name + ".log")).read_text()

def translate(match):
    line = int(match.group(1))
    for source in mapping:
        if source["start"] <= line <= source["end"]:
            return f'{source["source"]}:{line-source["start"]+1}:{match.group(2)}'
    return match.group(0)

translated = re.sub(r"DevelopmentAggregate\.lean:(\d+):(\d+)", translate, log)
(evidence / (args.pass_name + "-mapped.log")).write_text(translated)
print(translated)
