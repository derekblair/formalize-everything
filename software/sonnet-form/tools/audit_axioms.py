#!/usr/bin/env python3
"""Audit every project theorem with Lean #print axioms, after lake build.

No native evaluation is accepted as a proof; source scan additionally bans
proof holes, axiom declarations, native_decide, and unsafe definitions.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true', help='record deterministic audit result in verification/')
    args = parser.parse_args()
    theorems = []
    for path in sorted((ROOT / 'SonnetForm').glob('*.lean')):
        source = path.read_text()
        # The faithful poem strings themselves contain words such as "sorry".
        # Exclude string literals before inspecting executable Lean tokens.
        without_strings = re.sub(r'"(?:\\.|[^"\\])*"', '""', source)
        without_comments = re.sub(r'/-.*?-/', '', without_strings, flags=re.S)
        without_comments = re.sub(r'--[^\n]*', '', without_comments)
        forbidden = re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', without_comments)
        if forbidden:
            raise SystemExit(f'Forbidden Lean token {forbidden.group()} in {path}')
        theorems.extend('SonnetForm.' + name for name in re.findall(r'^theorem\s+(\w+)', source, re.M))
    assert theorems and len(theorems) == len(set(theorems)), 'theorem census invalid'
    driver = 'import SonnetForm\n' + '\n'.join('#print axioms ' + name for name in theorems) + '\n'
    with tempfile.NamedTemporaryFile('w', suffix='.lean', encoding='utf-8') as file:
        file.write(driver)
        file.flush()
        run = subprocess.run(['lake', 'env', 'lean', file.name], cwd=ROOT, text=True, capture_output=True)
    if run.returncode:
        raise SystemExit(run.stdout + run.stderr)
    findings = {}
    for name in theorems:
        empty = f"'{name}' does not depend on any axioms"
        if empty in run.stdout:
            findings[name] = []
            continue
        match = re.search(re.escape("'" + name + "' depends on axioms:") + r'\s*\[([^]]*)\]', run.stdout)
        if not match:
            raise SystemExit(f'No #print axioms answer for {name}:\n{run.stdout}')
        found = [x.strip() for x in match[1].split(',') if x.strip()]
        if set(found) - ALLOWED:
            raise SystemExit(f'Unapproved axioms for {name}: {found}')
        findings[name] = found
    used = sorted({axiom for xs in findings.values() for axiom in xs})
    result = {'theorems_audited': len(findings), 'method': 'Lean #print axioms for every theorem declared in SonnetForm/*.lean',
              'axioms_used': used, 'allowed_axioms': sorted(ALLOWED), 'forbidden_source_tokens': [],
              'per_theorem': findings}
    if args.write:
        (ROOT / 'verification').mkdir(exist_ok=True)
        (ROOT / 'verification/axiom-audit.json').write_text(json.dumps(result, indent=2) + '\n')
        (ROOT / 'verification/axiom-audit.txt').write_text(run.stdout)
    print(f'PASS: {len(findings)} theorems audited; axioms used: {used}; no prohibited source tokens')

if __name__ == '__main__':
    main()
