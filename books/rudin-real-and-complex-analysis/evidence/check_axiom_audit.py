#!/usr/bin/env python3
"""Check a captured Lean #print axioms audit against the programme's allowlist.

Usage: python3 check_axiom_audit.py SOURCE.lean BUILD_LOG
Requires an explicit audit command for every theorem/lemma in the source and
an exact fully qualified record for every explicit audit command. Records from
other chapters do not inflate this chapter's count or satisfy its audits.
Disallowed axioms and conflicting duplicate records anywhere in the log fail.
This checks evidence, not Lean itself; the logged build must separately exit 0.
"""
import re
import sys
from pathlib import Path


def code_only(source):
    """Blank comments and string contents while preserving line positions."""
    out, i, depth = [], 0, 0
    in_string = False
    while i < len(source):
        pair, char = source[i:i + 2], source[i]
        if depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
                continue
            if pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
                continue
            out.append('\n' if char == '\n' else ' ')
        elif in_string:
            if char == '\\' and i + 1 < len(source):
                out.extend('  ')
                i += 2
                continue
            if char == '"':
                in_string = False
            out.append('\n' if char == '\n' else ' ')
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
            continue
        elif pair == '--':
            end = source.find('\n', i)
            if end < 0:
                end = len(source)
            out.extend(' ' * (end - i))
            i = end
            continue
        elif char == '"':
            in_string = True
            out.append(' ')
        else:
            out.append(char)
        i += 1
    return ''.join(out)


def source_inventory(source):
    scopes, names, audits, errors = [], [], [], []
    for line_number, line in enumerate(code_only(source).splitlines(), 1):
        namespace = re.match(r'^\s*namespace\s+(\S+)\s*$', line)
        section = re.match(r'^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', line)
        end = re.match(r'^\s*end(?:\s+(\S+))?\s*$', line)
        if namespace:
            scopes.append(('namespace', namespace[1]))
        elif section:
            scopes.append(('section', section[1]))
        elif end:
            if not scopes:
                errors.append(f'Unmatched end at line {line_number}')
            else:
                kind, name = scopes.pop()
                if end[1] and end[1] != name:
                    errors.append(f'End scope mismatch at line {line_number}: {end[1]} versus {name}')
        declaration = re.match(
            r'^\s*(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
            r'(?:theorem|lemma)\s+([^\s:{(]+)', line)
        if declaration:
            name = declaration[1]
            if name.startswith('_root_.'):
                names.append(name.removeprefix('_root_.'))
            else:
                prefix = '.'.join(name for kind, name in scopes if kind == 'namespace')
                names.append(f'{prefix}.{name}' if prefix else name)
        audit = re.match(r'^\s*#print\s+axioms\s+(\S+)\s*$', line)
        if audit:
            audits.append(audit[1].removeprefix('_root_.'))
    if scopes:
        errors.append(f'Unclosed source scopes: {scopes}')
    return names, audits, errors


def main():
    source = Path(sys.argv[1]).read_text()
    log = Path(sys.argv[2]).read_text()
    names, audit_commands, source_errors = source_inventory(source)
    expected = set(audit_commands)
    missing_commands = sorted(set(names) - expected)
    duplicate_declarations = sorted(name for name in set(names) if names.count(name) > 1)
    records, variants = {}, {}
    entries = [(name, set(filter(None, re.split(r'[,\s]+', axioms))))
               for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log)]
    entries += [(name, set()) for name in
                re.findall(r"'([^']+)' does not depend on any axioms", log)]
    for name, axioms in entries:
        variants.setdefault(name, set()).add(tuple(sorted(axioms)))
        # Retain the union so an unsafe duplicate cannot be hidden by an allowed one.
        records.setdefault(name, set()).update(axioms)
    conflicts = {name: values for name, values in variants.items() if len(values) > 1}
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    missing = sorted(expected - records.keys())
    bad = {name: sorted(axioms - allowed) for name, axioms in sorted(records.items())
           if axioms - allowed}
    scoped = {name: records[name] for name in expected if name in records}
    print(f'Theorem/lemma declarations: {len(names)}; audit records: {len(scoped)}')
    print(f'Missing records: {missing}')
    print(f'Disallowed axioms: {bad}')
    print(f'Observed axiom union: {sorted(set().union(*scoped.values()))}')
    if missing_commands:
        print(f'Missing audit commands: {missing_commands}')
    if duplicate_declarations:
        print(f'Duplicate theorem/lemma declarations: {duplicate_declarations}')
    if conflicts:
        print(f'Conflicting duplicate records: {dict(sorted((n, sorted(v)) for n, v in conflicts.items()))}')
    if source_errors:
        print(f'Source inventory errors: {source_errors}')
    return bool(missing or bad or missing_commands or duplicate_declarations or conflicts or source_errors)


if __name__ == '__main__':
    sys.exit(main())
