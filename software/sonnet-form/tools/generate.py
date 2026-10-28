#!/usr/bin/env python3
"""Generate annotated Lean data and expectations; Lean independently checks every row.

All lexical choices are context-free. This Python mirror is NOT a proof;
SonnetForm/Audit*.lean prove its entire output with kernel `decide`.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from pronunciations import resolve, tokenize

ROOT = Path(__file__).resolve().parents[1]
SCHEME = [0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 6]
IAMB = [False, True] * 5
ELIDABLE = {'heaven', 'heavens', "heaven's", 'power', 'powers', "power's",
            'flower', 'flowers', "flower's", 'hour', 'hours', "hour's", 'our'}
LICENSES = [('initialTrochaicInversion', 'INITIAL_TROCHAIC_INVERSION'),
            ('feminineEnding', 'FEMININE_ENDING'),
            ('pyrrhicSubstitution', 'PYRRHIC_SUBSTITUTION'),
            ('spondaicSubstitution', 'SPONDAIC_SUBSTITUTION'),
            ('unstressedElision', 'UNSTRESSED_ELISION')]


def realize(masks):
    return [bool(i % 2) if value is None else value for i, value in enumerate(masks)]


def scans(masks, eligible):
    if not masks:
        return []
    result = [{'stress': realize(masks), 'elision': None}]
    for index in eligible:
        if 0 <= index < len(masks) and masks[index] is False:
            remaining = realize(masks[:index] + masks[index + 1:])
            result.append({'stress': remaining[:index] + [False] + remaining[index:], 'elision': index})
    return result


def scan_verdict(scan):
    raw, elision = scan['stress'], scan['elision']
    strict = elision is None and raw == IAMB
    valid_elision = elision is None or (0 <= elision < len(raw) and not raw[elision])
    xs = raw if elision is None else raw[:elision] + raw[elision + 1:]
    feminine = len(xs) == 11 and not xs[-1]
    core = xs[:10] if feminine else xs
    feet = list(zip(core[::2], core[1::2]))
    licensed = (valid_elision and len(core) == 10 and
                all(pair != (True, False) or i == 0 for i, pair in enumerate(feet)) and
                sum(pair != (False, True) for pair in feet) <= 2)
    flags = [bool(feet) and feet[0] == (True, False), feminine,
             (False, False) in feet, (True, True) in feet, elision is not None]
    licenses = [name for (_, name), flag in zip(LICENSES, flags) if flag] if licensed else []
    return strict, licensed, licenses


def rhyme_class(phones):
    stressed = [i for i, p in enumerate(phones) if p[-1:] in ('1', '2')]
    vowels = [i for i, p in enumerate(phones) if p[-1:] in ('0', '1', '2')]
    if not vowels:
        return None
    start = stressed[-1] if stressed else vowels[-1]
    return ' '.join(re.sub('[012]', '', p) for p in phones[start:])


def annotate(text):
    words = []
    masks, eligible, unknown = [], [], []
    for token in tokenize(text):
        answer = resolve(token)
        if answer is None:
            unknown.append(token)
            words.append({'token': token, 'phonemes': None, 'derivation': 'UNRESOLVED'})
            continue
        phones, derivation = answer
        stress = [p[-1] != '0' for p in phones if p[-1:] in ('0', '1', '2')]
        word_masks = [None] if len(stress) == 1 else stress
        normalized = token.lower().replace('’', "'").strip("'")
        if normalized in ELIDABLE and len(stress) == 2 and stress[1] is False:
            eligible.append(len(masks) + 1)
        words.append({'token': token, 'phonemes': phones, 'derivation': derivation,
                      'syllables': len(stress), 'masks': word_masks})
        masks += word_masks
    # An incomplete word annotation must not silently become an omitted word.
    candidates = scans(masks, eligible) if not unknown else []
    end = words[-1]['phonemes'] if words else None
    rhyme = rhyme_class(end) if end else None
    checks = [scan_verdict(s) for s in candidates]
    first = next((i for i, c in enumerate(checks) if c[1]), None)
    return {'text': text, 'words': words, 'masks': masks if not unknown else [],
            'eligible_elisions': eligible if not unknown else [], 'unknown': unknown,
            'rhyme': rhyme, 'scans': candidates,
            'strict': any(c[0] for c in checks), 'licensed': first is not None,
            'licenses': checks[first][2] if first is not None else [],
            'selected_scan': candidates[first] if first is not None else (candidates[0] if candidates else None)}


def boolstr(value):
    return 'true' if value else 'false'


def leanstr(value):
    return json.dumps(value, ensure_ascii=False)


def leanlist(items):
    return '[' + ', '.join(items) + ']'


def generate():
    raw = json.loads((ROOT / 'data/sonnets.json').read_text())
    annotated = []
    for sonnet in raw:
        lines = [annotate(line) for line in sonnet['lines']]
        rs = [line['rhyme'] for line in lines]
        rhyme = len(lines) == 14 and all(rs) and all((rs[i] == rs[j]) == (SCHEME[i] == SCHEME[j]) for i in range(14) for j in range(14))
        annotated.append({'number': sonnet['number'], 'lines': lines,
                          'line_count': len(lines) == 14, 'rhyme': bool(rhyme),
                          'strict_meter': bool(lines) and all(l['strict'] for l in lines),
                          'licensed_meter': bool(lines) and all(l['licensed'] for l in lines)})
    counts = {'sonnets': len(annotated), 'lines': sum(len(s['lines']) for s in annotated)}
    for key in ['line_count', 'rhyme', 'strict_meter', 'licensed_meter']:
        counts[key] = {'pass': sum(s[key] for s in annotated), 'fail': sum(not s[key] for s in annotated)}
    for key in ['strict', 'licensed']:
        counts['line_' + key] = {'pass': sum(l[key] for s in annotated for l in s['lines']),
                                 'fail': sum(not l[key] for s in annotated for l in s['lines'])}
    counts['unresolved_lines'] = sum(bool(l['unknown']) for s in annotated for l in s['lines'])
    counts['licenses'] = {name: sum(name in l['licenses'] for s in annotated for l in s['lines']) for _, name in LICENSES}
    outputs = {'data/annotations.json': json.dumps(annotated, ensure_ascii=False, indent=2) + '\n',
               'data/conformance-summary.json': json.dumps(counts, indent=2) + '\n'}
    header = ('/- Generated by tools/generate.py; DO NOT edit.\n'
              'Text: Project Gutenberg eBook1041, retrieved2026-10-27; see PROVENANCE.md.\n'
              'Lexical/stress decisions: see PRONUNCIATION.md and SPEC.md. -/\n')
    corpus = [header, 'import SonnetForm.Phonology\n\nnamespace SonnetForm\n']
    for s in annotated:
        corpus.append(f'\ndef sonnet{s["number"]:03} : Sonnet :=\n  ⟨{s["number"]}, [\n')
        ll = []
        for l in s['lines']:
            rhyme = '(some ' + leanstr(l['rhyme']) + ')' if l['rhyme'] else 'none'
            masks = leanlist(['none' if v is None else 'some ' + boolstr(v) for v in l['masks']])
            ll.append(f'    lineFromMasks {leanstr(l["text"])} {rhyme} {masks} {leanlist(map(str, l["eligible_elisions"]))}')
        corpus.append(',\n'.join(ll) + '\n  ]⟩\n')
    corpus.append('\ndef corpus : List Sonnet := ' + leanlist(f'sonnet{s["number"]:03}' for s in annotated) + '\n\nend SonnetForm\n')
    outputs['SonnetForm/Corpus.lean'] = ''.join(corpus)
    license_map = {name: ctor for ctor, name in LICENSES}
    theorem_names = []
    chunks = []
    for start in range(0, len(annotated), 14):
        part = annotated[start:start + 14]
        chunk_name = f'AuditPart{start // 14 + 1:02}'
        chunks.append(chunk_name)
        contents = [header, 'import SonnetForm.AuditTypes\n\nnamespace SonnetForm\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
        for s in part:
            n = s['number']
            v = ', '.join([str(n)] + [boolstr(s[k]) for k in ['line_count', 'rhyme', 'strict_meter', 'licensed_meter']])
            ds = leanlist('⟨' + ', '.join([boolstr(l['strict']), boolstr(l['licensed']), leanlist('.' + license_map[name] for name in l['licenses'])]) + '⟩' for l in s['lines'])
            contents.append(f'\ndef expected{n:03} : AuditRow := ⟨⟨{v}⟩, {ds}⟩\n')
            name = f'sonnet{n:03}_checked'
            theorem_names.append(name)
            contents.append(f'theorem {name} : inspectSonnet sonnet{n:03} = expected{n:03} := by decide\n')
        contents.append('\nend SonnetForm\n')
        outputs[f'SonnetForm/{chunk_name}.lean'] = ''.join(contents)
    audit = [header] + [f'import SonnetForm.{c}\n' for c in chunks]
    audit += ['\nnamespace SonnetForm\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n',
              '\ndef fullTable : List AuditRow := corpus.map inspectSonnet\n',
              '\ndef expectedTable : List AuditRow := ' + leanlist(f'expected{s["number"]:03}' for s in annotated) + '\n',
              '\ntheorem full_table_checked : fullTable = expectedTable := by\n  simp only [fullTable, expectedTable, corpus, List.map_cons, List.map_nil,\n    ' + ',\n    '.join(theorem_names) + ']\n',
              '\ntheorem corpus_complete : corpus.length = 154 ∧ (corpus.map (·.number)) = List.range\' 1 154 := by decide\n',
              '\ntheorem calibration_99 : sonnet099.lines.length = 15 ∧ lineCount sonnet099 = false := by decide\n',
              '\ntheorem calibration_126 : sonnet126.lines.length = 12 ∧ lineCount sonnet126 = false := by decide\n',
              '\ntheorem calibration_145 : sonnet145.lines.length = 14 ∧ meterLicensed sonnet145 = false ∧\n    sonnet145.lines.all (fun l => l.scans.all (fun s => s.stress.length == 8)) = true := by decide\n',
              '\nend SonnetForm\n']
    outputs['SonnetForm/Audit.lean'] = ''.join(audit)
    outputs['DEVIATIONS.md'] = catalogue(annotated, counts)
    return outputs, counts


def catalogue(sonnets, counts):
    text = ['# Conformance and deviation catalogue\n\n',
            'Generated by `python3 tools/generate.py`; checked by `--check` and the kernel theorems in `SonnetForm/Audit.lean`. ',
            'Every row and every line diagnostic below is encoded in the expected audit rows and proved equal to the Lean predicates.\n\n',
            '**ANOMALOUS means failure of this explicitly bounded annotation model. It is not a claim that Shakespeare wrote bad verse.** ',
            'Modern American rhyme, first dictionary pronunciations, flexible monosyllabic stress, and a two-substitution budget produce additional failures. ',
            'See [SPEC.md](SPEC.md), [PRONUNCIATION.md](PRONUNCIATION.md), [PROVENANCE.md](PROVENANCE.md), and the separately measured [validation sample](VALIDATION.md).\n\n',
            '## Summary\n\n| Component | Pass | Fail |\n|---|---:|---:|\n']
    for key in ['line_count', 'rhyme', 'strict_meter', 'licensed_meter', 'line_strict', 'line_licensed']:
        text.append(f'| {key} | {counts[key]["pass"]} | {counts[key]["fail"]} |\n')
    text.append(f'\n{counts["sonnets"]} sonnets, {counts["lines"]} lines; {counts["unresolved_lines"]} lines have unresolved pronunciation tokens.\n\n')
    text.append('License usage counts lines using each rule (rules can co-occur): ' + '; '.join(f'{k}={v}' for k,v in counts['licenses'].items()) + '.\n\n')
    text.append('## All 154 verdicts\n\nPASS means the component passes strictly; LICENSED means strict meter fails but the named meter rules succeed on every line. Rhyme and line count have no repair licenses.\n\n| Sonnet | Lines | Line count | Rhyme | Meter |\n|---:|---:|---|---|---|\n')
    for s in sonnets:
        meter = 'PASS' if s['strict_meter'] else 'LICENSED' if s['licensed_meter'] else 'ANOMALOUS'
        text.append(f'| {s["number"]} | {len(s["lines"])} | {"PASS" if s["line_count"] else "ANOMALOUS"} | {"PASS" if s["rhyme"] else "ANOMALOUS"} | {meter} |\n')
    text.append('\n## Full anomaly lists\n\n')
    for key in ['line_count', 'rhyme', 'licensed_meter']:
        text.append(f'- {key}: ' + ', '.join(str(s['number']) for s in sonnets if not s[key]) + '.\n')
    text.append('\n## Every failing component and line\n\nLine numbers are one-based. Each strict meter failure is listed, including licensed ones inside a sonnet with other anomalous lines. Stress notation: `u` weak, `S` strong; the displayed stress is before any explicitly indexed elision.\n')
    for s in sonnets:
        failed = not all(s[k] for k in ['line_count', 'rhyme', 'strict_meter'])
        if not failed:
            continue
        text.append(f'\n### Sonnet {s["number"]}\n\n')
        if not s['line_count']:
            text.append(f'- Line count: **ANOMALOUS**, {len(s["lines"])} rather than14.\n')
        if not s['rhyme']:
            rs = [l['rhyme'] for l in s['lines']]
            reasons = []
            if len(rs) != 14:
                reasons.append('requires exactly14 line endings')
            else:
                for i in range(14):
                    for j in range(i+1,14):
                        if (rs[i] == rs[j]) != (SCHEME[i] == SCHEME[j]):
                            reasons.append(f'{i+1}/{j+1}: `{rs[i]}` / `{rs[j]}` ({"expected same" if SCHEME[i] == SCHEME[j] else "expected distinct"})')
                reasons += [f'{i+1}: missing rhyme class' for i,r in enumerate(rs) if not r]
            text.append('- Rhyme: **ANOMALOUS**; ' + '; '.join(reasons) + '.\n')
        if not s['strict_meter']:
            text.append('- Meter: **' + ('LICENSED' if s['licensed_meter'] else 'ANOMALOUS') + '** at poem level.\n\n')
            text.append('| Line | Strict-meter failure classification | Evidence |\n|---:|---|---|\n')
            for i,l in enumerate(s['lines'],1):
                if l['strict']:
                    continue
                scan = l['selected_scan']
                evidence = 'unresolved: ' + ', '.join(l['unknown']) if scan is None else '`' + ''.join('S' if v else 'u' for v in scan['stress']) + '` (' + str(len(scan['stress'])) + ' syllables)'
                if scan and scan['elision'] is not None:
                    evidence += f'; elide syllable {scan["elision"]+1}'
                category = 'LICENSED: ' + ', '.join(l['licenses']) if l['licensed'] else 'ANOMALOUS'
                text.append(f'| {i} | {category} | {evidence} |\n')
    return ''.join(text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--corpus-only', action='store_true', help='emit only annotated corpus and evidence before audit integration')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'data/cmudict-source.json').read_text())
    for name, entry in manifest['files'].items():
        assert hashlib.sha256((ROOT / 'data' / name).read_bytes()).hexdigest() == entry['sha256'], name
    outputs, counts = generate()
    if args.corpus_only:
        outputs = {k:v for k,v in outputs.items() if k.startswith('data/') or k == 'SonnetForm/Corpus.lean'}
    for relative, text in outputs.items():
        path = ROOT / relative
        if args.check:
            assert path.read_text(encoding='utf-8') == text, f'stale generated file: {relative}'
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf-8')
    print(json.dumps(counts, indent=2))
    print(('CHECKED' if args.check else 'GENERATED') + f' {len(outputs)} files')

if __name__ == '__main__':
    main()
