"""Validate and render external scholarship; this does not set rhyme verdicts.

The review is bound to unchanged corpus strings and an explicit modern baseline.
Its claims are external evidence, never inputs to the Lean phonology or checker.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path

from pronunciations import tokenize

ROOT = Path(__file__).resolve().parents[1]
SCHEME = [0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 6]
# Derived from the original rebased annotations, not from the review JSON.
# Only number/class vectors for the complete failed set are projected, so the
# baseline can be checked in a source archive without Git or a duplicate corpus.
BASELINE_COMMIT = 'cfdc1c78e8f12deb451df8ae8c2425a8de159a38'
BASELINE_ANNOTATIONS_SHA256 = '045f381f66c977bb07fbe399506992c60000c5e1da860e71f0db1e651215f521'
BASELINE_PROJECTION_SHA256 = '4ea40ee1c739caf573e471778f89caabac90256941b609db0e41c74a64370699'


def sha(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def load_review():
    data = json.loads((ROOT / 'data/historical-rhyme-review.json').read_text())
    raw_bytes = (ROOT / 'data/sonnets.json').read_bytes()
    raw = {s['number']: s['lines'] for s in json.loads(raw_bytes)}
    assert data['schema_version'] == 1
    assert data['baseline']['git_commit'] == BASELINE_COMMIT
    assert data['baseline']['annotations_sha256'] == BASELINE_ANNOTATIONS_SHA256
    assert hashlib.sha256(raw_bytes).hexdigest() == data['baseline']['corpus_sha256']
    assert len(data['sonnets']) == data['baseline']['failed_sonnets'] == 133
    numbers = [s['number'] for s in data['sonnets']]
    assert numbers == sorted(set(numbers))
    projection = [{'number': s['number'], 'classes': s['baseline_classes']} for s in data['sonnets']]
    assert sha(json.dumps(projection, sort_keys=True, separators=(',', ':'))) == BASELINE_PROJECTION_SHA256
    evidence_ids = {e['id'] for e in data['evidence']}
    assert len(evidence_ids) == len(data['evidence'])
    constraint_ids = set()
    for sonnet in data['sonnets']:
        lines = raw[sonnet['number']]
        assert sonnet['baseline_rhyme_pass'] is False
        assert sonnet['baseline_line_count'] == len(lines)
        assert sonnet['source_text_sha256'] == sha('\n'.join(lines) + '\n')
        assert sonnet['baseline_ending_words'] == [tokenize(line)[-1] for line in lines]
        classes = sonnet['baseline_classes']
        assert len(classes) == len(lines) and all(classes)
        for kind, same in [('unequal_pairs', True), ('cross_class_collisions', False)]:
            expected = set()
            if len(lines) == 14:
                expected = {(i + 1, j + 1) for i in range(14) for j in range(i + 1, 14)
                            if (SCHEME[i] == SCHEME[j]) == same and
                            (classes[i] == classes[j]) != same}
            rows = sonnet[kind]
            assert {tuple(p['lines']) for p in rows} == expected
            assert len(rows) == len(expected)
            for pair in rows:
                assert pair['id'] not in constraint_ids
                constraint_ids.add(pair['id'])
                assert pair['status'] in data['status_definitions']
                assert set(pair['evidence_ids']) <= evidence_ids
                i, j = (v - 1 for v in pair['lines'])
                assert pair['words'] == [tokenize(lines[k])[-1] for k in (i, j)]
                assert pair['line_sha256'] == [sha(lines[k]) for k in (i, j)]
                assert pair['baseline_classes'] == [classes[k] for k in (i, j)]
                if pair['status'] == 'same_token_obstruction':
                    normalize = lambda w: w.lower().replace('’', "'").strip("'")
                    assert normalize(pair['words'][0]) == normalize(pair['words'][1])
        if len(lines) == 14:
            assert sonnet['unequal_pairs'] or sonnet['cross_class_collisions']
            assert sonnet['structure'] is None
        else:
            assert sonnet['structure']['line_count'] == len(lines)
            assert set(sonnet['structure']['evidence_ids']) <= evidence_ids
        local_ids = {p['id'] for key in ('unequal_pairs', 'cross_class_collisions')
                     for p in sonnet[key]}
        expected_open = {p['id'] for key in ('unequal_pairs', 'cross_class_collisions')
                         for p in sonnet[key] if p['open_question']}
        assert set(sonnet['open_constraint_ids']) == expected_open <= local_ids
        obstruction = any(p['status'] == 'same_token_obstruction'
                          for p in sonnet['cross_class_collisions'])
        assert sonnet['context_free_distinctness_obstruction'] == obstruction
        whole_status = ('excluded_by_line_count' if len(lines) != 14 else
                        'impossible_under_context_free_exact_classes' if obstruction else
                        'not_established')
        assert sonnet['whole_historical_scheme_status'] == whole_status
        assessment = ('documented_non14_structure' if len(lines) != 14 else
                      'historical_evidence_incomplete' if expected_open else
                      'failed_pairs_supported_distinctness_obstructed' if obstruction else
                      'failed_pairs_supported_only')
        assert sonnet['assessment'] == assessment
    for key, count_key, status_key in [
        ('unequal_pairs', 'unequal_pair_constraints', 'unequal_pair_status_counts'),
        ('cross_class_collisions', 'cross_class_constraints', 'cross_class_status_counts')]:
        counts = Counter(p['status'] for s in data['sonnets'] for p in s[key])
        assert dict(counts) == data['summary'][status_key]
        assert sum(counts.values()) == data['summary'][count_key]
    assert data['summary']['reviewed_sonnets'] == len(numbers)
    assert data['summary']['sonnets_with_open_constraints'] == [
        s['number'] for s in data['sonnets'] if s['open_constraint_ids']]
    assert data['summary']['non14_sonnets'] == [
        s['number'] for s in data['sonnets'] if s['baseline_line_count'] != 14]
    assert data['summary']['sonnets_with_context_free_obstruction'] == [
        s['number'] for s in data['sonnets'] if s['context_free_distinctness_obstruction']]
    assert data['summary']['complete_historical_schemes_validated'] == 0
    assert data['scope']['full_historical_validation'] is False
    return data


def cell(text):
    return str(text).replace('|', '\\|').replace('\n', ' ')


def refs(ids, evidence):
    return ', '.join(f"[{key}]({evidence[key]['url']})" if evidence[key]['url'] else key
                     for key in ids)


def render_sources(data):
    text = ['\n## Historical evidence sources and limits\n\n',
            'The per-sonnet review below covers the **original 133 modern-model failures**. ',
            'It is external author-side scholarship review, not a kernel theorem or independent review. ',
            'Historical findings do not alter pronunciation lookup or any verdict. ',
            'Baseline constraints remain visible even when a later lexical annotation changes a modern class. ',
            'See [HISTORICAL-RHYME.md](HISTORICAL-RHYME.md) and ',
            '[the full review data](data/historical-rhyme-review.json). ',
            '**No complete historical scheme has been validated.**\n\n']
    summary = data['summary']
    text.append(f"Inventory: {summary['reviewed_sonnets']} sonnets; "
                f"{summary['unequal_pair_constraints']} unequal intended pairs; "
                f"{summary['cross_class_constraints']} cross-class collisions; "
                '99/126 have non-fourteen-line structure.\n\n')
    for key in ['unequal_pair_status_counts', 'cross_class_status_counts']:
        text.append('; '.join(f'{status}={count}' for status, count in summary[key].items()) + '.\n\n')
    for e in data['evidence']:
        ref = f"[{e['id']}]({e['url']})" if e['url'] else e['id']
        text.append(f"- {ref}: {e['title']}. {e.get('locator', '')} {e['summary']} {e['limitations']}\n")
    text.append('\nStatus meanings:\n\n')
    for key, value in data['status_definitions'].items():
        text.append(f'- `{key}`: {value}\n')
    return ''.join(text)


def render_sonnet(review, current, evidence):
    text = [f"\nHistorical review: **{review['assessment']}**; whole historical scheme: ",
            f"**{review['whole_historical_scheme_status']}**.\n\n"]
    if review['structure']:
        s = review['structure']
        text.append(f"{s['finding']} {refs(s['evidence_ids'], evidence)}.\n")
    rows = review['unequal_pairs'] + review['cross_class_collisions']
    if rows:
        text.append('| Constraint / endings | Historical finding | Evidence | Current modern relation |\n'
                    '|---|---|---|---|\n')
    for pair in rows:
        i, j = pair['lines']
        same = SCHEME[i - 1] == SCHEME[j - 1]
        label = f"{pair['id']} ({'same' if same else 'distinct'}): " + '/'.join(pair['words'])
        finding = f"{pair['status']}: {pair['finding']}"
        if pair['open_question']:
            finding += ' Open: ' + pair['open_question']
        equal = current['lines'][i - 1]['rhyme'] == current['lines'][j - 1]['rhyme']
        text.append(f"| {cell(label)} | {cell(finding)} | {refs(pair['evidence_ids'], evidence)} | "
                    f"{'equal' if equal else 'different'} |\n")
    if review['open_constraint_ids']:
        text.append('\nOpen constraint IDs: ' + ', '.join(review['open_constraint_ids']) + '.\n')
    for remainder in review['open_remainder']:
        if remainder.startswith('WHOLE-SCHEME:'):
            text.append('\n' + remainder + '\n')
    return ''.join(text)
