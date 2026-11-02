#!/usr/bin/env python3
"""Build/check the independently authored hand-scansion fixture and comparison.

The TSV is the hand-authored source, not generated from pronunciation annotations.
No network or third-party packages are used. See VALIDATION.md for what this
author-agent exercise can and cannot establish.
"""

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SAMPLE = [2, 18, 19, 20, 29, 55, 60, 73, 116, 130, 145]


def hand_fixture():
    source = ROOT / "data/validation-scans.tsv"
    corpus = {s["number"]: s["lines"] for s in json.loads(
        (ROOT / "data/sonnets.json").read_text(encoding="utf-8"))}
    rows = []
    for raw in source.read_text(encoding="utf-8").splitlines():
        if not raw or raw.startswith("#"):
            continue
        key, feet, note = raw.split("\t")
        number, line = map(int, key.split("."))
        syllables = feet.replace("|", " ").split()
        assert all(s.isupper() or s.islower() for s in syllables), key
        stress = "".join("S" if s.isupper() else "u" for s in syllables)
        assert len(stress) in ([8] if number == 145 else [10, 11]), key
        rows.append({
            "number": number,
            "line": line,
            "text": corpus[number][line - 1],
            "syllables": len(stress),
            "stress": stress,
            "hand_scansion": feet,
            "intended_family": "tetrameter" if number == 145 else "pentameter",
            "note": note,
        })
    expected_keys = [(number, line) for number in SAMPLE for line in range(1, 15)]
    assert [(r["number"], r["line"]) for r in rows] == expected_keys
    return {
        "authors": "Codex author-agent, manual literary reading; not independent human review",
        "annotation_method": "Syllable-by-syllable reading with rhetorical stress; one defensible reading per line, not all possible performances",
        "sample_sonnets": SAMPLE,
        "sample_lines": len(rows),
        "hand_source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "annotation_blinding": "Hand TSV authored before examining machine annotation output; no retuning to increase agreement",
        "sources": [
            "https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/reading-shakespeares-language-sonnets/",
            "https://www.folger.edu/explore/write-a-sonnet/",
            "https://github.com/cmusphinx/cmudict",
        ],
        "lines": rows,
    }


def write_or_check(path, text, check):
    if check:
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            raise SystemExit(f"STALE: {path.relative_to(ROOT)}")
    else:
        path.write_text(text, encoding="utf-8")


def stress_text(values):
    return "".join("S" if value else "u" for value in values)


def after_elision(scan):
    values, index = scan["stress"], scan["elision"]
    return values if index is None else values[:index] + values[index + 1:]


METRICS = [
    ("baseline_syllables", "Baseline syllable count"),
    ("candidate_syllables", "Any supplied reading: syllable count"),
    ("baseline_stress", "Baseline complete stress sequence"),
    ("candidate_stress", "Any supplied reading: complete stress sequence"),
    ("selected_stress", "Selected reading: complete stress sequence"),
    ("fixed_stress_compatible", "Fixed lexical stresses compatible with hand reading"),
    ("meter_family", "Licensed-meter verdict versus hand verse family"),
]


def compare(fixture):
    path = ROOT / "data/annotations.json"
    annotations = {s["number"]: s for s in json.loads(path.read_text(encoding="utf-8"))}
    rows = []
    for hand in fixture["lines"]:
        number, index = hand["number"], hand["line"]
        model = annotations[number]["lines"][index - 1]
        assert model["text"] == hand["text"], (number, index)
        candidates = [stress_text(after_elision(s)) for s in model["scans"]]
        baseline = candidates[0] if candidates else None
        selected = (stress_text(after_elision(model["selected_scan"]))
                    if model["selected_scan"] else None)
        compatible = False
        for scan in model["scans"]:
            masks = model["masks"]
            at = scan["elision"]
            if at is not None:
                masks = masks[:at] + masks[at + 1:]
            compatible |= (len(masks) == hand["syllables"] and
                           all(m is None or m == (s == "S")
                               for m, s in zip(masks, hand["stress"])))
        agreement = {
            "baseline_syllables": baseline is not None and len(baseline) == hand["syllables"],
            "candidate_syllables": any(len(s) == hand["syllables"] for s in candidates),
            "baseline_stress": baseline == hand["stress"],
            "candidate_stress": hand["stress"] in candidates,
            "selected_stress": selected == hand["stress"],
            "fixed_stress_compatible": compatible,
            "meter_family": model["licensed"] == (hand["intended_family"] == "pentameter"),
        }
        rows.append({
            "number": number, "line": index, "text": hand["text"],
            "hand_stress": hand["stress"], "hand_syllables": hand["syllables"],
            "baseline_stress": baseline, "candidate_stresses": candidates,
            "selected_stress": selected, "model_meter_licensed": model["licensed"],
            "model_licenses": model["licenses"], "agreement": agreement,
        })
    counts = {key: {"agree": sum(r["agreement"][key] for r in rows), "total": len(rows)}
              for key, _ in METRICS}
    sonnets = []
    for number in SAMPLE:
        subset = [r for r in rows if r["number"] == number]
        observed = annotations[number]["licensed_meter"]
        sonnets.append({
            "number": number, "lines": len(subset),
            "metrics": {key: sum(r["agreement"][key] for r in subset) for key, _ in METRICS},
            "expected_pentameter": number != 145,
            "observed_licensed_meter": observed,
            "poem_verdict_agrees": observed == (number != 145),
        })
    return {
        "hand_source_sha256": fixture["hand_source_sha256"],
        "annotations_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "counts": counts,
        "poem_verdict": {"agree": sum(s["poem_verdict_agrees"] for s in sonnets), "total": len(sonnets)},
        "sonnets": sonnets,
        "lines": rows,
    }


def report(fixture, result):
    text = [
        "# Scansion validation\n\n",
        "## Scope and authorship\n\n",
        "The sample comprises **11 complete sonnets, 154 lines**: 2, 18, 19, 20, 29, 55, 60, 73, 116, 130, and 145. ",
        "This is a **manual reading by a Codex author-agent**, not independent human or scholarly validation. ",
        "The syllable-by-syllable annotations in [data/validation-scans.tsv](data/validation-scans.tsv) were written before inspecting the machine annotation output. ",
        "They were not retuned to improve agreement. Each records one defensible performance, rather than asserting that poetry has a unique stress sequence. ",
        "Uppercase syllables are strong; lowercase syllables are weak; vertical bars group feet. The original edition text remains unchanged in the fixture.\n\n",
        "The selection is purposive, not random. It includes pyrrhic and spondaic substitutions (2), initial inversion (20.6, 29.5, 60.7), ",
        "feminine endings (all fourteen lines of 20), contractions, rhetorical interior inversions, and the tetrameter control (145). ",
        "The denominator includes every line of every sampled sonnet. [data/validation.json](data/validation.json) contains the complete hand fixture, ",
        "and [data/validation-results.json](data/validation-results.json) contains every machine comparison.\n\n",
        "## Method\n\n",
        "`python3 tools/validate_scansion.py` joins the frozen hand source to the exact corpus text and compares it with `data/annotations.json`. ",
        "`python3 tools/validate_scansion.py --check` rejects stale fixtures, results, or this document. This Python comparison is a reproducible validation measurement, ",
        "not a Lean proof that a reading is linguistically correct. The conformance verdicts it consumes are separately checked by the Lean audit.\n\n",
        "Syllable and stress comparisons apply the candidate's explicitly indexed elision but retain a feminine ending. ",
        "“Any supplied reading” means the finite baseline/elision candidates, not an unbounded search for a favorable reading. ",
        "“Selected” means the first licensed reading, or the baseline when none passes. Fixed-stress compatibility allows the supplied monosyllabic masks to take the hand stress, ",
        "but requires exact length and every fixed multisyllabic stress to agree. It is a sequence-level compatibility measurement; it does not certify word-by-word phonetics. ",
        "The meter-family comparison expects pentameter for the ten ordinary sonnets and rejects pentameter for every line of 145; ",
        "it does not require the preferred rhetorical scan itself to obey the spec's restricted substitution budget.\n\n",
        "## Agreement\n\n| Measurement | Agree | Total | Agreement |\n|---|---:|---:|---:|\n",
    ]
    for key, label in METRICS:
        count = result["counts"][key]
        text.append(f"| {label} | {count['agree']} | {count['total']} | {100 * count['agree'] / count['total']:.1f}% |\n")
    count = result["poem_verdict"]
    text.append(f"| Whole-poem licensed-meter verdict versus hand family | {count['agree']} | {count['total']} | {100 * count['agree'] / count['total']:.1f}% |\n")
    text.extend([
        "\nLow exact stress agreement partly reflects a deliberate model choice: monosyllables are realized in alternating positions, ",
        "while the hand reading often stresses adjacent content words. Such differences do not by themselves disprove either performance. ",
        "Syllabification and fixed multisyllabic-stress disagreements are stronger evidence of the current lexical model's limits.\n\n",
        "| Sonnet | Baseline syllables | Any-reading syllables | Exact baseline stress | Exact any-reading stress | Fixed-stress compatibility | Line-family agreement | Model poem verdict | Poem-family agreement |\n",
        "|---:|---:|---:|---:|---:|---:|---:|---|---|\n",
    ])
    for sonnet in result["sonnets"]:
        m = sonnet["metrics"]
        values = [str(sonnet["number"])]
        values += [f"{m[k]}/14" for k in ["baseline_syllables", "candidate_syllables", "baseline_stress", "candidate_stress", "fixed_stress_compatible", "meter_family"]]
        values += ["PASS" if sonnet["observed_licensed_meter"] else "FAIL",
                   "agree" if sonnet["poem_verdict_agrees"] else "disagree"]
        text.append("| " + " | ".join(values) + " |\n")
    text.extend([
        "\n## What the discrepancies establish\n\n",
        "The hand reading expands `temperate` (18.2) and `fixed` (116.5), contracts `every`/`wandering` (116.7), ",
        "and uses one syllable for both instances of `wires` (130.4). The context-free first dictionary reading does not supply all those choices. ",
        "The noun/verb ambiguity of `record` (55.8), the historical stress of `antique` (19.10), and the prosodic reading of `contents` (55.3) ",
        "also expose the limits of a modern lexicon without contextual disambiguation. The interior inversion on `ever` in 19.14 is outside the named rule set even though its ten syllables agree.\n\n",
        "These findings support the implementation as an auditable **conditional baseline**, but do not establish that its extra failures are genuine exceptions to Shakespearean verse. ",
        "The validation fixture is complete; the remaining literary-model work is to reconcile documented pronunciation/stress discrepancies and justify the scope of permitted substitutions. ",
        "A claim of reliable full-corpus historical conformance would also require validating historical rhyme classes; this sample is a scansion check only. ",
        "No independent reviewer was appointed or consulted by the author lane.\n\n",
        "## Every disagreement\n\n",
        "The table includes any line with a disagreement on any metric. `S` means strong and `u` weak. Candidate strings are after their declared elision; ",
        "the full text and individual Boolean measurements are in the result JSON. “Fixed stress” means the hand sequence conflicts with all supplied masks or lengths. ",
        "“Realization” means the masks permit the hand sequence but the deterministic candidates did not choose it.\n\n",
        "| Line | Hand stress | Model candidate stresses | Disagreement |\n|---|---|---|---|\n",
    ])
    for row in result["lines"]:
        a = row["agreement"]
        if all(a.values()):
            continue
        labels = []
        if not a["baseline_syllables"]:
            labels.append("baseline syllable count")
        if not a["candidate_syllables"]:
            labels.append("all candidate syllable counts")
        if not a["fixed_stress_compatible"]:
            labels.append("fixed stress/length")
        elif not a["candidate_stress"]:
            labels.append("realization")
        if not a["baseline_stress"] and a["candidate_stress"]:
            labels.append("baseline stress; another candidate agrees")
        if not a["selected_stress"] and a["candidate_stress"]:
            labels.append("selected stress")
        if not a["meter_family"]:
            labels.append("meter family")
        candidates = "; ".join(f"`{s}`" for s in dict.fromkeys(row["candidate_stresses"])) or "unresolved"
        text.append(f"| {row['number']}.{row['line']} | `{row['hand_stress']}` | {candidates} | {'; '.join(labels)} |\n")
    text.extend([
        "\n## Sources and limits\n\n",
        "Consulted 2026-10-27 (America/Los_Angeles). The corpus edition is exclusively the Gutenberg source in [PROVENANCE.md](PROVENANCE.md); ",
        "the following references inform the model discussion and do not replace its wording or lineation.\n\n",
        "- Barbara Mowat and Paul Werstine, [Reading Shakespeare’s Language: Sonnets](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/reading-shakespeares-language-sonnets/). ",
        "Their analysis of 2.1–4 supports the hand fixture's pyrrhic/spondaic readings and distinguishes lexical stress from sentence stress.\n",
        "- Folger Shakespeare Library, [Write a sonnet](https://www.folger.edu/explore/write-a-sonnet/), for the conventional fourteen-line, rhyme-scheme and pentameter account.\n",
        "- [CMUdict project](https://github.com/cmusphinx/cmudict), whose own documentation identifies the dictionary as US English and warns of errors and omissions. ",
        "See [PRONUNCIATION.md](PRONUNCIATION.md) for the frozen commit and model choices.\n\n",
        "Hand-source SHA-256: `", fixture["hand_source_sha256"], "`.\n\n",
        "Compared annotation SHA-256: `", result["annotations_sha256"], "`.\n",
    ])
    return "".join(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    fixture = hand_fixture()
    write_or_check(ROOT / "data/validation.json",
                   json.dumps(fixture, ensure_ascii=False, indent=2) + "\n", args.check)
    result = compare(fixture)
    write_or_check(ROOT / "data/validation-results.json",
                   json.dumps(result, ensure_ascii=False, indent=2) + "\n", args.check)
    write_or_check(ROOT / "VALIDATION.md", report(fixture, result), args.check)
    print(f"Hand fixture: {len(SAMPLE)} complete sonnets, {fixture['sample_lines']} lines")
    for key, label in METRICS:
        value = result["counts"][key]
        print(f"{label}: {value['agree']}/{value['total']}")
    value = result["poem_verdict"]
    print(f"Whole-poem verdict agreement: {value['agree']}/{value['total']}")


if __name__ == "__main__":
    main()
