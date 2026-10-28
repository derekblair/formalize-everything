#!/usr/bin/env python3
"""Reproduce the corpus from the committed, byte-pinned Gutenberg edition.

No network access and no dependency beyond Python's standard library.
Use --check in CI; ordinary invocation writes the two generated JSON files.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "data/gutenberg-1041.txt"
EXPECTED_SHA256 = "4a3a5466591e30ca93b2c19daeb24770bb08833b57b1616c972b97246e23580f"
START = "*** START OF THE PROJECT GUTENBERG EBOOK SHAKESPEARE'S SONNETS ***"
END = "*** END OF THE PROJECT GUTENBERG EBOOK SHAKESPEARE'S SONNETS ***"


def roman(number):
    result = ""
    for value, symbol in [(100, "C"), (90, "XC"), (50, "L"), (40, "XL"),
                          (10, "X"), (9, "IX"), (5, "V"), (4, "IV"), (1, "I")]:
        while number >= value:
            result += symbol
            number -= value
    return result


def parse_source():
    raw = SOURCE.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != EXPECTED_SHA256:
        raise ValueError(f"Source byte hash changed: {actual}")
    # splitlines removes CRLF separators, but does not alter Unicode or verse text.
    source_lines = raw.decode("utf-8").splitlines()
    start = source_lines.index(START)
    end = source_lines.index(END)
    headers = []
    for index in range(start + 1, end):
        if re.fullmatch(r"[IVXLCDM]+", source_lines[index]):
            headers.append(index)
    if [source_lines[i] for i in headers] != [roman(i) for i in range(1, 155)]:
        raise ValueError("Expected exactly the successive headings I through CLIV")
    corpus, manifest = [], []
    for number, (begin, finish) in enumerate(zip(headers, headers[1:] + [end]), 1):
        verse_indices = [i for i in range(begin + 1, finish) if source_lines[i].strip()]
        # Only outer ASCII spaces/tabs are layout. Internal spaces and all text
        # punctuation (including curly apostrophes) remain byte-for-byte in UTF-8.
        verse = [source_lines[i].strip(" \t") for i in verse_indices]
        if any("***" in line for line in verse):
            raise ValueError("Unexpected boilerplate among verse lines")
        corpus.append({"number": number, "lines": verse})
        manifest.append({
            "number": number,
            "heading": source_lines[begin],
            "source_heading_line": begin + 1,
            "source_verse_lines": [i + 1 for i in verse_indices],
            "line_count": len(verse),
            "normalized_verse_sha256": hashlib.sha256(
                ("\n".join(verse) + "\n").encode("utf-8")).hexdigest(),
        })
    # Calibration asserts facts of this edition, never truncates/pads the source.
    expected_counts = [15 if i == 99 else 12 if i == 126 else 14 for i in range(1, 155)]
    if [len(s["lines"]) for s in corpus] != expected_counts:
        raise ValueError("Unexpected source lineation; investigate, never repair to fit")
    return corpus, manifest


def serialized(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify generated files without writing")
    args = parser.parse_args()
    corpus, manifest = parse_source()
    for name, value in [("sonnets.json", corpus), ("corpus-manifest.json", manifest)]:
        path = ROOT / "data" / name
        expected = serialized(value)
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != expected:
                raise SystemExit(f"FAIL: {path.relative_to(ROOT)} differs from frozen edition")
        else:
            path.write_text(expected, encoding="utf-8")
    print(f"PASS: {len(corpus)} sonnets; {sum(len(s['lines']) for s in corpus)} verse lines; "
          "source SHA-256 and every normalized verse line verified")
    print("Line-count distribution: 152 × 14; sonnet 99 = 15; sonnet 126 = 12")


if __name__ == "__main__":
    main()
