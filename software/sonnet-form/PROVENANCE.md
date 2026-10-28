# Corpus provenance and fidelity

The sole text edition is **William Shakespeare, _Shakespeare's Sonnets_,
Project Gutenberg eBook 1041**, credited to the Project Gutenberg Shakespeare
Team. It is [listed as public domain in the United States](https://www.gutenberg.org/ebooks/1041).
The entire downloaded text, including its Gutenberg header and license, is
committed as [`data/gutenberg-1041.txt`](data/gutenberg-1041.txt).

| Field | Recorded value |
|---|---|
| Exact download URL | <https://www.gutenberg.org/cache/epub/1041/pg1041.txt> |
| Retrieval date | 2026-10-27, America/Los_Angeles (2026-10-28 UTC) |
| Edition release date in downloaded header | September 1, 1997 |
| Edition update date in downloaded header | October 29, 2024 |
| File size | 119,936 bytes |
| SHA-256 of original downloaded bytes | `4a3a5466591e30ca93b2c19daeb24770bb08833b57b1616c972b97246e23580f` |
| Encoding and line separators | UTF-8; CRLF |
| Parsed corpus | 154 sonnets; 2,155 verse lines |

The catalogue page returned an update date of March 10, 2024, while the
downloaded file's own header says October 29, 2024. The frozen file and its
hash identify the edition used here; we have not silently reconciled these
two metadata dates. No claim is made that this edition is a diplomatic
transcription of the 1609 quarto.

## Import and check

From this directory:

```sh
python3 tools/import_corpus.py
python3 tools/import_corpus.py --check
```

The importer uses Python's standard library only, does not access the network,
and first checks the entire raw file against the pinned hash. It recognizes
the Gutenberg start/end markers and the successive headings `I` through
`CLIV`. Every nonblank line following a heading and preceding the next heading
is one verse line. It does not wrap, join, truncate, pad, or reorder lines.

The only text-to-data transformations are:

1. Decode UTF-8 and separate the source's CRLF lines.
2. Exclude the Gutenberg header/footer, title/author, Roman numeral headings,
   and blank layout lines from the poem's verse-line list.
3. Strip outer ASCII spaces/tabs from each verse line, including the indentation
   of concluding couplets. Internal spaces, spelling, punctuation, case, and
   Unicode apostrophes/quotation marks are preserved.

[`data/sonnets.json`](data/sonnets.json) is the resulting verse data.
[`data/corpus-manifest.json`](data/corpus-manifest.json) records each sonnet's
original heading, one-based source file line numbers for every verse line,
line count, and SHA-256 of its UTF-8 normalized verse lines joined with LF
(including one terminal LF). `--check` regenerates both structures in memory
and checks every field and every verse string against the committed JSON.
This is an external source-fidelity check; a Lean kernel proof about encoded
strings alone cannot prove that they match an Internet edition.

## Fidelity events and calibration

- **Sonnet 99:** all 15 source verse lines are retained. No line is dropped
  to satisfy the 14-line predicate.
- **Sonnet 126:** all 12 source verse lines are retained. This particular
  Gutenberg file has no empty parenthesis/bracket placeholder lines after
  sonnet 126, so no such lines have been removed. No missing couplet is added.
- **Sonnet 145:** all 14 source verse lines are retained. Its shorter meter
  must be detected from the stress model, not by altering or joining its lines.
- **Sonnet 27.2:** the edition's `respose` is retained.
- **Sonnet 28.2:** the edition's `debarre’d` is retained.
- **Sonnet 146.1–2:** the repeated `sinful earth` wording in this edition is
  retained. It is not replaced by an emendation from another edition.
- Every other sonnet has 14 verse lines in this file. This fact is checked
  after parsing; the expected counts never drive extraction.

Pronunciation-token normalization and any lexical aliases belong to the
separate scansion model. They must not mutate these recorded verse strings.
