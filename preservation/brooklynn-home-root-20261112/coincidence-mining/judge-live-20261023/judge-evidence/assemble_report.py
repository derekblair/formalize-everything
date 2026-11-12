import collections,datetime,hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parent.parent
e=root/'judge-evidence'
parts=['61-85','86-110','111-135','136-160']
reviews=[]
for part in parts:reviews+=json.loads((e/f'reviews/{part}.json').read_text())
assert [x['rank'] for x in reviews]==list(range(61,161))
assert all(x['verdict']=='DROP' for x in reviews)
counts=collections.Counter((x.get('primary_gate') or x['gate']).lower() for x in reviews)
manifest=json.loads((e/'retrieval-manifest.json').read_text())
assert len(manifest)==200 and all(x['valid'] and x['staged_equal'] for x in manifest)
for item in manifest:
 assert hashlib.sha256((e/f"records/{item['id']}.seq").read_bytes()).hexdigest()==item['sha256']
metrics=json.loads((e/'agreement.json').read_text())
assert all(x['packet_variant']['count']==x['claimed'] for x in metrics)
header='''# Independent judgment: coincidence-mining candidates 61–160

**Result: 0 KEEP; 100 DROP.** All 100 candidates fail at least one required gate. No candidate remains for proof or statement drafting.

| Primary failed gate | Count |
| --- | ---: |
| Data integrity: the proposed identity is false | 64 |
| Novelty: the relevant equality or transformed equality is already published | 26 |
| Interestingness: an excluded elementary sign, absolute-value, or periodic transform | 10 |
| **Total DROP** | **100** |
| **Total KEEP** | **0** |

Counts assign one decisive primary gate per candidate; secondary failures are recorded in the individual sections. A false proposed identity does not necessarily mean either OEIS sequence contains bad data.

## Method and evidence

Reviewed on **2026-10-23 UTC** against the brief's three gates. I independently retrieved all **200 complete records** from the official [OEIS data repository](https://github.com/oeis/oeisdata), using its `seq/Axxx/Axxxxxx.seq` files. Retrieval validation completed at **16:14:44 UTC**. All 200 match their staged counterparts after removing outer whitespace. The complete retrieved records, URLs, timestamps, byte counts, and SHA-256 hashes are retained in [the retrieval manifest](judge-evidence/retrieval-manifest.json) and its adjacent `records/` directory. No input file was changed.

The automated comparison concatenated each record's `%S`, `%T`, and `%U` terms and read the first `%O` component. It reproduced **all 100 advertised agreement lengths**, including the packet's transformations. The agreement metadata were therefore reproduced, but they are not evidence of infinite equality. Full numerical results are in [agreement.json](judge-evidence/agreement.json); the comparison is reproducible with [compare.py](judge-evidence/compare.py).

- **Native-index agreement** compares the original signed values at the same available index. **Positional agreement** compares their first listed terms, then their second listed terms, and so on; different offsets can make these different claims.
- **`drop1` / `drop2`** remove that many entries from **both** lists. They do not shift only one sequence. **`abs`** takes absolute values before positional comparison. Each section preserves the actual indices and exceptions.
- **A displayed-list agreement length is a lower bound when the shorter list ends.** Extended lengths are explicitly attributed to independent calculations, fetched b-files, or a published OEIS claim. A b-file comparison is data verification, not an independent proof of the definition. Where a first counterexample already occurs in `%S/%T/%U`, that is stated.
- For decimal expansions marked **`cons`**, the first offset also records the decimal-point position. Matching digit strings after moving that point or deleting initial digits does not assert equality of the constants. Native-index mismatch in such cases is a bookkeeping observation, not an additional mathematical counterexample.

Novelty checking inspected both complete records, including names, comments, formulas, qualified cross-references, and references. An explicit conjecture is already published and fails the novelty gate. Identical published formulas or explicit identification with the same third sequence also suffice; an unqualified `Cf.` or an implication between equivalence classes does not. Every candidate has a decisive counterexample, a published equivalence, or a prohibited elementary transform, so no candidate required a broader literature search to decide whether to KEEP it. No claim of exhaustive literature coverage is made for rejected pairs.

Finite-prefix counterexamples were independently calculated where practical and otherwise checked against the retrieved lists/b-files; the sections distinguish those evidence types. Reproducible calculations and supplementary-source manifests are saved in [judge-evidence/reviews](judge-evidence/reviews), with the first block's computations in [check_61_85.py](judge-evidence/check_61_85.py) and [computed-61-85.json](judge-evidence/computed-61-85.json). Independent block review and cross-review checked the verdicts and arithmetic.

## Material record errors found

These do not create survivors, but they matter for this programme's integrity gate:

- **Candidate 115:** A347470's claimed agreement for n<111 is false. Direct definitions first diverge at **n=110**, with **10 versus 0**, before its cited n=112 example.
- **Candidate 72:** A279186 publishes the exact same formula as A256608 while retaining a conflicting cross-reference claiming they are different. The published formula already defeats novelty.
- **Candidates 62, 116, 125, 130, 132, 149, and 150:** literal formulas or programs contradict listed terms or initial values; explicit witnesses appear below. In particular, A199918's bilateral sum gives constant coefficient 0 instead of 1, and A143064's mistyped product gives a(1)=2 instead of 1.
- Further malformed formulas, examples, comments, or code are flagged in **67, 78, 86, 91, 97, 104, 109, 112, and 140**. None was silently accepted as authority for an identity.

'''
body='\n'.join((e/f'reviews/{p}.md').read_text().strip() for p in parts)
body=body.replace('(records/', '(judge-evidence/records/')
body=body.replace('[https://arxiv.org/abs/2107.05572](https://arxiv.org/abs/2107.05572)','[Clark–Shattuck paper cited by OEIS](https://arxiv.org/abs/2107.05572)')
body=body.replace('Offsets 1/0; the 105 positional digit matches mean A010476(n)=A020762(n-1), n=1..105. Same-index comparison matches only n=1, then fails at n=2 (4 versus 7).','The `cons` offsets 1/0 encode different decimal-point positions. The 105 positional digit matches mean A010476(n)=A020762(n-1), n=1..105. A comparison using identical stored indices matches only n=1, then fails at n=2 (4 versus 7); this is bookkeeping, not a new mathematical discrepancy.')
report=header+body+'\n\nJUDGE COMPLETE\n'
(root/'JUDGE-LIVE.md').write_text(report)
summary={'keep':0,'drop':100,'primary_gates':dict(counts),'ranks':list(range(61,161)),'records_fetched':200,'record_hashes_verified':200,'packet_agreements_reproduced':100,'brief_sha256':hashlib.sha256((root/'BRIEF.md').read_bytes()).hexdigest(),'packet_sha256':hashlib.sha256((root/'PACKET2-FULL.md').read_bytes()).hexdigest()}
(e/'judgment-summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps({k:v for k,v in summary.items() if k!='ranks'},indent=2))
print('report bytes',len(report.encode()))
