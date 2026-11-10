# Historical rhyme review

This author-side review accounts for **all 133 original modern-model rhyme failures** at rebased commit `cfdc1c78e8f12deb451df8ae8c2425a8de159a38`. It does **not** validate a historical pronunciation model or a complete historical rhyme scheme. The sources support some intended pair relations, identify some imperfect rhymes, and leave explicit questions elsewhere.

The authoritative per-sonnet findings are in [data/historical-rhyme-review.json](data/historical-rhyme-review.json). [DEVIATIONS.md](DEVIATIONS.md) renders every original constraint with its evidence and current modern relation. A later pronunciation repair may change a current verdict; it does not change membership in this original 133-sonnet review.

## Results and their limits

The original failures contain 236 unequal intended pairs across 127 sonnets, 83 collisions between different signature letters across 23 sonnets, and the non-fourteen-line structures of sonnets 99 and 126. These groups overlap; their sonnet counts must not be added.

| Original unequal intended pairs | Count | What is established |
|---|---:|---|
| Scholarly pair support | 131 | A consulted historical discussion supports the particular poetic rhyme relation; no unique phonetic reconstruction is certified. |
| Inference from a scholarly rule or related pair | 8 | A plausible extension is identified, with the missing exact attestation left open. |
| Partial support | 2 | Only part of the difference is addressed. |
| Modern variant only | 2 | A diagnostic modern alternative, without historical attestation. |
| Scholarly imperfect analysis | 5 | The source expressly analyzes an imperfect rhyme, assonance, or unequal sounds; other historical alternatives are not exhaustively ruled out. |
| Scholarly disagreement | 1 | The consulted sources differ about exactness. |
| Open | 87 | A historically justified complete relation has not been established by this review. |
| **Total** | **236** | **Inventory coverage is complete; historical validation is not.** |

Of the 83 cross-class collisions, 21 repeat the same normalized ending token across different signature letters. These prove a distinctness obstruction under deterministic context-free lookup, whatever pronunciation that token receives. Four further constraints are covered by a scholarly observation of repeated rhyme in sonnets 46 and 134. The remaining 58 collisions need historical evidence for identity or separation.

The identical-token obstruction occurs in sonnets **3, 6, 24, 28, 29, 43, 44, 45, 46, 51, 90, 133, 134, 135, and 136**. It is a consequence of the formal specification requiring seven distinct classes, not a judgment that the poetry is defective. Folger corroborates 99's fifteen lines and 126's twelve; neither is forced into fourteen-position pair comparisons.

Eighty-one sonnets have at least one explicitly open original constraint. Even where every original failed pair has source support, a full historical scheme remains unestablished: that would additionally require coherent historical tails for all fourteen endings, all seven within-class equalities, and all twenty-one between-class inequalities. A finding about one pair does not supply those checks. **Complete historical schemes validated: zero.**

## Evidence

- David Crystal, [“Sounding out Shakespeare: sonnet rhymes in original pronunciation”](https://www.davidcrystal.com/Files/BooksAndArticles/-4836.pdf) (2011), printed pp. 295–306, especially §§2–2.5 and the appendix. His discussion covers vowel quality, quantity, diphthongs, stress, and consonants. The inventory here was independently built from the frozen corpus; it does not reproduce his table. The paper supports poetic relations while acknowledging historical variation.
- Wilhelm Viëtor, [*Shakespeare’s Pronunciation I*](https://archive.org/details/shakespearespron00virich) (1906), specific discussions in §§9, 16, 26, 35, 47, 65, 70, and 82, with the relevant index entries. This older reconstruction supplies additional evidence and explicit imperfect-rhyme analyses. Its index also selects some transcriptions according to rhyme partners (§10, p. 14); those transcriptions are **not** independent validation and are not adopted here.
- Barbara Mowat and Paul Werstine, [Folger's account of the sonnets' language and metrics](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/reading-shakespeares-language-sonnets/), and [Folger's text of 126](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/read/126/), corroborate structural exceptions.
- Rodolfo Delmonte, [“Computing the Sound–Sense Harmony”](https://www.mdpi.com/2078-2489/14/10/576) (2023), §3.2.3, explicitly observes repeated rhyme in 46 and 134. Only that observation is used. The paper's pronunciation fitting from rhyme partners is excluded as independent historical evidence.

Each JSON evidence ID gives a source URL, page or section locator, claim, and limitations. The task audit contains downloaded source snapshots and their checksums. These findings are author support, not an independent scholarly assessment or crossed review.

## Cases requiring care

- Crystal's love/prove numbering points to 9, but the frozen pair is in 10. His loving/approving entry differs from the frozen reproving in 142. His clear/everywhere and appear/everywhere entries differ from the frozen final token where in 84 and 102. These bindings are explicitly classified as inferences.
- The frozen **costs/boast** in 91 retains an extra final consonant. Crystal's singular cost does not settle it; Viëtor's prose prints costs but discusses the vowel difference. The consonantal remainder stays open.
- Viëtor discusses **open/broken** (61) and **remember'd/tender'd** (120) as assonance, distinguishes noun **use** in 78 from the verb in 21/82, and marks **possessing/releasing** (87) and **most/lost** (152) imperfect. These are evidence-backed nonexact analyses, not successful exact-rhyme certificates.
- **Spirit/merit** (108) remains open because Viëtor contrasts contemporary and later evidence. **Lease/excess** (146) records disagreement between Crystal's quantity account and Viëtor's retention of unequal quantity.
- Historical syllabification alone does not settle complete stress-tail equality: the partial **strumpeted/disabled** finding in 66 says precisely what the source addresses.

## Binding and reproduction

The review records the original annotation SHA-256, corpus SHA-256, full baseline class vectors and ending tokens, and per-constraint line hashes. It separates `unequal_pairs`, `cross_class_collisions`, and `structure`, with explicit `evidence_ids`, `open_question`, `open_constraint_ids`, and `whole_historical_scheme_status` for every sonnet.

[tools/rhyme_review.py](tools/rhyme_review.py) checks the fixed baseline projection, independently reconstructs every failed constraint from the class vectors, and verifies line/token bindings, status counts, and open lists. Generation renders the review but does not feed its claims into pronunciation selection or the Lean checker. No historical phonemes, rhyme-partner overrides, or sonnet-specific pronunciation fits are introduced by this review.
