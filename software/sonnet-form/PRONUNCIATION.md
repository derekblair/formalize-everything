# Pronunciation model

[`tools/pronunciations.py`](tools/pronunciations.py) is a deterministic,
context-free lookup layer. Its public API is `tokenize(text)` and
`resolve(word)`, the latter returning `(ARPAbet_phone_list, derivation)` or
`None`. It receives no sonnet number, line number, metrical target, or rhyme
partner. It cannot choose a pronunciation merely because that pronunciation
makes a line pass.

The base is the frozen CMU Pronouncing Dictionary in `data/cmudict.dict`.
[`data/cmudict-source.json`](data/cmudict-source.json) records its retrieval
and identity; its original license is included. This is a modern American
English dictionary, not reconstructed Elizabethan pronunciation. Its first
listed pronunciation is selected deterministically. A resulting rhyme failure
is a failure under this model, not a proof that Shakespeare did not rhyme.

The snapshot is commit
[`74790861f652b15e4ac49015a90074ad62a27690`](https://github.com/cmusphinx/cmudict/tree/74790861f652b15e4ac49015a90074ad62a27690),
retrieved 2026-10-27 (America/Los_Angeles). The dictionary is 3,618,488 bytes,
SHA-256 `81917843c7f44ce2b094ac63873c2c7a4cf802040792c455ba3ca406891c3d22`.
The accompanying Carnegie Mellon University license permits redistribution
subject to retention of its notice, conditions, and disclaimer; it is retained
in full as [`data/cmudict-LICENSE`](data/cmudict-LICENSE). This licensed
pronunciation resource is separate from the public-domain poem edition.

## Explicit lookup decisions

1. Tokenization extracts ASCII alphabetic words with internal, leading, or
   trailing straight/curly apostrophes. Hyphens and dashes separate tokens.
   The source's stored verse strings are never modified.
2. Lookup lowercases tokens and maps curly apostrophes to straight apostrophes.
3. An explicit lexical override takes precedence, then the first CMU entry.
4. Trailing quotation or plural possessive apostrophes, and leading quotation
   apostrophes, may be removed for a subsequent lookup. Actual contractions
   such as `'gainst` and `'twixt` have explicit entries before this rule.
5. Possessive/contraction `'s` adds the regular allomorph: `/ɪz/` after a
   sibilant, `/s/` after a voiceless nonsibilant, and `/z/` otherwise.
6. Written `'d` first tries an `ed` expansion and then a `d` expansion. The
   dictionary or regular past-tense allomorph determines its pronunciation.
   This spelling rule is not permission to delete arbitrary syllables.
7. Written `'st` adds consonantal `/st/` to an attested stem. Full `est` and
   `eth` add syllabic `/ɪst/` and `/ɪθ/`. Stem spellings allow final `i/y`,
   silent `e`, and consonant doubling. A stem must already be present in the
   dictionary or explicit table. Known false proper-name matches and
   homographs are overridden explicitly.
8. Limited British spelling correspondences (`our/or`, doubled `l`, `re/er`,
   `ise/ize`, `isation/ization`) are accepted only when the resulting spelling
   is directly in CMU. Other spelling aliases are explicit entries.
9. Regular `s`, `es`, `ies`, `ed`, and `ing` inflections can use an attested
   dictionary/override stem. The past-tense allomorph is `/ɪd/` after `/t,d/`,
   `/t/` after other voiceless consonants, and `/d/` otherwise. Plurals follow
   the same sibilant/voicing rule as possessives.
10. Resolution is bounded to five recursive transformations. Every successful
    resolution reports its derivation, and any unresolved token stays unknown.

[`data/pronunciation-overrides.json`](data/pronunciation-overrides.json)
contains the complete explicit annotation table with a note for every entry.
The OOV pronunciations are author annotations of a modern reading, not
attested historical pronunciations and not independent scholarly validation.
The file includes transparent archaic morphology, spelling aliases, and
contractions. Examples are one-syllable `o'er`, `ne'er`, and `stol'n`, and the
zero-vowel `th'` clitic. Full `beauteous`, `bounteous`, and `duteous` are
recorded as three syllables; any later contraction must be separately licensed
by the metrical model. The file does not attach a different pronunciation to
the same word in different lines.

Examples of explicit safeguards against incorrect automatic stemming include
`maketh`/`mak'st` from _make_, not the proper name _Mak_; `diest` from _die_,
not _Di_; `buriest` from _bury_, not _Buri_; and `putt'st` from _put_, not the
golfing verb _putt_. The archaic word `recur'd` is interpreted as _recured_
(cured again), not _recurred_. Verb stresses for `convertest`, `presenteth`,
and `present'st`, and adjective stress for `perfect'st`, are explicit.

## Coverage and limits

Run:

```sh
python3 tools/pronunciations.py
```

This regenerates [`data/pronunciation-unknowns.json`](data/pronunciation-unknowns.json)
with every unresolved token and its sonnet/line location. All 2,155 line
endings and all interior tokens now resolve. Coverage remains distinct from
linguistic accuracy.

### MD-SOURCE-ALIAS: `respose` → `repose`

The frozen Gutenberg string **`respose` (27.2)** is unchanged. The
[Folger Shakespeare Library edition, sonnet 27, line 2](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/read/27/)
(accessed 2026-11-10) reads _repose_ at the corresponding position. The explicit
override now interprets that exact token as _repose_ for pronunciation lookup,
using the pinned CMU first entry `R IY0 P OW1 Z`. This is a documented editorial
alias supported by a named comparison edition, not evidence for a historically
pronounced word _respose_. It is lexical, applies wherever the token occurs,
and uses neither sonnet number nor metrical/rhyme fit. The annotation records
the source and derivation; the source text is never repaired. No generalized
spell-correction rule is introduced. Unknown tokens still produce no scans.

The edition's `debarre’d` likewise remains textually preserved with an explicit
pronunciation annotation corresponding to _debarred_; that is a morphological
interpretation, distinct from the editorial alias above.

CMU lexical stress is not sentence stress or a complete poetic scansion.
Stress flexibility, syllable contraction licenses, rhyme-class extraction,
and verdicts are defined in the Lean spec and corpus generator. Coverage does
not establish accuracy. In particular, author-supplied OOV entries, a single
pronunciation per word, modern rhotic vowels, and full syllabic archaic endings
can all create model-specific deviations.

## From phonemes to meter and rhyme

Each ARPAbet vowel with a final `0`, `1`, or `2` contributes one lexical
syllable. In a word with more than one syllable, `0` becomes weak and both
`1` (primary stress) and `2` (secondary stress) become strong. Every
monosyllabic word contributes one flexible stress mask instead. This applies
to content words as well as function words; it is a broad, explicit metrical
modeling decision. The Lean realization procedure places those flexible
syllables in the alternating iambic positions of the candidate scan. Its
success therefore means compatibility with those choices, not independent
measurement of spoken stress. Explicitly licensed elision candidates may
remove a designated unstressed syllable of a small named word set; they do
not alter the poem's spelling.

Rhyme classes are phoneme suffixes starting at the **last vowel carrying
primary or secondary stress** (`1` or `2`); if no vowel is marked stressed,
the last vowel is used. Stress digits are erased from the suffix before
comparison. A rhyme class therefore contains the stressed nucleus and
everything after it, including any following unstressed syllables. Unlike
metrical monosyllables, rhyme phonemes are never made flexible. A single
dictionary pronunciation is used even when an alternate pronunciation or
historical accent would produce a rhyme. The distinction between lexical
stress masks and fixed phonetic rhyme classes is intentional.

## MD-ELISION-SITES: eligible lexical contractions

Only the second, explicitly weak syllable of a two-syllable reading of the
following forms can supply an elision candidate: `heaven`, `heavens`,
`heaven's`, `power`, `powers`, `power's`, `flower`, `flowers`, `flower's`,
`hour`, `hours`, `hour's`, and `our`. The list models conventional poetic
contraction/synizesis of these forms as deletion of one weak syllable. It is
an author-specified approximation, not a phonetic derivation; consonantal
realization is not reconstructed. Only one site can be used in a reading.
The baseline remains first, so a passing feminine-ending reading takes
precedence over a later elision candidate. No contraction is inferred from
line length, sonnet number, or rhyme partner. Other possible contractions
remain model failures and are visible in the validation sample.
