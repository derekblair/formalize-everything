# Pronunciation model

[`tools/pronunciations.py`](tools/pronunciations.py) is a deterministic,
lexical lookup layer. Its public API is `tokenize(text)`, `resolve(word)`, and
`resolve_in_context(tokens, index)`. Both resolution functions return
`(ARPAbet_phone_list, derivation)` or `None`. The context API additionally
recognizes the finite local lexical cues specified below. Neither API receives
a sonnet number, line number, metrical target, or rhyme partner. No rule measures
a line's syllable count or tests a pronunciation's metrical/rhyme success.

The base is the frozen CMU Pronouncing Dictionary in `data/cmudict.dict`.
[`data/cmudict-source.json`](data/cmudict-source.json) records its retrieval
and identity; its original license is included. This is a modern American
English dictionary, not reconstructed Elizabethan pronunciation. Its first
listed pronunciation is the fallback after documented lexical/context choices. A resulting rhyme failure
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
3. `resolve` uses an explicit global lexical override, then the first CMU
   entry. An entry containing only `context_variants` is not a global override.
   `resolve_in_context` first checks the named contextual rules below, then
   delegates unchanged to `resolve` when no cue matches.
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
by the metrical model. Global entries apply at every occurrence. Only the
separately named context rules can distinguish uses of the same token, using
adjacent words rather than poem identifiers or desired verdicts.

Examples of explicit safeguards against incorrect automatic stemming include
`maketh`/`mak'st` from _make_, not the proper name _Mak_; `diest` from _die_,
not _Di_; `buriest` from _bury_, not _Buri_; and `putt'st` from _put_, not the
golfing verb _putt_. The archaic word `recur'd` is interpreted as _recured_
(cured again), not _recurred_. Verb stresses for `convertest`, `presenteth`,
and `present'st`, and adjective stress for `perfect'st`, are explicit.

## MD-SOURCED-LEXICAL-READINGS: finite documented choices

Sources were consulted on 2026-11-10. These author-selected annotations address
specific discrepancies exposed by the development sample; the frozen hand
fixture was not changed. Improved agreement is therefore a regression result,
not independent or held-out evidence for historical accuracy. The sources
support the availability or literary convention of a reading; they do not make
the chosen performance uniquely correct. Source URLs and the selection reason
are retained in the JSON entries, including contextual variants.

| Token / scope | Selected syllables and stress | Evidence and boundary |
| --- | --- | --- |
| `temperate`, every occurrence | `TEM-per-ate`, three syllables (`Suu`) | Exactly `temperate(2)` in the pinned CMU dictionary. This establishes an available modern full form, not an exclusive Elizabethan pronunciation. |
| `every`, every occurrence | `EV-ry`, two syllables (`Su`) | Exactly pinned CMU `every(2)`. Selection is global, including lines outside the development sample. |
| `wandering`, every occurrence | `WAN-dring`, two syllables (`Su`) | [Poetry Foundation's sonnet 116](https://www.poetryfoundation.org/poems/45106/sonnet-116-let-me-not-to-the-marriage-of-true-minds) explicitly prints `wand'ring`. The author ARPAbet annotation replaces the weak `ER0` in CMU with consonantal `R`; no general rule deletes vowels from other `-ering` forms. |
| `wires`, every occurrence | one syllable | Exactly pinned CMU `wires(2)`, `W AY1 R Z`. Both occurrences receive the same lexical reading. |
| `antique`, every occurrence | `AN-tique`, two syllables (`Su`) | Alexander Schmidt, *Shakespeare-Lexicon*, vol. I, p. 43, entry *Antic*, treats the old `antic`/`antique` spellings together and gives initial stress; *Antique* cross-refers there ([publisher scan](https://api.pageplace.de/preview/DT0400.9783112315330_A39774742/preview-9783112315330_A39774742.pdf), fifth unchanged edition, 1962). Only the stress marks of the modern CMU segments are adapted. This is a historically informed stress annotation, **not** a reconstruction of historical vowel quality. |
| `contents`, every occurrence | `con-TENTS`, two syllables (`uS`) | Phones equal pinned CMU `contents(2)`. The [Audio Shakespeare Pronunciation Dictionary's guide](https://www.audioshakespearepronunciationapp.com/shakespeare-pronunciation-dictionary/) documents final stress for the word in *Cymbeline* II.2.27, *King Lear* II.4.33 and other plays. This supports a Shakespearean prosodic convention beyond the sampled sonnet; it does not establish a unique performance of that sonnet. |
| `fixed` in determiner + `ever fixed` + head-token frame | `FIX-ed`, two syllables (`Su`) | The same Poetry Foundation text marks `ever-fixèd`. Author ARPAbet is `F IH1 K S IH0 D`. Unclassified `fixed` retains CMU's one syllable. The preceding determiner and following token approximate an attributive adjective: `an ever-fixed mark` qualifies; `have you ever fixed this` and bare `ever fixed` do not. Hyphen and space are not distinguished. This is a finite cue, not a full syntactic parser, and does not generalize to other participles. |
| noun `record` in the finite frames below | `REC-ord`, two syllables (`Su`) | [Cambridge's pronunciation entry](https://dictionary.cambridge.org/pronunciation/english/record) distinguishes initial-stressed noun from final-stressed verb. The selected phones are exactly pinned CMU `record(2)`. This is contextual modern lexical disambiguation, not evidence that all historical noun uses had this stress. |

The specialist guide belongs to the pronunciation project of Shane Ann Younts
and Louis Scheeder, authors of *All the Words on Stage*, as identified on its
[project page](https://www.audioshakespearepronunciationapp.com/). It also
independently documents initial-stressed `antique`. Its recommendations concern
performable Shakespearean readings; they are not recordings of early modern
speakers. CMU's complete original variant entries remain unchanged in the
pinned dictionary; the overrides select or explicitly adapt those entries.

### MD-LOCAL-LEXICAL-CONTEXT: `record` and `ever fixed`

`resolve_in_context(tokens, index)` normalizes case and apostrophes for local
comparison. For **`record` only**, it chooses noun stress when either:

- The immediately preceding token is `a`, `an`, `the`, `my`, `thy`, `thine`,
  `your`, `our`, `his`, `its`, or `their`.
- The preceding two tokens are one of those determiners followed by `living`.
  This is a finite named adjective cue, not a guess that any intervening word
  is an adjective.
- The previous token is `this` or `that` **and** the following token is one of
  `of`, `is`, `was`, `can`, `could`, `shall`, `should`, `may`, `might`, `must`,
  `will`, or `would`.

The restriction on `that` leaves a relative-clause frame such as `songs that
record voices` unchanged. `Her` is deliberately excluded because `saw her
record` can contain a verb. Bare `record`, `to record`, and unclassified frames
retain the first CMU reading; no general part-of-speech accuracy is claimed.
Each match reports its named cue and source-backed variant in the derivation.
The only other contextual rule is the `fixed` expansion. It requires the
previous token `ever`, one of the same listed determiners immediately before
`ever`, and at least one following token. This excludes the observed verbal
false positive `have you ever fixed this`, although the rule still does not
prove that the following token is a noun.
Context does not cross a verse-line boundary.

Lexical syncope for `every`, `wandering`, and `wires` is part of the selected
pronunciation, not a use of the Lean `unstressedElision` license. More than one
of these lexical forms can therefore occur in a line without relaxing the
one-site scan-elision limit. Likewise the full `temperate` and `ever fixed`
readings specify syllables before scanning; the meter checker does not insert
syllables to complete a foot. No source text, dictionary bytes, dependency pin,
or reference hand scan is changed by these choices.

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
not establish accuracy. In particular, author-supplied OOV entries, one selected
pronunciation per classified use, modern rhotic vowels, and full syllabic archaic endings
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
metrical monosyllables, rhyme phonemes are never made flexible. The single lexical/contextual pronunciation selected before rhyme extraction
is used, even when another pronunciation would produce a rhyme. The sourced
`contents` stress choice therefore changes its extracted rhyme suffix too;
that is a consequence of its word-level annotation, not a rhyme-specific rule. The distinction between lexical
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

## Historical rhyme evidence does not select pronunciations

[HISTORICAL-RHYME.md](HISTORICAL-RHYME.md) and the per-sonnet review in
[DEVIATIONS.md](DEVIATIONS.md) assess the original 133 failed rhyme verdicts
against cited scholarship, including
[David Crystal's original-pronunciation study](https://www.davidcrystal.com/Files/BooksAndArticles/-4836.pdf).
The review is bound to a frozen baseline; later lexical choices may change a
modern rhyme suffix, so both baseline evidence and current modern relations are
visible. No review finding feeds into `resolve`, `resolve_in_context`, the rhyme
suffix extraction, or the Lean predicate. A documented historical or imperfect
rhyme relation is evidence to assess, not permission to fit a word to its partner.
The remaining per-pair and whole-scheme uncertainties stay explicit.

## Collateral corpus effects requiring follow-up

The full-corpus comparison retains two newly failing licensed-meter lines rather
than selecting a different reading by metrical fit:

- **53.12:** the globally selected two-syllable `every`, combined with the
  unchanged one-syllable CMU `blessed`, leaves nine syllables. The prior model's
  three-syllable `every` happened to supply ten. A sourced treatment of syllabic
  `blessed` or a principled finite lexical-alternative policy remains necessary.
- **59.5:** the local noun phrase `that record could` now receives noun stress.
  It produces a second-foot trochee, outside the stated license set. Historical
  noun-stress alternatives or a more complete syntactic/prosodic policy need
  independent justification. The old verb reading happened to pass strictly.

These are additional annotation/model questions, not established literary
exceptions. No metrical failure is used to override the sourced lexical rule.
All seven lines containing the eight specifically requested annotations pass
strict or licensed meter; that targeted success does not settle these other
contexts or full-corpus historical accuracy. The final verification records
include every changed line and both regressions.
