# Specification and modeling decisions

`SonnetForm/Spec.lean` is the executable form specification. It uses Lean's
standard library and no Mathlib. `SonnetForm/Phonology.lean` turns explicit
syllable/stress annotations into the finite readings checked by that
specification. The text, its annotation, and a theorem about the annotation are
three distinct things: the kernel checks the last against the middle; source
comparison and linguistic validation justify the first-to-middle relationship.

## Data and decidable components

A `Sonnet` has a number and a list of `Line`s. A line retains its source `text`,
an optional line-ending `rhyme` class, and a finite list of `Scan`s. Each scan
has a list of syllable stresses (`false` weak, `true` strong) and an optional
zero-based index of a syllable to elide. The text is never rewritten by the
specification. Missing rhyme classes and missing stress annotations fail their
respective components; they never receive favorable defaults.

The executable checks are `lineCount`, `rhymeScheme`, `meterStrict`, and
`meterLicensed`. Their propositional interfaces are `HasFourteenLines`,
`HasRhymeScheme`, `HasStrictMeter`, and `HasLicensedMeter`, each with a
constructive `Decidable` instance. `verdict` retains all four Boolean results,
so failure of one does not suppress another. Corpus theorems use kernel
reduction through `decide`.

## MD-LINES: source lineation

`lineCount` means exactly 14 encoded verse lines. An edition's indentation is
not a second line. Blank separator lines and headings are not verse. No padding,
deleting, wrapping, or joining verse lines is permitted to make the count pass.
There is no line-count license. Source extraction rules and fidelity checks are
recorded with the corpus provenance.

## MD-RHYME-EXACT: equality classes, including distinct letters

Rhyme classes are input annotations, not inferred from spelling by the Lean
predicate. The signature is `[A,B,A,B,C,D,C,D,E,F,E,F,G,G]`. Two positions have
equal classes **if and only if** their signature letters are equal. Thus A–G
are pairwise distinct: repeating an earlier quatrain's class in a later
quatrain fails this particular exact-form model. This is an explicit choice;
a weaker check of seven expected pairs would express a different specification.

A class must be present and nonempty. The list must have exactly 14 entries.
Consequently, a 15- or 12-line poem fails both line count and this rhyme
specification, even when its actual line endings follow a coherent alternate
scheme. There is no rhyme license. Pronunciation-dictionary classes may
misclassify historical, dialectal, or approximate rhymes; a failed dictionary
class check is not by itself a discovery of a literary anomaly. The corpus
annotation documentation records the concrete class construction.

## MD-STRESS: binary annotated syllables

The specification assumes a sequence of pronounced syllables, each marked weak
or strong. It does not prove that letters uniquely determine syllables, lexical
stress, rhetorical emphasis, or the pronunciation used in Shakespeare's time.
Its strict target is five repetitions of weak–strong, exactly ten syllables.
A strict reading has no elision and no additional syllable. Stress tiers beyond
weak/strong belong to the external annotation policy, not this Boolean model.

## MD-LICENSES: a finite, named grammar

Every rule below has its own executable predicate and `License` constructor.
The predicates require the whole scan to pass `scanLicensed`; detecting a
pattern somewhere in an otherwise failed scan does not grant a license.

| Rule / predicate | Exact condition |
| --- | --- |
| `initialTrochaicInversion` | The first foot is strong–weak. |
| `interiorTrochaicInversion` | Exactly one interior foot is strong–weak, in the third or fourth foot of the ten-syllable core. |
| `feminineEnding` | After any elision, an eleventh syllable is weak; remove it before checking the five feet. |
| `pyrrhicSubstitution` | At least one two-syllable foot is weak–weak. |
| `spondaicSubstitution` | At least one two-syllable foot is strong–strong. |
| `unstressedElision` | Exactly one explicitly indexed weak syllable is deleted before the other checks. |

`scanLicenses` enumerates all used rules for a passing reading. Multiple rules
can apply to the same reading. `lineLicenses` reports rules from the first
passing candidate, whose deterministic ordering is described below.

## MD-METER-BUDGET: restricted substitution, with composition

After an optional elision and feminine ending, exactly ten syllables remain.
They are grouped into five consecutive two-syllable feet. At most **two** feet
may differ from weak–strong, so at least three remain iambs. Trochees are
allowed in the initial foot and, subject to MD-INTERIOR-INVERSION below, in
the third or fourth foot. Weak–weak and strong–strong substitutions are
allowed in any foot. Every trochee consumes one unit of the same two-foot
budget. A feminine ending and elision do not consume this budget and can
combine with each other and the substitutions.

The two-foot bound is a conservative modeling choice, not a theorem about all
historical metrical practice. No second/fifth-foot inversion, anapestic
expansion, acephalous line, or arbitrary syllable insertion is granted. A line
rejected because it needs an unenumerated license is a failure **under this
model**. The strict and licensed checks are both recorded so the impact of
licenses is visible. A tetrameter cannot pass by invoking these licenses:
deletion never creates the missing fifth foot.

## MD-INTERIOR-INVERSION: bounded positional feasibility

At most **one** noninitial foot may be a trochee, and it must be the third or
fourth foot (zero-based index 2 or 3). An initial inversion may combine with
it, still subject to the shared two-substitution budget. Positions are counted
after the declared elision and removal of any feminine ending. Neither text,
word identity, nor sonnet/line number enters this predicate.

[Bruce Hayes, “The Prosodic Hierarchy in Meter” (1989), pp. 256–257](https://brucehayes.org/201A/readings/HayesProsodicHierarchy1989.pdf#page=29),
identifies the first, third, and fourth feet as preferred inversion positions
associated with possible colon beginnings, with second/fifth-foot inversions
avoided. He also requires genuine phrasal breaks for Shakespeare. The selected
positions follow that evidence; the one-interior limit and total budget are
conservative author choices, not universal historical rules.

The specific fourth-foot inversion on *ever* in sonnet 19.14 has direct
scholarly support: [Paul Kiparsky, “The Rhythmic Structure of English Verse”
(1977), p. 217, example (75d)](https://brucehayes.org/251metrics/papers/KiparskyRhythmicStructureEnglishVerse1977Shorter.pdf#page=29),
lists it among sentence-internal cases permitted after a phrase boundary
without a preceding proclitic. This evidence supports the example independently
of its passing the model; it does not define the executable rule by that line.

`Scan` has no phrase-boundary or proclitic annotation. Consequently this rule
is a **positional feasibility approximation**, not a complete implementation
of either scholar's grammar. It can admit a stress sequence whose phrasing
would not justify inversion. The specific *ever* reading is supported, but the
general linguistic license is only partially modeled: phrase/proclitic
annotation and validation remain outstanding. No new stress realization or
pronunciation is inferred by this license, and a failed whole scan receives
no license names. Sources consulted 2026-11-10 UTC.

## MD-MONOSYLLABLE-FLEX: context-sensitive stress masks

A stress mask is `Option Bool`: `some false` or `some true` fixes a syllable's
stress, while `none` is a **known syllable with flexible stress**. It is not an
unknown word, an absent syllable, or permission to alter the syllable count.
The corpus pronunciation policy marks known monosyllables flexible and fixes
multisyllabic stresses. This admits contextual promotion or demotion of
monosyllables, including suppression of an emphasis a particular reader might
prefer. Such choices are supplied as part of the annotation model, not silently
reported as facts about performance. Incomplete lexical coverage must produce
no scans for the line, rather than a list of flexible guessed syllables.

## MD-REALIZATION: deterministic finite readings, computed in Lean

`realizeStress` fills each flexible position with the alternating weak–strong
value, beginning weak. Fixed values are preserved. Thus it chooses an iamb
whenever a two-syllable foot is compatible with one; otherwise a fixed conflict
can force a substitution or rejection. The eleventh position is weak if
flexible. There is no search over arbitrary syllable counts and no use of the
sonnet number to select stresses. General kernel theorems
`realizeStress_compatible` and `realizeStress_length` prove that this baseline
realization respects every fixed mask and preserves the mask length.

`scansFromMasks` emits the baseline followed by one reading for each supplied
eligible elision index, in input order. An elision site is accepted only if it
indexes `some false`; flexible or strong stresses and out-of-range indices are
rejected. The remaining masks are realized after the deletion, then the weak
syllable is reinserted into the raw scan with its index, allowing the
specification itself to perform and check the elision. At most one site is
used in any reading; sites are not combined. The corpus documentation records
which lexical forms can supply these indices and why.

The check is existential over this finite list: a line passes if any candidate
passes; a sonnet passes meter if it has at least one line and **every** line
passes. Line count is checked separately. A failed realization is retained for
diagnostics. A line with empty masks has no readings and fails. No claim of
completeness over all plausible English performances is made. In particular,
failure may reflect lexical stress, syllable-count, dialect, pronunciation
variant, or license restrictions of the model.

## Diagnostic interpretation and assurance boundary

A strict failure rescued by one of the named metrical rules is `LICENSED`.
A failure remaining under the enumerated rules is `ANOMALOUS` relative to this
specification. That category must not conflate an incomplete or conservative
annotation with a confidently established poetic irregularity. The catalogue
retains the failing lines and model evidence to make that distinction visible.

The kernel checks the encoded data and verdict equations. It does not certify
the edition's historical authority, the external dictionary, the textual
justification of elision indices, or the generator's lexical decisions.
Recorded source bytes, reproducible extraction/annotation, and a stated
hand-scanned validation sample are separate evidence for those boundaries.
Boundary theorems cover ordinary pentameter, each named license, tetrameter,
allowed third/fourth-foot and forbidden second/fifth-foot inversions, multiple
interior inversions, composition and excess substitutions, invalid or stressed
elisions, missing annotations, and preservation of fixed stresses.

## MD-SOURCE-ALIAS: editorial interpretation is explicit

The pronunciation model may supply a narrowly enumerated lexical alias with a
named textual witness, without changing the encoded source string. The first
such source-error annotation is `respose` → `repose`, supported by
[Folger's sonnet 27, line 2](https://www.folger.edu/explore/shakespeares-works/shakespeares-sonnets/read/27/)
(accessed 2026-11-10); its phones come from the pinned CMU entry for _repose_.
The proof therefore remains conditional on that interpretation, not a proof
that the Gutenberg token is historically attested. See PRONUNCIATION.md.

## MD-SOURCED-LEXICAL-READINGS and MD-LOCAL-LEXICAL-CONTEXT

Before constructing masks, the external annotator selects the documented full
three-syllable `temperate`, two-syllable `every` and `wandering`, one-syllable
`wires`, initial-stressed `antique`, and final-stressed `contents` at every
occurrence. Several are literal alternatives in the frozen
[CMU dictionary](https://github.com/cmusphinx/cmudict/blob/74790861f652b15e4ac49015a90074ad62a27690/cmudict.dict).
The marked `wand'ring` and syllabic `ever-fixèd` in
[Poetry Foundation's edition of 116](https://www.poetryfoundation.org/poems/45106/sonnet-116-let-me-not-to-the-marriage-of-true-minds)
support those two author phoneme annotations. The `fixed` expansion applies
only in determiner + `ever` + `fixed` + following-token frames, approximating
an attributive adjective. A verbal frame such as `have you ever fixed this`
retains the default pronunciation. This finite cue cannot certify a noun head;
other participles are unaffected.

Initial stress of `antique` is supported by Alexander Schmidt,
*Shakespeare-Lexicon*, vol. I, p. 43, *Antic* entry
([publisher scan](https://api.pageplace.de/preview/DT0400.9783112315330_A39774742/preview-9783112315330_A39774742.pdf)).
The [Audio Shakespeare pronunciation guide](https://www.audioshakespearepronunciationapp.com/shakespeare-pronunciation-dictionary/)
documents final-stressed `contents` in several plays. Historical stress evidence
is not a reconstruction of the modern phoneme segments used in these annotations.

A finite local noun-phrase heuristic selects initial stress for `record` after
specified determiners, a determiner plus `living`, or `this/that` followed by a
specified nominal continuation. Unclassified uses retain the CMU first reading.
The noun/verb distinction is attested by
[Cambridge](https://dictionary.cambridge.org/pronunciation/english/record).
The exact cue sets, source scope and ambiguous frames left untouched are in
PRONUNCIATION.md; this heuristic is not a general syntactic parser.

These are explicit lexical choices before scansion, separate from the single
indexed unstressed-elision license. Multiple selected contracted lexical words
may coexist without granting multiple scan elisions. No choice reads a sonnet
number, metrical target, syllable-count deficit, or rhyme partner. Text and pins
remain fixed. All sources above were consulted 2026-11-10. The development
sample motivated these revisions, so its improved agreement is regression
evidence rather than independent historical validation.

## Historical rhyme review is external evidence

The review in HISTORICAL-RHYME.md and data/historical-rhyme-review.json covers
the original 133 modern-model failures. It records the 236 unequal intended
pairs, 83 cross-class collisions and the non-fourteen-line structures of 99/126.
Sources include David Crystal's
[study of sonnet rhymes in original pronunciation](https://www.davidcrystal.com/Files/BooksAndArticles/-4836.pdf).
Per-pair citations, limitations and unresolved questions appear in DEVIATIONS.md.

This layer does not change MD-RHYME-EXACT or supply favorable pronunciation
classes. Historical support for an individual pair is not a complete check of
all seven classes, their 21 pairwise distinctions, or a single consistent
pronunciation model. Repeated identical tokens can obstruct the distinct-class
policy independently of vowel reconstruction. Such an obstruction is a fact
about the selected formal specification, not proof of a defective literary rhyme.

The generator checks the review's corpus hashes, ending words, exhaustive
baseline constraints, evidence references and status summaries. A fixed checksum
of the original failed-sonnet/class projection binds the baseline without
requiring Git at verification time. These checks establish data consistency;
the kernel does not validate the scholarship. Full historical scheme validation
remains open, and no historical-rhyme completeness theorem is asserted.
