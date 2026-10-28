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
| `initialTrochaicInversion` | The first foot is strong–weak; inversion is allowed only in that foot. |
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
allowed only in the initial foot; weak–weak and strong–strong substitutions
are allowed in any foot. A feminine ending and elision do not consume this
two-foot budget and can combine with each other and the substitutions.

The two-foot bound is a conservative modeling choice, not a theorem about all
historical metrical practice. No medial inversion, anapestic expansion,
acephalous line, or arbitrary syllable insertion is granted. A line rejected
because it needs an unenumerated license is a failure **under this model**.
The strict and licensed checks are both recorded so the impact of licenses is
visible. A tetrameter cannot pass by invoking these licenses: deletion never
creates the missing fifth foot.

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
medial inversion, excess substitutions, invalid or stressed elisions, missing
annotations, and preservation of fixed stresses.
