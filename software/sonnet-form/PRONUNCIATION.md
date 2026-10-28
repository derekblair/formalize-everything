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
with every unresolved token and its sonnet/line location. At the recorded
corpus version, all 2,155 line endings resolve. One interior token remains
unresolved: **`respose`, sonnet 27, line 2**. That is the exact edition's
spelling. It is not silently changed to _repose_, and its line cannot receive
an unconditional successful metrical verdict from missing pronunciation data.

The edition's `debarre’d` is preserved as text and has an explicit pronunciation
annotation corresponding to _debarred_. These two different treatments are
visible decisions: ordinary morphological interpretation for `debarre’d`,
an unresolved apparent lexical error for `respose`.

CMU lexical stress is not sentence stress or a complete poetic scansion.
Stress flexibility, syllable contraction licenses, rhyme-class extraction,
and verdicts are defined in the Lean spec and corpus generator. Coverage does
not establish accuracy. In particular, author-supplied OOV entries, a single
pronunciation per word, modern rhotic vowels, and full syllabic archaic endings
can all create model-specific deviations.
