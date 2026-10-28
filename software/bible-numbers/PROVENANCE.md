# Genealogy data provenance and fidelity record

The Lean results concern the finite datasets in `BibleNumbers/Data.lean`. They
make no assertion about the historicity of the events, the age of the world,
which witness is original, or the completeness of the manuscript tradition.
The dataset names identify source profiles, not an edition-critical consensus.

## Reproducible cell-level table

[`data/provenance.csv`](data/provenance.csv) is the requested provenance table:
one row for each **variant, witness, chapter, patriarch, field, value, status,
source, locator**. Its 360 rows contain 298 sourced numeric cells, 56 fields
not explicitly stated, and six cells belonging to an absent patriarch.
[`data/chronology-inputs.csv`](data/chronology-inputs.csv) records the twelve
variant-indexed Flood bridge inputs. [`data/comparison-values.csv`](data/comparison-values.csv)
records the separately sourced interpretive and printed comparison values.

The CSV is the source of truth for the generated Lean numeric table:

```sh
python3 scripts/generate_data.py          # regenerate Data.lean
python3 scripts/generate_data.py --check  # verify exact agreement without writing
```

The generator rejects duplicate cells, missing source identifiers, incomplete
inventories, numeric cells without `SOURCED` status, and an absent patriarch
with partially populated fields. Generation is not a proof mechanism: Lean's
kernel checks the theorems using the generated explicit numeral definitions.

## Named sources

| Source ID | Published source and exact consulted location |
| --- | --- |
| `Smith2018` | Henry B. Smith Jr., **“MT, SP, or LXX? Deciphering a Chronological and Textual Conundrum in Genesis 5,” Bible and Spade 31.1 (2018), pp. 18–27**. [Author's published PDF](https://www.biblearchaeology.org/images/Genesis-5-and-11/Smith-Henry-Winter-2018-BAS_MT-SP-or-LXX.pdf). Table 2, printed p. 19, supplies the three-witness cells; notes A–J distinguish readings, alternatives, and reconstructions. Table 1, p. 18, and Table 4, p. 25, supply comparison chronologies and endpoint interpretations. Table 3, p. 23, supplies the SP Flood coordinate. |
| `Millam2010` | John Millam, **The Genesis Genealogies**, revised June 2010. [Published paper mirror](https://www.onthewing.org/user/G1_Genesis%20Genealogies%20-%20Millam.pdf). Table 7, p. 37, cross-checks Genesis 5 begetting ages and the two Methuselah readings, and reports the longer LXX Nahor reading. Table 6, p. 36, is examined as a comparison and contains the issues recorded below. |
| `Brenton` | Lancelot Charles Lee Brenton, **The Septuagint Version of the Old Testament**, public-domain English translation, `eng-Brenton` digital transcription: [Genesis 5](https://cyber.bible/study/content/texts/eng-Brenton/GN5.html), [Genesis 7](https://cyber.bible/study/content/texts/eng-Brenton/GN7.html), [Genesis 11](https://cyber.bible/study/content/texts/eng-Brenton/GN11.html). The main text and every printed numerical `Alex.` footnote in chapters 5 and 11 are distinguished. The [edition index](https://ebible.org/eng-Brenton/) includes an 1844 preface and 1870 introduction; this package does not pretend that the web transcription is a newly collated manuscript or identify it with a particular scanned printing. |
| `JPS1917` | **The Holy Scriptures According to the Masoretic Text**, Jewish Publication Society (1917), [Mechon-Mamre edition identification](https://mechon-mamre.org/e/et/et0.htm); [Genesis 7:6](https://mechon-mamre.org/p/pt/pt0107.htm), [Genesis 11:10–32](https://mechon-mamre.org/p/pt/pt0111.htm). These independently cross-check the MT Flood bridges and the MT chapter 11 numerals. |

Sources were read on 2026-10-28 UTC (2026-10-27 local). Only numeric facts,
short bibliographic identifiers, and our own analysis are committed; article
prose and extended source transcriptions are not copied into the package.

## The six comparison profiles

| Lean variant | Witness | Exact meaning |
| --- | --- | --- |
| `mt` | MT | Smith Table 2's **actual MT** readings, taking the unbracketed values identified by notes E, H, I, J. |
| `sp` | SP | Smith Table 2's extant SP profile, including its explicitly reported Genesis 11 lifespans. |
| `lxxSmith` | LXX | Smith Table 2's first-listed LXX readings: Methuselah 187/782; Arpachshad remaining 430; Shelah remaining 403; Eber remaining 370; Nahor 79/129. It is a published table profile, not a claim that all these choices identify one named manuscript. |
| `lxxBrenton` | LXX | Brenton's main text: Methuselah 167/802; Arpachshad remaining 400; Shelah remaining 330; Eber remaining 270; Nahor 179/125. |
| `lxxArp330` | LXX | Smith Table 2's explicitly printed second Arpachshad remaining-years reading, 330, isolated against the `lxxSmith` profile. This is a **one-cell sensitivity profile**; Smith does not name the manuscript or establish co-occurrence of all its other cells. No single-manuscript claim is made. |
| `lxxShelah330` | LXX | Brenton with **all printed `Alex.` numerical footnotes** applied: Methuselah 187/782; Arpachshad remaining 430; Eber remaining 370; Nahor 79/129; unchanged main-text Shelah remaining 330. Numerically it differs from `lxxSmith` only at Shelah, and independently realizes the alternative Smith mentions in note G. It records Brenton's apparatus, not an independent new collation of Codex Alexandrinus. |

No average is taken. The Arpachshad 330 and Shelah 330 alternatives are not
silently combined into an allegedly attested manuscript. These six named
profiles delimit the universe of the proved pairwise comparisons; this is not
an exhaustive catalogue of every surviving LXX or SP manuscript reading.

## Fields, omissions, and endpoint conventions

- Genesis 5 rows run from Adam through Noah; Genesis 11 rows run from Shem
  through Terah, with the LXX's additional Kainan represented separately from
  the antediluvian Kenan. Abraham is the terminal offspring, not a row with a
  begetting number stated in Genesis 11.
- `Row.begetting` stores the raw number, including Noah **500** in Genesis
  5:32 and Terah **70** in Genesis 11:26. Neither three-son notice proves that
  the first named son was born at that age. No inferred **502** for Noah's age
  at Shem's birth is substituted for the raw 500.
- `remaining` means years **after the reported begetting event**. Smith's
  Noah entry of 350 is explicitly **after the Flood**; it is therefore not
  inserted into this field. Noah's remaining cell is `none`, and his stated
  lifespan 950 is retained with its Genesis 9:29 locator.
- Terah's parenthesized 75 in Smith Table 2 is an inferred residual associated
  with a chosen Abraham endpoint, not a remainder explicitly stated after the
  raw age 70. His remaining cell is `none`; his stated lifespan is 205 in
  MT/LXX and 145 in SP.
- The MT and LXX do not explicitly give total lifespans for the intermediate
  Genesis 11 rows. Those cells are `none`, not the arithmetic sum of the two
  stated ages. Smith Table 2 and the discussion on p. 20 identify the SP's
  explicit lifespan additions; they are retained as given. Thus a
  present-versus-absent lifespan cell is a real dataset divergence, separate
  from a disagreement between two stated numerals.
- Kainan's entire row is absent from the MT/SP profiles. These are
  `ABSENT_PATRIARCH` cells, not an unsourced zero-year generation. Chronological
  paths deliberately omit that generation for MT/SP and include it for LXX.
- Adam-to-Flood totals add the Adam-through-Lamech begetting numbers to
  Noah's **600** at the Flood (Genesis 7:6), not to Noah's raw 500.
- Flood-to-Abraham totals begin with the **2** years from Flood to Arpachshad
  (Genesis 11:10), then follow the stated begetting path. The SP bridge is
  independently represented by Smith's Flood 1307 and Arpachshad 1309
  coordinates in Tables 3/4; MT and LXX are also checked directly in JPS and
  Brenton respectively.
- The **70** endpoint is the literal Terah row arithmetic. The **130** endpoint
  is an explicitly separate interpretive input documented in Smith Table 4,
  notes D–F, using Genesis 11:32, Genesis 12:4, and Acts 7:4. It must not be
  disguised as the numeral in Genesis 11:26. Applying 130 to SP is a
  sensitivity calculation, not the SP's own inferred endpoint (145−75=70).

## Source disagreements and fidelity events

1. **MT reconstructions versus readings.** Smith Table 2 prints proposed
   values in brackets: Arpachshad remaining 430, Eber remaining 370, Nahor
   remaining 129. Notes E/H/I/J explicitly identify actual MT readings as
   **403, 430, 119**. The actual readings populate `mt`; the proposals are
   recorded separately in `comparison-values.csv`, not relabelled as MT.
2. **LXX is not a single numeric table.** Smith, Brenton's main text, Brenton's
   `Alex.` apparatus, and Smith's extra slash reading disagree at the cells
   described above. Every encountered Table 2 slash alternative is represented
   by a named profile. Millam Table 7's 167-or-187 Methuselah and 179 Nahor are
   preserved by these profiles, rather than reconciled away.
3. **Smith's reconstructed versus extant totals.** Table 1 uses Lamech 182 and
   prints Adam-to-Flood **2256**. Table 2's LXX profile instead has Lamech 188,
   yielding **2262**, six more. Table 4's LXX Adam-to-Abraham **3388** uses the
   Table 1 base, whereas Table 2 data plus the same 1132 post-Flood interval
   yields **3394**. This is an explicitly explained change of input profile,
   not evidence that addition is wrong or authority to change Table 2's 188.
4. **Smith's blanket compensation claim needs qualification.** The prose on
   p. 26 says the SP's Arpachshad-through-Serug remaining years are each 100
   lower than MT. For the *actual* MT Eber cell **430**, versus SP **270**, the
   difference is **160**. The 100 pattern holds there only using Smith's
   conjectured 370. The formal pattern theorems must restrict the constant
   offset to the cells where it actually holds.
5. **Millam Table 6 column semantics.** Its Genesis 11 column headed “Age at
   Death” contains Shem **500**, Arpachshad **403**, etc., the remaining-year
   numerals rather than total lifespans. These values are not copied into a
   lifespan field. For Shem the same row prints birth **1556**, death **2036**:
   even birth plus the displayed 500 is **2056**, not 2036. The source row is
   recorded as inconsistent; the verified input is not adjusted.
6. **Millam Table 6's post-Flood chronology.** Arpachshad is placed at **1656**,
   the MT Flood coordinate, instead of two years later. Its Abram coordinate
   **1946** is therefore two below the **1948** obtained from the encoded MT
   numbers with the literal 70 endpoint. Table 6 also labels Adam's birth as
   year 1 while later columns use sums from zero. Our elapsed-year origin and
   the Genesis 11:10 two-year bridge are explicit; no numbers are altered to
   reproduce the table's dates.
7. **Millam Table 7's Noah heading.** The row **600** appears under a fatherhood
   heading, although Table 6 and Genesis 5:32 give **500**. The 600 is used only
   as the Genesis 7:6 Flood endpoint, whose semantics are independently
   checked in the primary translation texts.
8. **Partial historical SP report.** Smith p. 24 quotes Jerome reporting SP
   Methuselah **187/782/969** and Lamech begetting **182**. These explicitly
   named historical readings are preserved in `comparison-values.csv` as
   `PARTIAL_HISTORICAL_REPORT`. They do not determine a complete historical SP
   dataset, so no unreported cells are filled from the modern SP and no total
   is asserted for that partial report. The six complete comparison profiles
   concern the chosen published tables/editions, not every historical report.
9. **Explicit versus inferred values.** Noah's post-Flood 350, inferred Shem
   link 502, Terah's parenthesized 75 and inferred 130, and computed Genesis 11
   lifespans are not silently promoted into raw genealogical fields. The
   130 endpoint is separately parameterized and sourced.

## UNVERIFIED inventory

**No unsourced numeric datum is included in `Data.lean`, and the numeric
UNVERIFIED input list is empty.** All 298 included genealogy numerals and all
12 bridge inputs have named source locators. `NOT_STATED` and
`ABSENT_PATRIARCH` are positively identified textual omissions, not unverifiable
numbers. The incomplete Jerome report is explicitly partial and has no proved
total; its unknown other cells are not assigned numbers. Smith's reconstructions
are sourced scholarly proposals, not unverifiable quotations, and are excluded
from the raw MT dataset for that distinct reason.
