# Sabbatical and jubilee sources, coordinates, and scope

Sources consulted 2026-10-28 UTC. `BibleNumbers/Jubilee.lean` uses only Lean's
standard library. All numbered constants below are either source data or
explicitly derived arithmetic; no calendar datum is UNVERIFIED.

## Source register

| ID | Named published source and locator | Encoded facts |
|---|---|---|
| LEV25 | *King James Version*, Leviticus 25:3–4, 8, 10–11 ([Bible Gateway edition](https://www.biblegateway.com/passage/?search=Leviticus%2025%3A1-12&version=KJV)) | Six agricultural years followed by a seventh-year land sabbath; seven groups of seven years total 49; the designated jubilee is the fiftieth year. |
| NED61-D | *Babylonian Talmud*, Nedarim 61a, William Davidson Edition ([Sefaria](https://www.sefaria.org/Nedarim.61a?lang=bi)), discussion beginning with the vow “for a Jubilee” and following baraita | The Rabbis exclude the jubilee year from the following seven-year cycle; Rabbi Yehuda includes it in that cycle. This gives the full-50 and overlapping-49 period alternatives. |
| NED61-S | *Babylonian Talmud*, Nedarim, Soncino English translation, folio 61a ([Halakhah transcription](https://halakhah.com/nedarim/nedarim_61.html)), same discussion and notes 6–11 | Independent English cross-check of the above two readings and their implications for agricultural-year counting. |

The search hit Rosh Hashanah 9a:3 identified another primary locus but its
initial page scrape returned no text. The complete Nedarim 61a texts above
were read instead. Search-engine snippets and secondary discussion are not
used as numerical authority.

## Numerical provenance

| Quantity | Value | Status and source |
|---|---:|---|
| Sabbatical period | 7 | Source datum, LEV25 v.4 |
| Number of seven-year groups | 7 | Source datum, LEV25 v.8 |
| Elapsed years in those groups | 49 | Source datum, LEV25 v.8; also 7×7 |
| First numbered jubilee year | 50 | Source datum, LEV25 vv.10–11 |
| Overlapping jubilee period | 49 | Interpretation parameter, NED61-D/NED61-S: the fiftieth year is also the first of the next cycle |
| Full jubilee period | 50 | Interpretation parameter, NED61-D/NED61-S: the fiftieth year is excluded from the next cycle |
| Common period | 2,450 | Derived by `period_lcm`, `period_products`, and `realignment_minimal`; not a source datum |
| Next shared numbered jubilee | 2,500 | Derived from common first year 50 plus recurrence gap 2,450 |
| Zero and one used for epochs, indices, increments | 0, 1 | Mathematical indexing conventions, not claimed as textual numbers |

## Coordinates and theorems

`IsSabbatical y` means that `y` is positive and divisible by seven on a
**continuous seven-year reference grid**. The epoch is year zero; counted
civil-year labels begin at one. `sabbaticalCount start span` genuinely
inspects each year in `(start, start + span]`; its quotient expression is a
proved theorem, not its definition:

`count(start, span) = floor((start + span)/7) − floor(start/7)`.

`boundary reading k` is the elapsed duration of `k` periods: `49k` or
`50k`. Thus 49-year boundaries always have phase zero modulo seven, while
50-year boundaries have phase `k mod 7`, advancing by one per cycle. The
number of sabbaticals from the epoch through `k` periods is respectively
`7k` or `7k + floor(k/7)`. The theorem for arbitrary starts additionally
shows seven sabbaticals in any 49-year interval; a 50-year interval contains
seven or eight according to its starting phase.

`jubileeYear reading k` uses the text's **numbered year 50** for the first
jubilee, followed by `50 + 49k` or `50 + 50k`. Consequently the overlapping
jubilees remain at phase one, immediately after a sabbatical; full-period
jubilees have phase `(k+1) mod 7`. This is distinct from calling the elapsed
49-year boundary itself the fiftieth numbered year.

`common_multiple_iff` characterizes *all* common period multiples as
multiples of 2,450. `realignment_2450` and `realignment_minimal` prove that
2,450 is the first positive such duration. `boundary_coincidence` gives
50 short periods = 49 long periods. With a common first jubilee numbered 50,
`jubileeYear_next_coincidence` and `jubileeYear_coincidence_minimal` give the
next common label 2,500 and prove no earlier positive recurrence. The
2,450-year headline is a duration, not a claim that the first common
numbered jubilee is year 2,450.

## Fidelity events and what these results do not show

1. **Continuous versus restarted sabbatical counting.** NED61-D explicitly
   says that, under the Rabbis' full-50 reading, the seven-year cycle starts
   again in the year after the jubilee. That calendar is not the uninterrupted
   seven-year grid required for the milestone's requested 50-year drift
   comparison. Our `IsSabbatical` predicate deliberately denotes that common
   reference grid. The full-50 drift and counts are conditional mathematical
   comparisons against it; they must not be presented as a formalization of
   the Rabbis' entire restarted calendar. No source claim was altered to
   make a drift theorem true.
2. **Boundary versus numbered year.** Identifying the elapsed 49-year boundary
   with the text's numbered fiftieth year would conceal an off-by-one change.
   Both coordinates are modeled explicitly, with separate proved phases.
   Likewise, the first positive period realignment is 2,450 elapsed years,
   but after the initial common jubilee at year 50 the next common label is
   2,500.
3. These results choose neither interpretation as historically correct, prove
   no historical observance or civil-date epoch, and assert no theological
   conclusion. The source choices motivate the two period parameters; Lean
   checks the arithmetic of those stated parameters and conventions.
4. No arithmetic contradiction was found in the cited Leviticus figures.
   The contrast between uninterrupted and restarted sabbatical counting is
   a modeling distinction, not a source arithmetic error.
