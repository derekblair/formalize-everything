# Verified worked-case catalogue

`U` means Muhammad ibn Salih al-Uthaymin, [*Summary of the Fiqh of
Inheritance*](https://d1.islamhouse.com/data/en/ih_books/single3/en-fiqh-of-inheritance.pdf).
Page numbers are **PDF pages, counting the title page as page 1**. The book
was inspected on 2026-10-27. `B13632` is the [named comparative
answer](https://islamqa.info/en/answers/13632) documented in SOURCES.md.
All 31 vectors and their locators were checked against the live sources again
on 2026-11-01 during checkpoint recovery.

The numbers below are collective role shares, in the listed order. A source
that states integer portions or “the rest” determines an exact rational;
reducing those stated fractions is arithmetic transcription, not an invented
scenario. No calculator output is used as an oracle. The Lean case module
implements the following 31-case battery.

| ID | Heirs, in output order | Expected role totals | Regime | Exact source locator |
| --- | --- | --- | --- | --- |
| C01 | Husband; full sister | 1/2; 1/2 | Fixed | U p.3, estate-priority example: each receives 100 from the final distributable 200 |
| C02 | Three daughters; mother; father | 2/3; 1/6; 1/6 | Fixed | U p.8, “more than two daughters” example |
| C03 | Maternal sister; full sister; two paternal sisters; mother | 1/6; 1/2; 1/6; 1/6 | Fixed | U p.10, “one maternal sibling” example |
| C04 | Two maternal brothers; two full sisters | 1/3; 2/3 | Fixed | U p.10, “two maternal siblings” example |
| C05 | Son; daughter | 2/3; 1/3 | Residuary | U p.7, daughters by ta'sib example: two portions to son, one to daughter |
| C06 | Full brother; full sister | 2/3; 1/3 | Residuary | U p.9, full sisters by ta'sib through others |
| C07 | Paternal brother; paternal sister | 2/3; 1/3 | Residuary | U p.13, paternal sisters by ta'sib through others |
| C08 | Father; daughter | 1/2; 1/2 | Fixed + residue | U p.6, father by fard and ta'sib together |
| C09 | Daughter; full sister | 1/2; 1/2 | Fixed + residue | U p.13, agnates along with others: full-sister example |
| C10 | Wife; daughter; full brother | 1/8; 1/2; 3/8 | Fixed + residue | U p.7, daughter inheriting one half |
| C11 | Daughter | 1 | Radd | U p.18, radd for one inheritor |
| C12 | Two daughters | 1 collectively, 1/2 each | Radd | U p.18, radd for one category |
| C13 | Wife; mother; maternal brother | 1/4; 1/2; 1/4 | Radd, spouse excluded | U p.18, radd involving a spouse: final portions 1:2:1 |
| C14 | Husband; two full sisters | 3/7; 4/7 | Awl | U p.10, first complementary example: original shares 1/2 + 2/3, denominator 6 becomes 7 |
| C15 | Husband; mother; two full sisters; two maternal sisters | 3/10; 1/10; 2/5; 1/5 | Awl | U p.10, second complementary example: denominator 6 becomes 10 |
| C16 | Wife; two full sisters; maternal sister | 3/13; 8/13; 2/13 | Awl | U p.10, third complementary example: denominator 12 becomes 13 |
| C17 | Wife; two daughters; mother; father | 1/9; 16/27; 4/27; 4/27 | Awl | U p.11, fourth complementary example: denominator 24 becomes 27 |
| C18 | Husband; mother; father | 1/2; 1/6; 1/3 | Umari | U p.6, first Umari case: 3:1:2 portions |
| C19 | Wife; mother; father | 1/4; 1/4; 1/2 | Umari | U p.6, second Umari case: 1:1:2 portions |
| C20 | Husband; father | 1/2; 1/2 | Fixed + residue | U p.5, husband inheriting one half |
| C21 | Husband; son | 1/4; 3/4 | Fixed + residue | U p.5, husband inheriting one fourth |
| C22 | Wife; father | 1/4; 3/4 | Fixed + residue | U p.5, wife inheriting one fourth |
| C23 | Wife; son | 1/8; 7/8 | Fixed + residue | U p.6, wife inheriting one eighth |
| C24 | Mother; father | 1/3; 2/3 | Fixed + residue | U p.6, mother inheriting one third |
| C25 | Mother; son | 1/6; 5/6 | Fixed + residue | U p.6, mother inheriting one sixth |
| C26 | Paternal grandmother; son | 1/6; 5/6 | Fixed + residue | U p.7, one grandmother inheriting: explicitly father's mother |
| C27 | Paternal grandfather; son | 1/6; 5/6 | Fixed + residue | U p.7, grandfather by fard only; paternal definition as explained below |
| C28 | Mother; paternal grandfather | 1/3; 2/3 | Fixed + residue | U p.7, grandfather by ta'sib only |
| C29 | Daughter; paternal grandfather | 1/2; 1/2 | Fixed + residue | U p.7, grandfather by fard and ta'sib |
| C30 | Mother; four full brothers; father | 1/6; 0; 5/6 | Majority blocked-sibling rule | B13632, first view |
| C31 | Mother; four full brothers; father | 1/3; 0; 2/3 | Named blocked-sibling alternative | B13632, second view; `ignoreFatherBlockedSiblings` |

In C01 the translation uses the generic word “spouse”; its stated one-half
share identifies the husband, consistently with U p.5's spouse schedule.

U's grandfather examples follow its definition requiring an exclusively male
line and its example of exclusion of the father's father's father by the
father's father. Those identify the paternal grandfather. The contradictory
“mother's father” phrase in that same introductory paragraph is documented in
SOURCES.md and is not adopted. M-mother case 7 independently confirms that the
paternal grandfather represents the father in this Sunni rule family.

B13632 describes four brothers without specifying their degree. C30/C31
explicitly specialize that example to four full brothers; the cited rule
counts brothers of every degree under the majority view, and excludes all
father-blocked brothers under the named alternative. This specialization does
not change either of the source's stated mother/father outcomes.

## Additional source-backed rule checks

Policy regression assertions may check the specified rules directly. They are
labelled rule/model checks rather than additional externally supplied worked
cases; they must not be included in the 31 classical-case count.

## Unverified or excluded candidates

- **UNVERIFIED as a numerical worked case:** simultaneous spouse and blood
  sharer under `includeSpouses`. The policy has sources (IQ4855 and OM2017),
  but no inspected worked example supplying a particular final vector was used.
  Do not present a vector generated by the implementation as a sourced case.
- **UNVERIFIED as a numerical worked case:** the two-grandmother/father
  comparison under both paternal-grandmother policies. The policy is sourced,
  but no matching immediate-grandmother worked vector was selected here.
- **Excluded by scope:** U p.12 husband + mother + two maternal brothers + two
  full brothers is a mushtaraka example, with a school-specific zero for the
  full brothers. It is not silently used as a universal regression expectation.
- **Excluded by representation:** U p.18 daughter + son's daughter + mother
  (radd), since the son's daughter is not a role in milestone 1.
- **Not test authorities:** the suspect numerical passages in M-mother and the
  inaccessible PDF listed in SOURCES.md's fidelity record.
