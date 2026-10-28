# Rule provenance and fidelity record

Sources were inspected on 2026-10-27. This is a computational model of a
specified Sunni fara'id ruleset, with named alternatives where implemented;
it is not a statement that every historical school gives identical answers.
The input estate is the distributable balance after prior obligations.

## Source keys

| Key | Inspected source and locator |
| --- | --- |
| Q4:11 | [Qur'an, An-Nisa 4:11](https://quran.com/4/11), children and parents. |
| Q4:12 | [Qur'an, An-Nisa 4:12](https://quran.com/4/12), spouses and maternal siblings. |
| Q4:176 | [Qur'an, An-Nisa 4:176](https://quran.com/4/176), non-maternal siblings. |
| U | Muhammad ibn Salih al-Uthaymin, [*Summary of the Fiqh of Inheritance*](https://d1.islamhouse.com/data/en/ih_books/single3/en-fiqh-of-inheritance.pdf), English translation of *Talkhis Fiqh al-Fara'id*, 22-page PDF. Page references below count the title page as PDF page 1. |
| IQ4855 | Ibn Qudama, [*al-Mughni*, Kitab al-Fara'id, section 4855](https://www.islamweb.net/ar/library/content/15/4186/مسألة-يرد-على-كل-أهل-الفرائض-على-قدر-ميراثهم), volume 6, pp.185–186, radd and treasury alternatives. Arabic text inspected. |
| M-mother | Muhammad Jawad Mughniyya, [*Inheritance according to the Five Schools of Islamic Law*, “The Mother's Share in Inheritance”](https://al-islam.org/inheritance-according-five-schools-islamic-law-muhammad-jawad-mughniyya/mothers-share-inheritance), cases 7, 14, subsection “Does the Mother Take One-Third of the Remainder?”, and footnote 1. Used for school differences, not numerical test expectations. |
| B13632 | Muhammad Salih al-Munajjid, [IslamQA answer 13632, “Division of inheritance among a mother, father and four brothers”](https://islamqa.info/en/answers/13632), 19 May 2001. It identifies the majority and Ibn Taymiyya/al-Sa'di alternatives and gives their classical locators. |
| OM2017 | Nizaita Omar and Zulkifly Muda, [“Change of Mazhab (School of Thought): The Effects on Inheritance in Islamic Family Law”](https://hrmars.com/papers_submitted/3504/Change_of_Mazhab_(School_of_Thought)_The_Effects_on_Inheritance_in_Islamic_Family_Law.pdf), *IJARBSS* 7(11), 2017, pp.633–642, DOI 10.6007/IJARBSS/v7-i11/3504; especially p.636 (PDF page 4), views on radd. |

## Rule-source table

All numerical entitlements below are collective role totals; equal division
within a role is separate from the male/female weight ratio between roles.

| Rule implemented | Source |
| --- | --- |
| Daughter: 1/2 alone, 2/3 collectively when plural and no son; son/daughter ratio 2:1 | Q4:11; U, “Daughters,” pp.7–8 |
| Parents: sixths with children; mother's third without descendants or reducing siblings | Q4:11; U pp.6–7 |
| Husband: 1/2 or 1/4; wife/wives: 1/4 or 1/8 depending on descendants | Q4:12; U pp.5–6 |
| One maternal sibling: 1/6; several: 1/3 collectively, equally without a sex multiplier | Q4:12; U p.10 |
| Full/paternal sisters: 1/2 or 2/3; brothers convert their corresponding sisters to 2:1 residuaries | Q4:176; U pp.9–10,13 |
| Father: fixed sixth with son; sixth plus residue with daughter; residue without children | U p.6, “Father's share” |
| Paternal grandfather substitutes when father absent, excluding disputed sibling combinations | U p.7, “Grandfather's share”; exclusions below |
| Mother takes one third of residue in spouse-plus-both-parents cases, not when grandfather replaces father | U p.6; M-mother, “Does the Mother…” |
| Mother blocks grandmothers; eligible grandmothers share 1/6; father blocks grandfather | U p.7; M-mother case 7 and footnote 1 |
| Father/son block siblings; descendants and male ascendants block maternal siblings | U pp.9–10,16–17 |
| Full brother blocks paternal siblings; one fixed-share full sister allows paternal sisters a collective completing 1/6; two fixed-share full sisters block paternal sisters unless paternal brother makes them residuaries | U pp.9–10 |
| Sisters with daughters become residuaries; full sisters then precede paternal siblings | U pp.9,13 |
| Residue priority within represented roles: sons, father, paternal grandfather, full siblings, paternal siblings | U pp.12–15, “Agnates” and “Order of Agnates” |
| Proportional awl when fixed shares exceed the estate | U pp.10–11, “A Complementary Section” |
| Proportional radd where no residuary exists; spouses excluded by default | IQ4855; U pp.17–18 |

The count limits describe the finite representation: single parents and immediate
grandparents, one husband or up to four wives, arbitrary natural counts for
children and siblings. The four-wife cap follows [Qur'an 4:3](https://quran.com/4/3)
and is an input constraint, not an extra inheritance fraction. These bounds do
not establish marriage, identity, survival or legal eligibility from external
evidence.

## Variants and excluded disputes

The default spouse policy excludes spouses from radd. IQ4855 describes this as
the general position among those who apply radd; it reports a contrary act by
Uthman but offers other explanations for that act. OM2017 p.636 explicitly
describes the reported inclusive position. `includeSpouses` represents that
reported alternative; it is not labelled a standard four-school consensus.

Radd itself is not universal across the classical schools. IQ4855 assigns the
surplus-to-treasury position to Zayd, Malik and al-Shafi'i. A treasury alternative
must be explicit in the configuration; the default return-to-heirs convention
is the radd framework requested by the milestone. “Majority” here describes
exclusion of spouses among radd users, not a claim that the early four schools
all applied radd.

M-mother case 7 and footnote 1 distinguish the paternal grandmother's exclusion
by the father from the Hanbali permission to inherit alongside him. The model's
default is exclusion; `inheritsWithFather` is the named alternative. Its ordinary
mother-blocking rule remains in effect under either choice.

B13632 states that siblings blocked by the father still reduce the mother's
share under the majority position; it also records the contrary Ibn Taymiyya/
al-Sa'di principle that only siblings with a right to inherit cause reduction.
`allSiblings` is the default. `ignoreFatherBlockedSiblings` implements the
explicit father-present case. It does not extrapolate the alternative to other
blocking relationships or to exhaustion of the estate by fixed shares.

Grandfather versus full/paternal siblings is excluded when the grandfather is
not himself blocked by the father. The common-third case (mushtaraka/himariyya)
is also excluded: husband, mother or grandmother, multiple maternal siblings
and a full brother can produce different Hanafi/Hanbali and Maliki/Shafi'i
answers (M-mother case 14). These are rejected scope boundaries, not cases
silently forced through a preferred school's formula.

Other excluded frameworks and persons: the Imami inheritance hierarchy;
descendants below children; ascendants above the immediate grandparents;
maternal grandfather; nephews, uncles and cousins; dhawu al-arham; wala';
multiple simultaneous kinship relationships; uncertain death, pregnancy and
missing persons; impediments to inheritance; local probate legislation; debts,
funeral costs and wasiyya before the distributable estate is computed.

## Fidelity events during source work

1. The Hanbali textbook's paternal-grandmother-with-father rule was identified
   as a school-specific choice and separated from the default by a named policy.
2. The radd-versus-treasury disagreement was identified; the documentation does
   not describe radd as unanimous, and the implementation exposes the alternative.
3. The spousal-return report is labelled a reported minority alternative; no
   unsupported attribution of inclusive radd to a standard school was made.
4. The mother/blocked-siblings disagreement was identified and communicated to
   the model implementation. The default remains the documented majority rule.
5. U PDF p.7 contains an internally contradictory example in the grandfather
   definition: “mother's father” follows a definition requiring no female link.
   The model uses the paternal grandfather, consistently with the definition and
   M-mother case 7. The contradictory phrase was not copied into the model.
6. M-mother's online chapter contains suspect numerical statements (notably its
   maternal-sibling plural example and its full-plus-paternal-sister example).
   It is used only for the specific comparative passages identified above. No
   case expectation is taken from those suspect numerical passages.
7. A search result for a Hanbali inheritance PDF at thethinkingmuslim.com led
   to a “Coming Soon” page. That inaccessible document is not a rule or case
   authority in this package.
8. Every selected numerical worked example is traceable in CASE-SOURCES.md.
   Candidate cases lacking a checked expected distribution are explicitly
   separated there; they cannot be promoted to sourced tests by computation.
