# Mirath — computational inheritance, milestone 1

An executable rational model of the fixed shares in An-Nisa 4:11–12 and
4:176 and their specified Sunni classical development: exclusion (hajb),
residuary priority ('asaba), proportional reduction ('awl), and surplus
return (radd). The general conservation theorem and 31 sourced numerical
cases are kernel checked. This is the implementation for [ticket #46](https://github.com/derekblair/formalize-everything/issues/46),
pending coordinator-appointed independent review.

## Build and trust boundary

```sh
cd software/mirath
lake build
```

The package pins `leanprover/lean4:v4.34.1` and uses only Lean's bundled
libraries, including core `Rat`; it has no Mathlib or external dependencies.
The default build includes all cases, domain checks, and `Mirath.Audit`.
That audit transitively checks every `Mirath.*` constant and every declaration
from the seven implementation/proof modules (including private/generated
declarations), permitting only `propext`, `Classical.choice`, and `Quot.sound`.
It also rejects project axiom declarations and missing expected imports.
There are no sorry/admit placeholders or native-decision proofs; the numerical
case proofs use `decide +kernel`.

## Public interface and theorem

`Config` holds natural-number counts for husbands/wives, parents, the paternal
grandfather, the two immediate grandmothers, sons/daughters, and full,
paternal, and maternal brothers/sisters. A share is the **collective total
for a role**; `perPersonShare` divides it equally among that role's members.
The public-treasury destination has no person count.

```lean
Mirath.distribute? : Mirath.Config → Option (Mirath.Allocation Mirath.Role)

theorem Mirath.distribution_total (c : Mirath.Config) (h : Mirath.Valid c) :
    Mirath.total (Mirath.distribution c) = 1
```

`distribution` is total on all inputs, but its advertised domain is `Valid`.
`distribute?` returns `none` outside that domain. `Valid` requires:

- At most one husband, parent, or immediate grandparent; at most four wives;
  no husband and wives together; arbitrary child/sibling counts.
- No unblocked paternal-grandfather/full-or-paternal-sibling combination,
  and no mushtaraka combination as defined in `Config.isMushtaraka`.
- Whenever fixed shares leave a surplus and there is no residuary, a
  nonzero return-recipient weight. This is a condition on available input
  recipients; it does not assume the output sum or conservation theorem.

An empty default configuration or a sole spouse with default nonspousal radd
is therefore rejected. The explicit inclusive-radd or treasury policy can
make a sole-spouse input valid. The typed model assumes the enumerated people
are otherwise eligible and that there are no omitted heirs relevant to the
distribution.

`distribution_total` covers every valid configuration, including unbounded
child/sibling counts and all named policy choices. Additional general proofs
establish nonnegative final shares, preservation of totals when repeated role
increments are aggregated, and conservation for every successful `distribute?`
result. The proof proceeds through a general rational settlement theorem,
not a finite case enumeration.

## Algorithm and source choices

The fixed-share schedule and residuary weights are defined separately.
If fixed shares exceed one, all fixed shares are scaled proportionally to
one. Otherwise, the remainder goes to the first eligible residuary class
(children, father, paternal grandfather, full siblings, paternal siblings).
With no residuary and a surplus, it goes proportionally to the selected
return recipients, or to the explicitly selected treasury account. The
canonical ledger has one entry for each of the 16 destinations, including
zeros, so a role's fixed share and residue are combined.

| Policy field | Default | Named alternative |
| --- | --- | --- |
| `raddPolicy` | `excludeSpouses` | `includeSpouses` (reported historical alternative) |
| `paternalGrandmotherPolicy` | `blockedByFather` | `inheritsWithFather` (Hanbali) |
| `motherSiblingPolicy` | `allSiblings` | `ignoreFatherBlockedSiblings` (specified Ibn Taymiyya/al-Sa'di case) |
| `surplusPolicy` | `returnToHeirs` | `publicTreasury` (classical Zayd/Malik/al-Shafi'i position) |

The default spouse exclusion is the majority position **among radd users**;
the package does not claim that radd itself is unanimous. The mother-sibling
alternative is limited to father-blocked siblings, with no extrapolation to
other blocking relations. The full [rule-source table and fidelity record](SOURCES.md)
give the verse/classical source next to each rule and document school
differences and source anomalies.

## Kernel-checked worked cases

[CASE-SOURCES.md](CASE-SOURCES.md) lists all 31 expected vectors, with named
sources and exact page/section locators: 29 examples from al-Uthaymin's
*Summary of the Fiqh of Inheritance* and the two positions in IslamQA 13632.
`CaseMatches` proves both validity and equality of the **entire** canonical
ledger, including absent and blocked roles. Coverage includes pure fixed
shares, pure residue, combined shares/residue, radd, the two Umari cases,
grandparents, and four awl denominators. The required husband/two-full-sisters
case proves the initial sum `7/6` and final shares `3/7` and `4/7`.

Separate domain checks test rejected input forms and the per-person meaning
of a sourced case. They are not counted as additional classical examples.
Unsourced candidate vectors for inclusive spousal radd and the paternal
grandmother/father policy comparison are marked **UNVERIFIED** and excluded
from the numerical case battery; their policy sources remain explicit.

## What this does NOT show

Conservation and nonnegativity prove properties of the encoded rules; they do
not prove that the historical sources were transcribed faithfully. Citations
and the sourced case battery expose that separate obligation to review.

The model excludes grandfather-versus-agnatic-sibling disputes, mushtaraka,
the Imami inheritance hierarchy, grandchildren and lower descendants,
ascendants above the immediate grandparents, the maternal grandfather,
nephews/uncles/cousins, dhawu al-arham, wala', multiple simultaneous kinship
relationships, uncertain death, pregnancy, missing persons, impediments to
inheritance, and local probate legislation. No theorem establishes identity,
marriage, survival, or legal eligibility from evidence. Debts, funeral costs,
and bequests/wasiyya are settled before this algorithm's distributable estate;
their computation is outside the model. Configurations with omitted relevant
heirs cannot be treated as complete inputs merely by leaving those heirs out.
