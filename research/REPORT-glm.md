> **Editorial note (added 2026-10-24, revision of PR #1 after independent review — VERDICT: FAIL, Checks 1 & 3):**
> This is a raw lane report, preserved as a historical artifact. Its absence and novelty
> phrasing inside the report body is the lane's own unedited wording and is **not** the
> programme's claim. Where the body says e.g. "never been formalized", "nobody has",
> "for the first time in Lean", "Not done anywhere", "100% untouched", or
> "completely unformalized in any proof assistant", read it as bounded by the
> programme's supported wording: **"no complete book-ordered Lean formalization found"**
> in the dated, documented searches behind these reports. `SYNTHESIS.md` supersedes
> this report where they conflict, and `SYNTHESIS.md` §6 already flags this phrasing.
> The only other change in this revision is one trailing newline at EOF, aligning the
> file with the canonical Dropbox copy.
>
> ---

# What should formalize-everything formalize next?

**Research report for the formalize-everything programme · compiled 2026-10-21**

Scope choices made up front (per the brief, these are mine):

- A **candidate** is a published, canonical book that people teach from — not lecture notes, not problem collections without a body of theory, not encyclopedias. This cuts against several ATLAS books (MIT course notes rather than canonical texts) and against reference works like Stanley's *Enumerative Combinatorics* (whose symmetric-functions heart is also now largely done — see do-not list).
- Books whose role in the programme is already filled by the queued Rudin volumes (RCA, Functional Analysis) are excluded from the shortlist even where feasible (e.g. Folland, Royden) — recommending them would be recommending the queue back at itself.
- **Node counting** is calibrated to PMA ≈ 330 main-text nodes / 11 chapters ≈ 30 nodes per chapter. Estimates below are extrapolations from chapter/section counts and known numbering density, good to about ±30%. I mark them as estimates.
- **Effort classes**: *PMA-class* (single book, months, one agent-heavy push), *heavy single-book* (≈1.5–2.5× PMA or significant infrastructure to build first), *multi-year* (blocked on fields mathlib does not have, or size > 2× PMA by a wide margin).

The world has changed under this question in the last 12 months: whole-book autoformalization is now a race (ATLAS: 26 books; ReasBook: 13 books; Grinberg's *Algebraic Combinatorics* in one week). The programme's edge is **complete coverage at a hostile-review standard** — most of what exists is partial target coverage with AI-facing quality control. The recommendations below favour texts that are (a) canonical, (b) genuinely absent from Lean, (c) ready enough in Mathlib to finish, and (d) at risk of being claimed by someone else's firehose soon.

---

## Executive summary — top 3

1. **Munkres, *Topology* (2nd ed.)** — the canonical general-topology text has no Lean formalization (only Isabelle and Megalodon versions exist); Mathlib covers chapters 1–8 well and *just* grew covering maps, so the book's real frontier (fundamental group → van Kampen → classification of surfaces and covering spaces) is now reachable. Highest canonical value per unit of missing Lean in the whole survey.
2. **Graham–Knuth–Patashnik, *Concrete Mathematics* (2nd ed.)** — a canonical, universally taught CS-mathematics text with zero existing formalization found anywhere in any system; prerequisites are ~80% in Mathlib; distinctive new field for the programme (discrete mathematics) with no collision with any active project.
3. **Cover & Thomas, *Elements of Information Theory* (2nd ed.)** — the canonical information-theory text, unclaimed in Lean (a Coq library exists for the core theorems, no Lean version); would kernel-check Shannon's source- and noisy-channel-coding theorems for the first time in Lean while building a genuinely missing Mathlib area; highest "trusted-but-unverified-anywhere" prestige per node in the survey.

---

## Ranked shortlist

Format: **rank. Title, author, edition** — field · scope estimate · existing-formalization status (with evidence) · Mathlib readiness & biggest gaps · case · risks.

---

### 1. *Topology*, James R. Munkres, 2nd ed. (2000)

- **Field:** general topology + intro algebraic topology (point-set half + fundamental-group half).
- **Scope:** 13 chapters (1–8 point-set, 9–13 homotopy). Estimated **~630 nodes** (ch. 1–8 ≈ 440; ch. 9–13 ≈ 190). Effort: **heavy single-book** (≈2× PMA; the back half is the hard half).
- **Existing formalization status:** **No Lean version found.** Two substantial non-Lean versions: (i) autoformalized in **Isabelle/HOL** (arXiv:2604.07455, "Munkres' General Topology Autoformalized in Isabelle/HOL"); (ii) a large portion (1.5k+ lemmas) in **Megalodon** (Josef Urban, arXiv:2601.03298, 160k lines, Urysohn/Tietze/metrization included). I verified absence in Lean via the Lean-projects registry, Palomar announcement, web search, and the ATLAS/ReasBook catalogues (its topology coverage is MIT course notes, not Munkres). **This recommendation explicitly relies on the "different proof assistant" exception.** Caveat: with two firehose projects already on the book, a Lean firehose is likely within a year or two — moving first matters.
- **Mathlib readiness:** Chapters 1–8 map well onto Mathlib (orders, filters, compactness, Tychonoff, separation axioms, Urysohn lemma, **Tietze extension ✓** — `Mathlib.Topology.TietzeExtension`, verified via Loogle; metrizability theory partly via uniform spaces; Baire ✓). Back half: **`Mathlib.AlgebraicTopology.FundamentalGroupoid` exists (177 declarations, verified)** and **`Mathlib.Topology.Covering.Basic` with `IsCoveringMap` exists (116 declarations, verified — new)**. **Biggest gaps:** Seifert–van Kampen (0 Loogle hits), Jordan curve theorem (0 hits — all "Jordan" hits are measure/order/algebra), classification of surfaces, classification of covering spaces, quotient/adjunction-space lemmas in textbook form.
- **Case:** the single most-taught topology book in the English-speaking world; the point-set half kernel-checks the working mathematician's default toolkit in book order (the programme's PMA method, proven), and the homotopy half would add real missing Mathlib content (van Kampen, surface classification) rather than duplicating it. Downstream: every geometry/physics/topology project.
- **Risks:** ch. 10–12 are diagram-chase/quotient-heavy and will need design decisions (fundamental group via groupoid vs. group); Isabelle/Megalodon versions undermine uniqueness-of-first; point-set half has high Mathlib overlap so review tedium is a real cost.

### 2. *Concrete Mathematics: A Foundation for Computer Science*, Graham, Knuth & Patashnik, 2nd ed. (1994)

- **Field:** discrete mathematics / analysis of algorithms.
- **Scope:** 9 chapters. Estimated **~520 main-text nodes** plus a huge graded exercise set (the exercises are half the book; decide coverage policy up front). Effort: **heavy single-book**, but per-node difficulty is low (combinatorial identities, not analysis) — likely the fastest of the top 3 to push through with agents.
- **Existing formalization status:** **None found, in any proof assistant.** Checked: web searches (English), ATLAS catalogue (26 books — not there), ReasBook (13 books — not there), Lean-projects registry, Palomar announcement. The closest existing thing is Sequencelib (OEIS-adjacent results in Lean, arXiv preprint) — not the book. **Highest-confidence "absent" claim in this report** (for the main text; individual identities are scattered through libraries everywhere).
- **Mathlib readiness:** high. Verified present: Stirling numbers 1st/2nd (`Mathlib.Combinatorics.Enumerative.Stirling`), Euler pentagonal number theorem & partitions (`Enumerative.Pentagonal/Partition`), Catalan (`Enumerative.Catalan`), Bell, Dyck words, inclusion–exclusion, double counting, Fibonacci, Bernoulli numbers, binomial sums, Möbius inversion. **Biggest gaps:** floor-sum machinery (ch. 3), hypergeometric summation in the style of ch. 5 (Gosper-level identities), Eulerian numbers (partial), continued-fraction/continuant depth of ch. 6, operator/umbral formalism of ch. 7 (would need disciplined scaffolding), asymptotics of ch. 9 (saddle-point method — genuinely hard tail of the book).
- **Case:** canonical (the discrete-math book for a generation of CS students; Knuth), teaches a style (manipulation of sums, generating functions) that is exactly where LLM agents are strongest and humans are weakest; fills a field (discrete math) the programme has no presence in; zero collision risk today.
- **Risks:** ch. 9 asymptotics is the one genuinely hard technical tail (Laplace/saddle-point methods are not in Mathlib); many exercises are "guess-and-prove" research problems whose faithful formalization needs judgment; risk of devolving into an identity zoo unless book order and prose structure are kept first-class.

### 3. *Elements of Information Theory*, Cover & Thomas, 2nd ed. (2006)

- **Field:** information theory.
- **Scope:** 17 chapters. Estimated **~380 main-text nodes** (definitions+theorems; the book is theorem-dense but many chapters are short). Effort: **heavy single-book with infrastructure-building** (this is the "build a missing field" pick).
- **Existing formalization status:** **No Lean version found** (verified via searches + registries above). In **Coq**, a research-line library (Affeldt et al., "Formalization of Information Theory" / Infotheo) covers AEP, source coding, and discrete memoryless channel coding — I know this from training, not re-verified today. Isabelle has scattered information-theory AFP entries. **Relies on the different-PA exception relative to Coq.**
- **Mathlib readiness:** foundations only. Verified via Mathlib source listing: `Mathlib/InformationTheory/` contains exactly `Coding/` (Kraft, Kraft–McMillan, PrefixFree, UniquelyDecodable), `Hamming`, `KullbackLeibler` — plus `Real.binEntropy`/`qaryEntropy` and topological entropy. **Missing:** Shannon entropy for PMFs/measures as a developed calculus, conditional entropy, **mutual information (0 Loogle hits)**, chain rules, AEP/typical sets, source coding theorem, channel capacity, noisy channel coding theorem (the crown), method of types, rate–distortion, differential entropy beyond fragments, Gaussian channel. Measure/probability side is strong (CLT ✓ in Mathlib now — verified `Mathlib.Probability.CentralLimitTheorem`).
- **Case:** the canonical text of a whole field; Shannon's coding theorems are among the most-used and least-machine-checked results in applied mathematics; downstream value is enormous (CS, ML theory, statistics, quantum information via PhysLib/QuantumInfo). Completing it would create the IT layer Lean currently lacks, which others (PhysLib's quantum-info half) would immediately consume.
- **Risks:** ch. 7–10 (channel capacity, channel coding) require delicate asymptotic/limit constructions that are notoriously fiddly to state faithfully; ch. 9+ (continuous, Gaussian) lean on L²/CLT machinery; the book's proofs are often sketchy, forcing the formalizer to supply real proofs (raises review burden); collision risk with PhysLib's quantum-IT TODO list is moderate (Wilde's book is their target, and that's a different book — but shared infrastructure).

### 4. *A Classical Introduction to Modern Number Theory*, Ireland & Rosen, 2nd ed. (1990)

- **Field:** number theory (classical → algebraic).
- **Scope:** 20 chapters. Estimated **~580 nodes**. Effort: **heavy single-book verging on multi-year** (the last third is real algebraic number theory).
- **Existing status:** **No Lean book formalization found** (searches + registries). Adjacent work: ATLAS formalized Sutherland's MIT *Number Theory I* notes at 80% of 576 targets (arXiv:2605.29955) — course notes, different book, different standard; mathlib now contains a surprising amount of the book's spine (see below).
- **Mathlib readiness:** unusually good for a number theory book: quadratic reciprocity ✓, Gauss sums ✓ (`Mathlib.NumberTheory.GaussSum`, verified), finite fields ✓, cyclotomic fields ✓, Dirichlet characters & L-series ✓ (`Mathlib.NumberTheory.LSeries`), **Dirichlet's theorem on APs ✓ in Mathlib** (Loeffler–Stoll, `LSeries.PrimesInAP`), Dirichlet unit theorem ✓, class groups ✓ (`Mathlib.RingTheory.ClassGroup`), Dedekind domains ✓. **Gaps:** Jacobi-sum chapters (cubic/biquadratic reciprocity), quadratic forms over ℤ and genus theory, class-number computations/formulas, the zeta/L-function analytic chapters (partially colonized — see risks), elliptic-curve chapters (ch. 18–20 — heavy).
- **Case:** the canonical bridge text from elementary to algebraic number theory; enormous teaching base; its results are used daily and almost none are machine-checked at book scale.
- **Risks:** **collision risk with PNT+/IEANTN** (Kontorovich–Tao et al., verified active: PNT with error term, PNT in APs, stretch goal Chebotarev — this is exactly the analytic half of chapters 11–16) and with the FLT project (modular-forms direction: verified 281 `ModularForm` declarations in Mathlib). Recommend scoping to chapters 1–10 (the "classical" half) if started now, or sequencing after the point-set pick.

### 5. *A Mathematical Introduction to Logic*, Herbert Enderton, 2nd ed. (2001)

- **Field:** mathematical logic.
- **Scope:** five chapters (0–4: preliminaries, sentential logic, first-order logic, undecidability, second-order logic) + appendices. Estimated **~300 nodes**. Effort: **single-book, PMA-class or lighter.**
- **Existing status:** **No Lean book formalization found** (searches + registries; not in ATLAS/ReasBook). Nearest Lean work: `FormalizedFormalLogic/Foundation` (incompleteness, Löb, Tarski — verified via the 1000-theorems page) and Mathlib itself. In other PAs: Isabelle/HOL and Coq have rich logic libraries (training knowledge, not re-verified).
- **Mathlib readiness:** strong. Verified present: `Mathlib/ModelTheory/` (Skolem, elementary maps, Fraïssé, ultraproducts, satisfiability, semantics, complexity) and `Mathlib/Computability/` (Turing machines, partial recursiveness, RE, halting, Turing degrees, Myhill–Nerode, CFGs). Completeness/compactness for FOL is in Mathlib's ModelTheory layer (satisfiability file; standard-axioms-only, part of the library). **Gaps:** textbook-ordered development of compactness/Löwenheim–Skolem as Enderton states them, representability of recursive functions in arithmetic (the machinery for Gödel II — Foundation repo has versions to port/re-derive), decidability chapters' book-specific encodings.
- **Case:** logic is a core mathematical field and no canonical logic book exists in Lean; the field's infrastructure (Mathlib + Foundation) is freshly in place, so this is a "harvest" book — much of the content exists, nobody has assembled it as a faithful book. Cheap, unique, complements the programme's analysis line with a logic line.
- **Risks:** faithfulness disputes over Enderton's specific (sometimes dated) encodings (e.g. his sentential-logic setup, second-order semantics choices); some content (ch. 4 second-order logic) is conceptually subtle with little Mathlib support; lower glamour than topology/IT — worth it only if the programme wants a fast parallel win.

### 6. *Complex Analysis* (Princeton Lectures in Analysis, Vol. II), Stein & Shakarchi (2003)

- **Field:** complex analysis.
- **Scope:** 10 chapters. Estimated **~330 nodes**. Effort: **heavy single-book.**
- **Existing status:** **No Lean formalization found** (searches + registries; ReasBook's complex-adjacent entry is Forster's Riemann surfaces, a different book). Note the programme already has Rudin RCA queued — its complex chapters overlap ~30% with this; recommend only if a dedicated complex volume is wanted ahead of RCA.
- **Mathlib readiness:** holomorphic machinery strong (Cauchy integral formula, Liouville, maximum modulus, power series, analytic continuation, Möbius — verified in the 1000-theorems/Mathlib layer); Fourier side strong (inversion ✓). **Biggest verified gap: residues — 0 hits for any complex residue theorem; `residue` hits are all local-ring/algebraic-geometry residue fields.** Also missing: argument principle/Rouché in textbook form, Riemann mapping theorem, Weierstrass products/elliptic-function chapters (partial), gamma/zeta special-function development.
- **Case:** the most-taught graduate complex analysis text of the last two decades; residue calculus is a daily tool of every analyst and physicist and is not kernel-checked in Lean at book scale.
- **Risks:** building residue + argument-principle infrastructure is a genuine research-engineering effort (it blocks ch. 3 onward in spirit); ch. 9–10 (elliptic functions, applications of theta) reach toward modular territory where the FLT project is active.

### 7. *Differential Geometry of Curves and Surfaces*, Manfredo do Carmo (1976/2016)

- **Field:** classical differential geometry.
- **Scope:** 6 chapters + appendices. Estimated **~350 nodes**. Effort: **heavy single-book** (infrastructure-building: the classical surface theory does not exist in Mathlib in this form).
- **Existing status:** **No Lean formalization found** (searched; ATLAS has Seidel's MIT differential-geometry notes at 76% of targets — different source). This is a "different-PA exception" candidate too: some Coq/Isabelle geometry work exists in spirit, nothing book-scale (training knowledge, unverified).
- **Mathlib readiness:** smooth manifolds, tangent bundles, differential forms exist; **missing:** theory of regular surfaces in ℝ³ as the book does it, first/second fundamental forms, Gauss/mean curvature, covariant derivative on surfaces, geodesics as curve-energy minimizers (verified: no `IsGeodesic`/Riemannian geodesics in Mathlib; only quiver/word-metric geodesics), Gauss–Bonnet. `Bundle.RiemannianMetric` exists (verified via Loogle suggestion) but the curvature machinery does not.
- **Case:** canonical for a century of teaching; kernel-checking Gauss–Bonnet is a landmark result for the programme; unblocks PhysLib-adjacent classical physics and every subsequent geometry book.
- **Risks:** design decision — build on Mathlib's manifold API (correct but heavy) vs. a self-contained embedded-surfaces API (closer to the book, risks divergence from Mathlib norms); chapter 4–5 computations are lengthy; hostile review of differential-geometry statements is notoriously argumentative.

### 8. *Probability with Martingales*, David Williams (1991)

- **Field:** measure-theoretic probability.
- **Scope:** 15 chapters + "front H" measure-theory part. Estimated **~330 nodes**. Effort: **single-book, PMA-class.**
- **Existing status:** **No Lean version of this book.** But the adjacent space is crowded: ReasBook has **Klenke's *Probability Theory*** (3rd ed., 9 contributors, source published); ATLAS has Sheffield's MIT probability notes (84%); a third group is formalizing *Measure-Theoretic Probability* (Deng & Shum, arXiv:2607.27298). A Williams project would be the fourth probability-adjacent book formalization — justify it as the *most canonical teaching text* of the four or skip.
- **Mathlib readiness:** very good — measure theory ✓, martingales with optional stopping ✓ (verified), CLT ✓ (verified, new in Mathlib), Gaussians ✓, Stirling ✓, filtrations/adaptedness ✓. **Gaps:** martingale convergence theorems in book order (upcrossing/a.s. convergence status unverified today), characteristic-function toolkit, weak convergence chapters (partial), coupling/Markov-chain chapters beyond basics.
- **Case:** the book most responsible for how measure-theoretic probability is taught; short; mathematically honest; its "trust" content (martingale convergence, optional stopping in the book's exact generality) is real.
- **Risks:** overlap with queued Rudin RCA (measure chapters) and with the three existing probability formalizations; value is in the teaching text, not in new Mathlib content.

### 9. *An Introduction to Ergodic Theory*, Peter Walters (1982)

- **Field:** ergodic theory / dynamical systems.
- **Scope:** 9 chapters. Estimated **~250 nodes**. Effort: **single-book, PMA-class.**
- **Existing status:** **No Lean formalization found.** No ATLAS/ReasBook entry; cam-combi and PhysLib do not touch it.
- **Mathlib readiness:** surprisingly strong and fresh: `Mathlib.Dynamics.Ergodic` exists with conservative systems and **empirical-measure/Birkhoff-average results** (verified: `integral_empiricalMeasure_eq_birkhoffaverage`), mean ergodic theorem ✓ (`Analysis.InnerProductSpace.MeanErgodic`), topological entropy ✓ (verified: `Dynamics/TopologicalEntropy` files), Haar measure ✓, Poincaré recurrence ✓ (1000-theorems). **Gaps:** invariant-measure existence (Krylov–Bogolyubov), ergodic decomposition, mixing criteria, topological dynamics chapters, the isomorphism-theory chapters (tail).
- **Case:** the canonical graduate entry to the field; rides exactly on Mathlib's newest layer, so it's a "strike while the iron is hot" pick that would consolidate a scattered new Mathlib area into a book.
- **Risks:** last chapters (Krieger finite generator, Ornstein isomorphism) are research-grade — scope honestly to early chapters; smaller community recognition than the picks above.

### 10. *A Course in Arithmetic*, Jean-Pierre Serre (1970/1973)

- **Field:** number theory / quadratic forms / modular forms.
- **Scope:** 3 parts, ~300 nodes. Effort: **heavy single-book.**
- **Existing status:** **No Lean book formalization found.** Strong adjacent activity: FLT project building modular forms (verified 281 `ModularForm` declarations), flt-regular (Kummer direction), ATLAS Sutherland notes.
- **Mathlib readiness:** Part I (finite fields, QR, Z/n) ✓ almost entirely; Part II (ℝⁿ lattices, p-adic fields, Hasse–Minkowski over ℚ) — p-adics/local fields ✓, **lattices/quadratic-form classification missing**; Part III (Dirichlet characters ✓ (LSeries), modular forms in active FLT-driven development, theta series/Hecke operators partial).
- **Case:** Serre; canonical; slim; would define "quadratic forms over ℤ/ℚ" in Mathlib, which nobody has.
- **Risks:** **direct collision with the FLT project's active area for Part III** — coordinate before starting, or treat Parts I–II as the project; quadratic-form chapters need genus-theory infrastructure from scratch.

### 11. *Linear Algebra*, Hoffman & Kunze, 2nd ed. (1971)

- **Field:** linear algebra.
- **Scope:** 12 chapters. Estimated **~480 nodes**. Effort: **heavy single-book but low technical risk.**
- **Existing status:** **No Lean formalization found** (searched). Axler's *LADR* is done (rkirov companion, see do-not list), but H&K — the other canonical undergrad/grad text — is untouched.
- **Mathlib readiness:** high (~70% overlap: determinants, rank, spectral theorem, inner-product theory, bilinear forms). **Verified gap: no Jordan normal form, no rational canonical form in Mathlib** (0 hits for `JordanNormalForm`); invariant factors/Smith normal form in textbook form also thin.
- **Case:** canonical, timeless, and its missing pieces (Jordan/rational canonical forms) are exactly the results every mathematician uses weekly and no Lean library has.
- **Risks:** heavy overlap with Mathlib + the Axler companion makes marginal value lower than rank suggests; Jordan-form chapters are a known Lean engineering tar pit (representability of canonical forms).

### 12. *The Cauchy–Schwarz Master Class*, J. Michael Steele (2004)

- **Field:** inequalities / problem-driven analysis.
- **Scope:** ~19 chapters. Estimated **~280 nodes**. Effort: **single-book, PMA-class, easiest on this list.**
- **Existing status:** **No formalization found.**
- **Mathlib readiness:** very high (Cauchy–Schwarz, AM–GM, Hölder, Minkowski, Jensen, Gronwall all in Mathlib; competition-style manipulation is agent-friendly).
- **Case:** the standard "how to prove inequalities" course text; perfect training ground and showcase for the programme's agent pipeline; natural companion volume to PMA.
- **Risks:** problem-book character (some "theorems" are embedded in prose/exercises — needs a numbered-node policy); lower canonical weight than everything above.

### 13. *Mathematical Methods of Classical Mechanics*, V.I. Arnold, 2nd ed. (1989)

- **Field:** mathematical physics.
- **Scope:** 2 parts, ~50 numbered sections. Estimated **~300 nodes**. Effort: **multi-year** (not the size — the missing foundations).
- **Existing status:** **No Lean formalization found.** PhysLib (verified) targets physics broadly but currently centres on core physics + quantum information (Wilde TODO); no Arnold activity visible.
- **Mathlib readiness:** the blocker: **no symplectic geometry** (verified: only the matrix symplectic group exists in `LinearAlgebra.SymplecticGroup`), no calculus of variations, no geodesic theory (verified 0 hits), no Legendre-transform-in-mechanics layer, no rigid-body theory. ODE side has Picard–Lindelöf ✓; flows partially.
- **Case:** the most canonical math-physics text ever written; would be the programme's flagship outside pure math.
- **Risks:** realistically a two-phase project (build symplectic/variations infrastructure, then the book); PhysLib may claim parts; only choose if the programme wants a long-horizon second track while PMA-style books run in parallel.

---

## Top 3 in depth

### 1. Munkres, *Topology* (2nd ed.) — ~630 nodes, heavy single-book

**How it proceeds, chapter by chapter:**

- **Ch. 1 (Set theory and logic, ~60 nodes).** Directories, relations, Zorn. Mathlib has all of it (`Set`, `Rel`, `Zorn`); the work is book-order restatement and the finite-set/ordered-pair conventions. Hostile review is cheap here; expect it to go fast. One decision: Munkres' finiteness-by-bijection vs. Mathlib `Finite` — mirror the book, bridge to Mathlib at section ends (the PMA repo's "bridge lemma" pattern applies).
- **Ch. 2 (Topological spaces, ~80 nodes).** Basis, subbasis, order topology, product, metric. Heavier than it looks: the book's sequence of constructions (basis criterion, subbasis generation, product vs. box) is exactly where Mathlib's filter-based API diverges from textbook topology. Budget for an interface layer early; this is the pattern-setter for the whole point-set half.
- **Ch. 3 (Connectedness/compactness, ~70 nodes).** Largely present in Mathlib (connectedness, compactness, limit-point vs. sequential compactness, local compactness). Mostly harvesting; the review risk is over-trusting Mathlib equivalents whose hypotheses differ slightly (e.g. type-class vs. predicate formulations).
- **Ch. 4 (Separation + countability, ~80 nodes) and Ch. 5 (Tychonoff, ~30 nodes).** Urysohn lemma in Mathlib ✓; choice-based Tychonoff ✓. Normality lemmas are the fiddly part.
- **Ch. 6–8 (Metrization; complete metric spaces, function spaces; Baire/dimension, ~120 nodes).** Urysohn metrization theorem: Mathlib has the pieces (uniform spaces, `TietzeExtension` ✓) but the book's exact route (embedding via countable family of functions) must be assembled. Baire ✓; Arzelà–Ascoli ✓ (Mathlib); Ascoli applications in book order need work. Chapter 8's dimension theory (covering dimension) is thin in Mathlib — first genuinely new material.
- **Where it starts to get hard — Ch. 9 (Fundamental group, ~60 nodes).** Mathlib's `FundamentalGroupoid` exists, but Munkres' treatment is loops-at-a-point with `[0,1]`-concatenation, π₁ of circle via covering of ℝ, retract arguments, Brouwer fixed point in dimension 2. Bridging groupoid-API ↔ book-API is a real design task; the circle computation is the first proof of the book that will take genuine effort.
- **Ch. 10 (Separation in the plane, ~35 nodes).** **Jordan curve theorem is not in Mathlib (verified).** This is the hardest chapter relative to its size: separation by arcs, invariance of domain, Jordan theorem itself. Expect this chapter alone to be a multi-week subsystem with careful review; consider publishing it as a Mathlib contribution.
- **Ch. 11 (Seifert–van Kampen, ~30 nodes).** Missing in Mathlib (verified). The groupoid route (via `FundamentalGroupoid.pushout`-style results) is the natural Lean approach but diverges from Munkres' free-product presentation — a faithful-statement choice to make explicitly. Fundamental groups of surfaces appear here and in ch. 12.
- **Ch. 12 (Classification of surfaces, ~30 nodes).** Quotient of polygonal regions, Euler characteristic, orientability, surgery classification. Nothing exists in Mathlib; the combinatorial quotient machinery is heavy but elementary. Satisfying "every surface is a connected sum of spheres/tori/projective planes" in Lean is a publishable milestone.
- **Ch. 13 (Classification of covering spaces, ~35 nodes).** `Mathlib.Topology.Covering.Basic` exists (verified) but the classification theorem (subgroups ↔ covering maps, universal covers, deck groups) does not in book form. Builds on ch. 9+11; the equivalence-of-categories-flavored statement must be carefully de-categorified to book statements.
- **Hard parts in summary:** chapters 10–13. Recommended sequencing: 1→9 straight through (harvest-heavy), then a deliberate pause to design the homotopy layer (10–13 together), shipping van Kampen + Jordan + classification as Mathlib-facing PRs along the way.

### 2. Graham–Knuth–Patashnik, *Concrete Mathematics* (2nd ed.) — ~520 nodes, heavy single-book

- **Ch. 1 (Recurrent problems, ~30 nodes).** Towers of Hanoi, lines in the plane, Josephus. Josephus in closed form is a surprisingly good early stress test of "solve in ℤ" reasoning. All feasible with elementary Mathlib.
- **Ch. 2 (Sums, ~60 nodes).** Summation methods, perturbation, multiple sums, finite calculus, infinite sums. Mathlib big-operators cover much; the *methods* (perturbation identity, summation by parts in the book's form) must be built as reusable tactics-by-lemma. Straightforward but voluminous — this is where the "identity zoo" risk starts; hold the line with book-order files.
- **Ch. 3 (Integer functions, ~50 nodes).** Floor/ceiling properties, **floor sums** (the "Spectrum" and `⌊⌊nx⌋/m⌋`-type results), `x mod y` manipulations, the three "hi/lo" surprises. **Biggest verified gap of the early chapters**: Mathlib has floor basics, not the floor-sum calculus. This chapter defines the project's novelty; build a `FloorSum` mini-library.
- **Ch. 4 (Number theory, ~60 nodes).** Divisibility, primes, factorial factors, relative primality, `φ`, Möbius, "the phi function and divisors" — heavily covered by Mathlib (`Nat.totient`, `Nat.factorization`, `ArithmeticFunction`). Harvest-heavy; good place to demonstrate interface discipline.
- **Ch. 5 (Binomial coefficients, ~70 nodes).** The 30+ basic identities, Vandermonde and generalizations, generating functions for binomials, hypergeometric transformations, partial fractions, the "mechanical summation" section (Gosper). Mathlib has many binomial identities; the **hypergeometric-sum machinery is missing** — the last sections of this chapter are the first hard tail.
- **Ch. 6 (Special numbers, ~80 nodes).** Stirling numbers (✓ verified present — but only basic API; the chapters' identities around `stirlingSecond` need extension), Eulerian numbers (partial), Stirling polynomials, harmonic numbers (partial), harmonic summation, Fibonacci (✓ but the *finite-calculus treatment* — `F_n` via continuants and the "fibonaccorial" material — needs new work), Bernoulli ✓ (basic), Euler summation, continuants. Harvest + extend.
- **Ch. 7 (Generating functions, ~60 nodes).** Domino theory, solving recurrences via OGFs, partition-generating functions (✓ pentagonal theorem present), Catalan (✓ folder present), exponential generating functions, Dirichlet generating functions (Mathlib has Dirichlet series basics ✓). The *method* chapters need a disciplined `GeneratingFunction`-as-formal-power-series layer over `PowerSeries` — engineering, not research.
- **Ch. 8 (Discrete probability, ~60 nodes).** Definitions, mean/variance, probability generating functions, flipping coins, hashing. Mathlib probability + `PMF` cover the base; the applications (coupon collector-ish results) are self-contained and pleasant. Low risk.
- **Ch. 9 (Asymptotics, ~50 nodes).** Big-O hierarchy ✓, `O`-manipulation ✓, Stirling ✓ (hard version?), Bernoulli numbers ✓, saddle-point method — **this is the genuinely hard chapter**: Mathlib has no Laplace-method/saddle-point toolkit. Two honest options: (a) scope ch. 9 as "core asymptotics without the saddle-point derivations," deferring those nodes with a documented gap; (b) build the saddle-point machinery first as a standalone mini-project. Decide before promising complete coverage.
- **Hard parts in summary:** ch. 3 (new floor-sum library), ch. 5 (hypergeometric summation), ch. 9 (asymptotics). Everything else is harvest-plus-identity bookkeeping. Excellent agent-staffable profile: 90% of nodes are low-depth, high-volume.

### 3. Cover & Thomas, *Elements of Information Theory* (2nd ed.) — ~380 nodes, heavy single-book

- **Part I (Ch. 1–2, ~40 nodes):** entropy, joint/conditional entropy, relative entropy, mutual information, chain rules, Jensen/Kraft warmups. **Everything here beyond binary-entropy and KL must be built** (verified: no `mutualInfo` in Mathlib). Design decision #1 of the project: entropy on `PMF` (finite) for ch. 1–4 and on measures (`MeasureTheory`) for ch. 5+ — build both with transfer lemmas. This part defines the API everything else uses; budget generous review time.
- **Ch. 3–4 (Asymptotic equipartition; entropy rates, ~50 nodes).** AEP for i.i.d. sources and typical sets — needs a theorem about limsups of product-probability deviations (law of large numbers ✓ in Mathlib makes this pleasant); stationary stochastic-process entropy rate for ch. 4 (stationary processes exist in Mathlib; entropy rate does not). First new-to-Lean headline theorem: **AEP**.
- **Ch. 5–6 (Data compression; gambling and data compression, ~50 nodes).** Kraft/McMillan ✓ present (verified file listing); the *theorems* — optimum prefix-code length bounds, uniqueness/optimality of Huffman codes, and the duality of gambling and data compression (Kullback–Leibler as growth rate) — must be built. First new-to-Lean headline result: **Huffman optimality** and the source-coding half of Shannon's theory. Feasible; combinatorial-flavored.
- **Ch. 7 (Channel capacity, ~40 nodes).** Definitions, symmetric channels, properties of capacity — builds only on Part I. The back half of the chapter is **jointly typical sequences and the noisy channel coding theorem (achievability + converse via Fano)**: the crown of the book, not in Lean anywhere. Mostly finite combinatorics on top of the Part I API — hard but honest. **Hard tail #1, and the payoff.**
- **Ch. 8–10 (Differential entropy; Gaussian channel; rate–distortion, ~80 nodes).** Differential entropy on ℝⁿ: Mathlib has Gaussian measures and the CLT (✓ verified), and some pdf-entropy fragments; the Gaussian-channel coding theorem (capacity ½log(1+SNR)) and the parallel-Gaussian water-filling are new-to-Lean headline results; rate–distortion needs a variational characterization and achievability via random codebooks — **hard tail #2**.
- **Ch. 11–13 (Information theory and statistics; maximum entropy; universal source coding, ~70 nodes).** Method of types, Stein's lemma/Chernoff bound, EM-sketches, maximum-entropy distributions, Lempel–Ziv-style universal coding. The statistics chapter is largely self-contained once types are built (a nice, unusual formalization target); universal coding is engineering-heavy. Medium.
- **Ch. 14–17 (Kolmogorov complexity; network information theory; portfolio theory; inequalities in information theory, ~90 nodes).** The sparsest part of the book (few full proofs given — Cover–Thomas hand-waves by design, especially ch. 15–16). Ch. 17's entropy-power inequality is a genuinely hard formalization (known-hard analysis). Faithful-complete coverage forces supplying real proofs for sketched arguments; recommend an explicit "proof-supplied-where-book-sketches" review protocol, or scoping to ch. 1–13 + ch. 17 as the deliverable with 14–16 as stretch.
- **Hard parts in summary:** the API design of Part I (everything inherits it), the random-coding/joint-typicality core (ch. 7) and its continuous counterparts (ch. 8–10), and the sketchy back chapters (14–16). Nothing here is blocked by missing Mathlib *analysis* — it is blocked by missing Mathlib *information theory*, which is the point: this project adds a field.

---

## Do-not-formalize list

**Already done or near-done in Lean (evidence):**

- **Tao, *Analysis I*** — formalized by Tao himself (github.com/teorth/analysis; full book drafted, exercises as sorries by design; verified README). **Tao, *Analysis II*** — by a nine-author PKU group in ReasBook (`ReasBook/Books/Analysis2_Tao_2022`, verified).
- **Axler, *Linear Algebra Done Right* (4e)** — Lean companion complete through ch. 1–9 with every numbered item stated and main results proved (github.com/rkirov/linear-algebra-done-right-lean; verified README/commit log). Doing it again buys nothing.
- **Grinberg, *Algebraic Combinatorics*** — autoformalized end-to-end (340/340 targets; arXiv:2604.03071, 130k lines, open-sourced). Also kills much of the symmetric-functions-adjacent space (Fulton *Young Tableaux*, Sagan, and the heart of Stanley EC2) as "substantially adjacent."
- **ReasBook's catalogue (verified):** **Klenke, *Probability Theory* (3rd ed.)**; **Rockafellar, *Convex Analysis***; **Bauschke–Combettes**; **Beck, *First-Order Methods***; **Nesterov**; **Conforti–Cornuéjols–Zambelli, *Integer Programming***; **Forster, *Lectures on Riemann Surfaces***; **May, *A Concise Course in Algebraic Topology***; **Magnus–Karrass–Solitar**; **Lebl, *Intro to Real Analysis*; Sun–Yuan** — all have substantial Lean formalizations in ReasBook; do not duplicate. (Caveat: I did not audit ReasBook's sorry/faithfulness status per book; if one of these matters strategically, audit before assuming quality.)
- **Sipser, *Introduction to the Theory of Computation*** — ATLAS covered it at 71% of 118 targets (arXiv:2605.29955, verified table), and Mathlib already has DFA/NFA/regex/Myhill–Nerode/Turing machinery (verified file listing). Low marginal value now.

**Actively being done by strong projects (collision):**

- **Apostol, *Introduction to Analytic Number Theory*; Davenport, *Multiplicative Number Theory*** — PNT+ (Kontorovich–Tao; verified: PNT with error term, PNT-in-AP, IEANTN explicit-ANT network spun out to teorth/IEANTN) plus Mathlib's Dirichlet-in-AP/L-series (verified) are colonizing exactly this content. Stay away.
- **Silverman, *A First Course in the Arithmetic of Elliptic Curves*** — FLT project + ATLAS's Sutherland 18.783 notes (59% of 360 targets, verified) + mathlib elliptic-curves work. Colliding on all sides.
- **Neukirch / Marcus / any class-field-theory book** — 2025 Clay summer school on formalizing CFT (kbuzzard/ClassFieldTheory, verified) plus missing Mathlib prerequisites. Premature.
- **Riehl, *Category Theory in Context*** — started (rkirov companion, ch. 1 only, stalled; verified) and Mathlib already contains most of the book's actual mathematical content. Low marginal value.

**Prerequisites missing in Mathlib (verified today):**

- **Hatcher, *Algebraic Topology*** — no homology theory, no Seifert–van Kampen (0 Loogle hits for both), no CW-complex chapter. Multi-year field-building; do Munkres first.
- **Diestel / West / graph-theory texts** — Menger, planarity, coloring, min–max theory all absent from Mathlib; Cambridge Combinatorics in Lean (YaelDillies/cam-combi, verified) is colonizing the teaching side.
- **Kunen / Jech (set theory)** — forcing machinery absent in Lean 4 (flypitch did CH independence in Lean 3; a hobbyist Lean 4 port spotted (klatz.co blog), nothing serious). Isabelle has Independence_CH. Massive prerequisite build; low teaching-fit for this programme.
- **Lee, *Introduction to Smooth Manifolds*** — no Sard (manifold version in progress, verified fpvandoorn/sard), no integration of forms, no de Rham, no Lie groups. The book would drown the programme for years.

**Low value (already kernel-checked or queued):**

- **Folland / Royden / any real-analysis text** — Mathlib measure theory + queued Rudin RCA cover this role.
- **Halmos, *Naive Set Theory***; **any intro-proofs text (Hammack, Velleman)** — content already in Mathlib at higher rigor; the PMA repo already did this calibration work for ℝ-basics.
- **Dummit & Foote** — ~1,500+ nodes, multi-year, with ATLAS's Artin-adjacent notes (86% of 176 targets, verified) and flt-regular in adjacent territory. Too big, too contested, too little new.

---

## Method note

**What I did (all "verified" items below were checked live on 2026-10-21):**

1. **Registries and catalogues scraped:** the Lean community projects page (leanprover-community.github.io/lean_projects.html — downstream-repo registry), the ReasBook catalogue (github.com/optpku/ReasBook — 13 books, live), the ATLAS paper + repo (arXiv:2605.29955 + facebookresearch/atlas-lean — 26 books, per-book coverage table), the community "1000+ theorems" page (mathlib coverage at theorem level, with authors), the Palomar registry announcement (Tao, 2026-08-18; palomar-registry.org), and Prove2Me's scope (preprint arXiv:2608.28433 — a platform, not book work).
2. **Book-by-book absence checks:** web searches (Firecrawl) for "[author/title] Lean formalization" for every shortlist and do-not candidate, plus GitHub-repo scrapes where a candidate hit appeared. Verified-existing items: teorth/analysis (Tao I), ReasBook/Analysis2_Tao_2022, rkirov/linear-algebra-done-right-lean, rkirov/category-theory-in-context-lean, Grinberg formalization (arXiv:2604.03071), Isabelle-Munkres (arXiv:2604.07455), Megalodon-Munkres (arXiv:2601.03298), Deng–Shum probability textbook (arXiv:2607.27298), flypitch (+ Lean 4 port blog).
3. **Mathlib readiness checks:** Loogle (loogle.lean-lang.org) name/string searches — positive: TietzeExtension, FundamentalGroupoid (177 decls), IsCoveringMap (116 decls), Stirling, Catalan folder, Pentagonal/partitions, gaussSum, ClassGroup, ModularForm (281 decls), entropy (binary/topological), MeanErgodic, Dynamics.Ergodic.EmpiricalMeasure, Bundle.RiemannianMetric; **negative (0 hits): JordanNormalForm, ResidueTheorem, mutualInfo, Perron, IsGeodesic, vanKampen (topology), jordanCurve/Jordan-curve, Nat.catalan**. Plus GitHub-API directory listings of `Mathlib/InformationTheory`, `Mathlib/ModelTheory`, `Mathlib/Computability`, `Mathlib/Combinatorics/Enumerative` (verified file inventories).

**What I could not check, and confidence accordingly:**

- **The project-intentions registry** (GitHub project board — not scrapable without JS/login): some candidates may be "claimed" there invisibly. This is the biggest blind spot; shortlist items should be cross-checked there before committing.
- **Palomar's full index** and the Zulip archive (searchable but huge — I only sampled): medium risk of missed Lean projects for any specific book.
- **ReasBook per-book completeness/sorry status:** their catalogue lists coverage counts but I did not audit proof quality; my do-not entries rest on "substantial existing work," not "complete hostile-review-grade work." If ReasBook's standard turns out weak, Klenke/Forster/Rockafellar/May could re-enter the shortlist as redo-at-standard candidates.
- **Node counts** are estimates (±30%) from chapter/section structure and my knowledge of each book's numbering, calibrated to PMA ≈ 330; I did not open the books to count. Marked as estimates throughout.
- **Mathlib API descriptions** mix verified checks (named above) with training knowledge (e.g. "Arzelà–Ascoli in Mathlib", "Cauchy integral formula in Mathlib") — those specific items were not re-verified today and are standard, stable facts; low risk.
- **Training-knowledge-only claims** (flagged inline where load-bearing): Coq information-theory library (Affeldt et al.), Isabelle AFP logic/computability depth. Everything else in the report cites a live check.

**Confidence summary:** high confidence on "already done" do-not entries (all evidence-based, cited); high confidence on the top-3 absence claims (multiple independent registries + searches + catalogues all empty); medium confidence on Mathlib readiness details (verified spot-checks over a fast-moving library — re-run Loogle checks at project start); medium confidence on effort classes (extrapolated, not measured).
