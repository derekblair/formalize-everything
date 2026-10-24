# Formalize-Everything: Three-Lane Synthesis

**Sources:** `REPORT-kimi.md` (Kimi), `REPORT-glm.md` (GLM), and `REPORT-argon.md` (Argon). Lane ranks below are the reports' own ranks. The reports did not use a common numerical score, and their node-count conventions differ, so node figures are planning ranges—not directly comparable measurements.

Rudin's *Principles of Mathematical Analysis* is treated as already covered by `rudin-lean`; the reports also treat Rudin's *Real and Complex Analysis* and *Functional Analysis* as already queued. None is ranked as a new candidate.

## 1. Consensus shortlist

“Consensus” means shortlisted by at least two lanes. The combined order weighs the number of supporting lanes, their ranks, boundedness of scope, readiness, and unresolved status conflicts.

| Combined | Candidate | Kimi | GLM | Argon | Synthesis |
|---:|---|---:|---:|---:|---|
| **1** | M. F. Atiyah & I. G. Macdonald, *Introduction to Commutative Algebra* | **1** | — | **1** | The strongest peak support: two independent first-place rankings. Kimi estimates 180–240 nodes and Argon about 230 in its table (about 265 in its blueprint). Both find no complete book formalization and strong Mathlib support, with dimension theory the main spike. One Mathlib-coverage contradiction must be checked before the Chapter 4 plan is trusted—see §6. |
| **2** | David Williams, *Probability with Martingales* | 7 | 8 | **2** | The only candidate shortlisted by all three lanes. All agree that no ordered complete Lean book was found and that Mathlib already contains much of the martingale, conditional-expectation, strong-law, and limit-theorem infrastructure. The reports disagree materially on the book's chapter/node scope, so a frozen table of contents and node ledger are prerequisites. |
| **3** | Herbert B. Enderton, *A Mathematical Introduction to Logic* | **3** | 5 | — | A coherent logic project with substantial Mathlib and Foundation infrastructure but no complete book-ordered Lean development found. Kimi estimates 230–330 nodes; GLM estimates about 300. Both identify statement/calculus fidelity—not the famous incompleteness endpoints alone—as the real work. |
| **4** | John W. Milnor, *Topology from the Differentiable Viewpoint* | 4 | — | 6 | Small node count—Kimi 80–130, Argon about 95—but not small effort. Both see useful manifold, Whitney-embedding, and partition-of-unity infrastructure; both also identify Sard/degree/Poincaré–Hopf/framed-cobordism material as substantial new work. |
| **5** | Peter Walters, *An Introduction to Ergodic Theory* | — | 9 | 10 | Both lanes regard Mathlib's recent ergodic layer as timely and find no Lean book formalization. GLM emphasizes Birkhoff/mean-ergodic and topological-entropy support; Argon emphasizes how much of the later entropy, topological-dynamics, pressure, and variational-principle material remains to be built. |
| **6** | Ronald L. Graham, Donald E. Knuth & Oren Patashnik, *Concrete Mathematics* | 14 | **2** | — | Very high ceiling but the largest consensus ranking split. GLM found no formalization in any assistant and estimates about 520 nodes; Kimi estimates 350–650, calls it multi-year, and would first build prerequisites through Wilf and *A=B*. The absence claim is strong in both reports; the disagreement is sequencing and true scope. |
| **7 — HOLD** | Jean-Pierre Serre, *A Course in Arithmetic* | 5 | 10 | Rejected as in flight | Do not start until the existing-project facts are resolved. Kimi reports only Chapter 1 in the blueprint project's formalization tree; GLM found no Lean book formalization; Argon says a named project has already formalized Chapter I and Chapter II §§1–3.1 with zero `sorry`s and has modular forms underway. See §6. |

### What the consensus says

- **Algebra and probability dominate the actionable consensus.** Atiyah–Macdonald and Williams are the clear first tier, for different reasons: Atiyah–Macdonald has two #1 votes; Williams has unanimous support.
- **Enderton is the cleanest third lane.** It is less glamorous than the topology candidates in the individual reports, but it has two top-five votes, convergent scope estimates, and no lane placing it on a do-not list.
- **Milnor is compact in inventory, not in difficulty.** Its rank should not be read as “quick win.”
- **Concrete Mathematics is not rejected; it is mis-sequenced in one lane's judgement.** GLM would start it now; Kimi would deliberately build toward it.

## 2. Single-lane picks worth noting

These were shortlisted by only one lane, but the reasoning is strong enough that they should not disappear from the decision set.

### Wilf, *generatingfunctionology* — Kimi #2

Kimi's highest-ranked non-consensus pick. It has five chapters, an estimated 110–220 nodes, strong `PowerSeries`/`MvPowerSeries` support, and reusable payoff across combinatorics, probability, and number theory. The warning is precise: exponential families/species, Lagrange inversion, WZ/cycle-index tools, and Hayman/singularity asymptotics are not routine gaps. Kimi recommends an early Chapter 5 spike before committing.

### Cover & Thomas, *Elements of Information Theory* — GLM #3

GLM's case is that this project would create a largely missing Lean field rather than merely assemble an existing one. It reports Kraft/Kraft–McMillan and fragments of entropy/KL already present, but no developed mutual-information calculus, AEP/typicality layer, source- and channel-coding theorems, or rate–distortion theory. That makes it higher-risk than the consensus picks, but also potentially higher-leverage for computer science, statistics, and quantum information.

### Serre, *Linear Representations of Finite Groups* — Argon #3

Not the same book as Serre's *A Course in Arithmetic*. Argon ranks it third because finite groups keep the work in finite-dimensional linear algebra, cyclotomic fields, and DVRs, avoiding analytic and topological bottlenecks. It reports Part I infrastructure in Mathlib but major missing results in Mackey theory, Artin/Brauer induction, rationality/Schur index, and the modular \(cde\) triangle.

### Garling, *A Course in Galois Theory* — Argon #4

Argon's lowest-risk algebra alternative: about 220 nodes, no book formalization found, and a Mathlib Galois-theory API said to cover most core theorems. Its distinctive work is concentrated in constructibility framing, explicit cubic/quartic Galois-group computations, Artin–Schreier extensions, and possible transcendence-degree material.

### Petkovšek, Wilf & Zeilberger, *A=B* — Kimi #11

Kimi singles this out for unusually direct alignment with verified computation: Gosper, Zeilberger, WZ certificates, creative telescoping, and algorithm termination/correctness. The same feature is the risk—a project that proves only identities would not faithfully cover the book. It is also a possible prerequisite lane for the mechanical-summation parts of *Concrete Mathematics*.

### Fulton, *Algebraic Curves* — Argon #15

Argon's strategic sleeper. Despite the low rank, its case is distinctive: Bézout, blow-ups/resolution of singularities, and Riemann–Roch for curves in about 226 pages, using commutative algebra rather than first building schemes and sheaf cohomology. The gaps—intersection multiplicity, projective curves, Noether's \(AF+BG\), blow-ups, adeles/differentials—are nevertheless central, not peripheral.

### Other single-lane candidates not elevated here

- **Kimi:** Norris, *Markov Chains* (#8); Bollobás, *Graph Theory* (#9); Winskel, *The Formal Semantics of Programming Languages* (#12); Stein & Shakarchi, *Real Analysis* (#13); Hall, *Quantum Theory for Mathematicians* (#15).
- **GLM:** Stein & Shakarchi, *Complex Analysis* (#6—a different book from Kimi's Stein & Shakarchi *Real Analysis*); do Carmo, *Differential Geometry of Curves and Surfaces* (#7); Hoffman & Kunze, *Linear Algebra* (#11); Steele, *The Cauchy–Schwarz Master Class* (#12).
- **Argon:** Humphreys, *Introduction to Lie Algebras and Representation Theory* (#5); Lieb & Loss, *Analysis* (#8); Cutland, *Computability* (#11); van Lint, *Introduction to Coding Theory* (#12); Marker, *Model Theory* (#13); Alon & Spencer, *The Probabilistic Method* (#14).

Munkres, Ireland & Rosen, Hatcher, Riehl, Arnold, Apostol, and Marcus are not treated as ordinary single-lane picks because another lane explicitly rejects or materially disputes them; they are covered in §3.

## 3. Where the lanes disagree

### Munkres, *Topology* — the sharpest ranking conflict

- **GLM ranks it #1:** no Lean version found; Mathlib covers much of Chapters 1–8; covering maps and the fundamental groupoid make the later frontier newly reachable. GLM accepts the Isabelle and Megalodon versions under a different-proof-assistant exception.
- **Kimi places it on the do-not list for low marginal value:** Isabelle/HOL is reported to cover all 39 sections of Chapters 2–8 with zero `sorry` (albeit with statement defects found on review), while Chapters 9–14 overlap the harder Hatcher programme.
- **Argon also rejects it (#19):** Megalodon has autoformalized Part I, Mathlib already contains most Part I material natively, and May's *A Concise Course in Algebraic Topology* in ReasBook supersedes the algebraic-topology side for Argon's purposes. Argon prefers Milnor.

This is a values disagreement about what counts as valuable Lean novelty, not just a factual dispute.

### Serre, *A Course in Arithmetic* — shortlist versus already in flight

Kimi (#5) and GLM (#10) treat it as an opening with partial adjacent work. Argon removes it entirely as already in flight. Because Argon's reported progress is much more extensive than Kimi's, this is first a factual verification problem (§6), then a coordination problem. No lane should start a competing project before the repositories are inspected at commit level.

### Ireland & Rosen, *A Classical Introduction to Modern Number Theory* — formalizable versus contract-incompatible

- **GLM ranks it #4,** while warning about its size and collisions with PNT+/IEANTN and modular-forms work.
- **Kimi rejects it under the strict complete-book contract** because Chapter 20 is described as a proofless research survey: stopping after Chapter 19 could be useful, but would not be the whole second edition under Kimi's coverage rules.

The conflict is about the programme's completeness contract, not primarily about Mathlib readiness.

### Hatcher, *Algebraic Topology* — high-payoff investment versus premature field-building

- **Kimi ranks it #10:** large to multi-year, but the highest-payoff reusable topology investment, with CW complexes, covering maps, fundamental groupoids, and some singular-homology infrastructure already available.
- **GLM puts it on the do-not list:** Seifert–van Kampen, homology, and the CW-complex chapter are described as missing prerequisites; GLM recommends Munkres first.

Their descriptions of current Mathlib readiness conflict directly; see §6.

### Riehl, *Category Theory in Context* — source-specific value versus duplication

- **Kimi ranks it #6:** existing Lean work is partial, and Chapters 5–6 plus the epilogue and source-specific examples would have broad downstream reuse.
- **GLM rejects it as low marginal value:** a companion has started, and Mathlib already contains most of the book's mathematical content.

Both agree that Leinster's *Basic Category Theory* is already done; they disagree on whether Riehl's additional scope justifies another category-theory book.

### Arnold, *Mathematical Methods of Classical Mechanics* — flagship versus multi-programme trap

- **GLM includes it at #13,** explicitly as a multi-year flagship requiring symplectic geometry, variations, and geodesic infrastructure first.
- **Kimi rejects it for the next slot** because the 16 appendices expand the obligation into KAM, contact/singularity theory, KdV, fluids, and forms, with many proofs delegated to cited literature.

The lanes largely agree on the scale; they disagree on whether that scale is a reason to choose it as a long-horizon track or exclude it.

### Apostol, *Introduction to Analytic Number Theory* — Lean opening versus collision risk

- **Argon ranks it #7:** no Lean book found, strong Mathlib support for arithmetic functions, Dirichlet characters, Gauss sums, L-series, and Euler products, with Isabelle AFP work disclosed.
- **GLM puts Apostol on the do-not list** because PNT+ and the IEANTN network, together with Mathlib's analytic-number-theory work, are colonizing the same mathematical territory.

This is a tolerance-for-adjacent-work disagreement: neither lane claims that the other has found a complete Lean Apostol.

### Marcus, *Number Fields* — book-specific readiness versus category-level caution

- **Argon ranks it #9,** reporting Chapters 1–5 as very highly supported by Mathlib's number-field, Dedekind-domain, class-number, unit, discriminant, and ramification APIs.
- **GLM groups “Neukirch / Marcus / any class-field-theory book” as premature,** citing the 2025 Clay class-field-theory formalization effort and missing prerequisites.

GLM's objection is category-level; Argon's is book-specific. A Marcus decision needs a chapter-level prerequisite audit rather than reliance on either generalisation.

### Concrete Mathematics — start now versus build prerequisites first

GLM ranks it #2 and stresses low per-node difficulty outside the hard tails. Kimi ranks it #14, estimates a wider and potentially larger scope, and explicitly sequences Wilf and *A=B* first. This is mainly a sequencing/scope dispute, not a disagreement that the book is absent or valuable.

## 4. Merged do-not-formalize list

“Do not formalize” here means **do not start a new clean-room project now under the strict complete-book, zero-`sorry`, standard-axioms, statement-fidelity standard**. It does not rule out auditing, completing, or collaborating with an existing project. Items marked † are contested by another lane's shortlist and are cross-referenced in §3.

### Already complete, main-text complete, or too substantially covered to duplicate

- **Axler, *Linear Algebra Done Right*** — GLM and Argon report a Lean companion covering the main text through Chapters 1–9; restarting buys little.
- **Grinberg, *An Introduction to Algebraic Combinatorics*** — all lanes treat the 340-target project as disqualifying for a duplicate. Its status under the programme's stricter exercise/axiom standard is disputed; see §6.
- **Spivak, *Calculus*** — Kimi and Argon report a complete Lean project. Kimi explicitly notes that independent build and hostile statement review were not performed, so “complete” is a project claim until audited.
- **Leinster, *Basic Category Theory*** — Kimi and Argon report all six chapters and the appendix complete with zero `sorry`; use as infrastructure and as an overlap warning for Riehl.
- **Tao, *Analysis I* and *Analysis II*** — all three lanes report substantial or complete companions; Analysis I intentionally leaves exercises as `sorry` by design, so neither should be described as strict-complete without qualification.
- **Beck, *First-Order Methods in Optimization*** — Kimi and Argon report ReasBook main Chapters 1–15 complete by project metadata.
- **Lebl, *Introduction to Real Analysis, Volume I*** — GLM and Kimi report ReasBook coverage of Chapters 0–7 / Volume I declarations complete; this does not settle the whole series.
- **May, *A Concise Course in Algebraic Topology*** — GLM and Argon report a substantial ReasBook formalization.
- **Forster, *Lectures on Riemann Surfaces*** — GLM and Argon report ReasBook coverage.
- **Klenke, *Probability Theory*** — all lanes treat ReasBook's effort as the incumbent. Kimi reports 99.29% theorem/lemma completion but 150 remaining `sorry` declarations and exclusion from the active release profile: finish or audit it rather than duplicate it.
- **Rockafellar, *Convex Analysis*, and the ReasBook optimization cluster** — Bauschke & Combettes, Nesterov, Beck, Sun & Yuan, and related convex-optimization texts are already substantially represented; Argon also reports heavy Prove2Me extraction from Boyd & Vandenberghe and Murota.
- **Magnus, Karrass & Solitar, *Combinatorial Group Theory*** — GLM and Argon report ReasBook coverage.
- **Sipser, *Introduction to the Theory of Computation*** — GLM reports ATLAS coverage of 71% of 118 targets plus extensive Mathlib computability infrastructure; low marginal value for a new book project.
- **Aigner & Ziegler, *Proofs from THE BOOK*** — Kimi reports a near-complete official repository with remaining proof-bearing `sorry`s; residual work, not a clean-room duplicate.
- **CLRS, *Introduction to Algorithms*** — Kimi and Argon both reject a new project because CLRS-Lean already covers 1,689 selected/curated entries across 35 chapter guides. They disagree on whether that amounts to book completion under the strict contract; see §6.
- **Chan, *An Invitation to q-Series*** — Argon reports a Lean formalization.
- **Lattimore & Szepesvári, *Bandit Algorithms*, and Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*** — Argon reports both as completed full-book Prove2Me missions.
- **Conforti, Cornuéjols & Zambelli, *Integer Programming*** — GLM reports substantial ReasBook coverage.

### Already in flight or high collision risk: coordinate, audit, or take a scoped residual instead

- **Etingof et al., *Introduction to Representation Theory*** — Argon reports two active Lean efforts, with 402/452 files already `sorry`-free in one count.
- **Serre, *A Course in Arithmetic* †** — Argon reports active zero-`sorry` work on early chapters; Kimi and GLM shortlist it. Hold pending §6 verification.
- **Apostol, *Introduction to Analytic Number Theory* †, and Davenport, *Multiplicative Number Theory*** — GLM warns that PNT+/IEANTN and Mathlib's L-series/Dirichlet work are colonizing the content; Argon nevertheless shortlists Apostol.
- **Silverman elliptic-curve texts** — GLM rejects its Silverman entry because the FLT project, ATLAS Sutherland notes, and Mathlib elliptic-curve work collide on all sides; Kimi separately rejects Joseph Silverman's *The Arithmetic of Elliptic Curves* as multi-year with major prerequisites. The reports give different titles, so do not treat their bibliographic identity as settled without checking.
- **Hartshorne, *Algebraic Geometry*** — Argon reports Chapter I §§1–7 already in flight and the whole book at more than 1,400 nodes.
- **Wilde, *Quantum Information Theory*** — Argon reports section-by-section work merged into PhysLib.
- **Pierce, *Types and Programming Languages*** — Kimi reports substantial active partial coverage of 19 core chapters but explicit omission of 13; any work should be a scoped residual after audit, not a duplicate core.
- **Nielsen & Chuang, *Quantum Computation and Quantum Information*** — Kimi reports large adjacent AxQM coverage and lower differentiation from existing finite-dimensional quantum libraries.
- **Riehl, *Category Theory in Context* †** — GLM rejects it as low marginal value; Kimi shortlists it. See §3.

### Too large, prerequisite-blocked, or structurally unsuited to the next strict complete-book slot

- **Dummit & Foote, *Abstract Algebra*** — all three lanes reject it as oversized and duplicative; Kimi estimates roughly 1,200–1,700 nodes.
- **Lang, *Algebra*** — Kimi and Argon reject it as a mega-tome duplicating several narrower algebra projects.
- **Jech, *Set Theory*** — GLM and Argon reject it as oversized/prerequisite-heavy; GLM also rejects Kunen for the same forcing-infrastructure reason.
- **Evans, *Partial Differential Equations*** — Argon groups it with the >1,000-node mega-tomes.
- **Durrett, *Probability: Theory and Examples*** — Kimi estimates 520–650 nodes before all definitions are counted and regards it as a multi-year probability spine, unlike Williams.
- **Washington, *Introduction to Cyclotomic Fields*** — Kimi regards Iwasawa theory and the Main Conjecture scope as multi-year and dependent on missing/non-core p-adic L-function layers.
- **Bott & Tu, *Differential Forms in Algebraic Topology*** — Kimi: the source is explicitly non-foundational and quotes key results without proof; strict coverage would add spectral sequences and characteristic classes to the manifold/forms stack.
- **Lee, *Introduction to Riemannian Manifolds*** — Kimi: curvature, geodesics, and global-analysis prerequisites are not ready at book scale.
- **Lee, *Introduction to Smooth Manifolds*** — GLM: no Sard theorem in the required form, no integration of forms/de Rham layer, and no Lie-group infrastructure sufficient for the book. This is a different Lee book from the Riemannian one above.
- **Takhtajan, *Quantum Mechanics for Mathematicians*** — Kimi: regularized determinants, Grassmann/Berezin integration, supermanifolds, localization, and index theory turn it into several programmes.
- **Arnold, *Mathematical Methods of Classical Mechanics* †** — GLM shortlists it only as multi-year; Kimi rejects it because the appendices make the strict obligation multi-field and multi-year.
- **Hatcher, *Algebraic Topology* †** — GLM rejects it as prerequisite-blocked; Kimi shortlists it as a long-horizon investment. See §§3 and 6.
- **Diestel, *Graph Theory*, and other graph-theory texts** — Kimi finds Diestel's graph-minor obligation incompatible with strict coverage as scoped; GLM reports Menger, planarity, coloring, and min–max prerequisites missing and teaching-side work already being colonized elsewhere.
- **Øksendal, *Stochastic Differential Equations*** — Kimi: important results are accepted without proof in the source, requiring substantial reconstruction beyond transcription.
- **Ireland & Rosen †** — Kimi rejects it only under strict whole-edition coverage because of the proofless survey chapter; GLM shortlists it. See §3.

### Low marginal value or role already filled

- **Folland, Royden, and other general real-analysis texts** — GLM: Mathlib measure theory plus the queued Rudin analysis line already fill the role.
- **Halmos, *Naive Set Theory*, and introductory proof texts such as Hammack and Velleman** — GLM: content is already in Mathlib at higher rigor or has low marginal value for this programme.
- **Nipkow & Klein, *Concrete Semantics*** — Kimi: complete Isabelle coverage lowers the return on a Lean port; Winskel offers more new joined-up Lean infrastructure.
- **Munkres, *Topology* †** — Kimi and Argon reject it despite GLM's #1 ranking. See §3.
- **Neukirch and other class-field-theory-first books** — GLM regards the area as premature and actively claimed by the Clay CFT effort. Marcus is contested separately in §3 because Argon gives a book-specific readiness case.

## 5. Recommended first three books to start

### 1. Atiyah & Macdonald, *Introduction to Commutative Algebra*

Start here because it is the only candidate ranked first by two lanes and combines bounded scope with unusually concrete Mathlib anchors across ideals, modules, localization, primary decomposition, integrality, chain conditions, Dedekind domains, completions, and dimension. Kimi and Argon both make Chapter 11 the critical risk—Hilbert functions/polynomials, Hilbert–Samuel theory, and the equivalence of local-dimension characterizations—so the launch should begin with a frozen 1969-edition ledger plus a Chapter 11 pilot, not with an assumption that the whole book is a simple harvest. The primary-decomposition disagreement in §6 must also be resolved before Chapter 4 effort is estimated.

### 2. Williams, *Probability with Martingales*

Start in parallel because it is the sole unanimous shortlistee and opens a field Rudin's queued trilogy deliberately does not cover: conditional expectation, discrete-time martingales, uniform integrability, backwards martingales, Kakutani products, and limit theorems. The reports converge on strong Mathlib readiness for the core—conditional expectation, optional stopping/sampling, upcrossing/convergence, strong law, and parts of the CLT/characteristic-function apparatus—while identifying Kakutani, Lévy downward/backwards convergence, and Lindeberg–Feller as real new work. Before coding, reconcile the reports' conflicting chapter and node counts against one frozen edition and make those three gaps explicit pilot packages.

### 3. Enderton, *A Mathematical Introduction to Logic*

Start as the third, complementary lane because Kimi and GLM independently place it in their top five, estimate roughly the same 230–330-node scope, and agree that Mathlib plus Foundation already supply many landmarks—first-order semantics, satisfiability/compactness material, recursive functions, halting/reducibility, and incompleteness results—without supplying Enderton's book-ordered development. Its decisive pilots are exactly the fidelity risks both lanes identify: Enderton's Hilbert calculus versus Foundation's LK completeness proof, and Presburger arithmetic/quantifier elimination, which Kimi notes is still an explicit Mathlib TODO. If those pilots close faithfully, the rest is a coherent harvest-and-bridge project rather than a new foundations programme.

## 6. Factual contradictions — verification required

The following are **not resolved in this synthesis**. They should be checked against repositories, current Mathlib declarations, and a frozen edition before any launch decision relies on them.

1. **Atiyah–Macdonald primary decomposition.** Kimi says Mathlib's Lasker module explicitly covers Atiyah–Macdonald Theorems 4.5 and 4.10 and, in its deep dive, that Mathlib contains Lasker–Noether decomposition and the two cited uniqueness results. Argon's deep dive says the Lasker–Noether uniqueness theorems for primary decompositions of ideals are missing and rates Chapter 4 only 40% ready, although its summary separately lists the second uniqueness theorem as the gap. **Verify:** the exact declarations in Mathlib's Lasker/primary-decomposition modules and whether their statements match Theorems 4.5 and 4.10 in scope (ideals versus modules, minimality, isolated components).

2. **Atiyah–Macdonald Artin–Rees readiness.** Argon's executive summary calls “general Artin–Rees” an unverified target and its profile identifies the general good-filtration version as a gap, while its Chapter 7 blueprint says Artin–Rees and Krull intersection are in Mathlib. Kimi cites exactness of adic completion but does not make the same general claim. **Verify:** which Artin–Rees statement, under which filtration hypotheses, is actually in Mathlib.

3. **Serre, *A Course in Arithmetic*: project identity and extent.** Kimi identifies `are4c4/SerreNumberTheoryBlueprint`, says its formalization tree contains Chapter 1 with four files, and finds no near-complete book. Argon identifies both `are4c4/SerreNumberTheoryAI` and the Blueprint, says Chapter I and Chapter II §§1–3.1 are already formalized with zero `sorry`s, and says modular forms are actively underway. GLM says no Lean book formalization was found. **Verify:** repository identity/branches, current file inventory, chapter coverage, `sorry` count, and axiom audit.

4. **Williams: basic bibliography and scope.** Kimi describes Chapter 0, Chapters 1–18, and appendices, estimating 300–450 nodes. Argon describes Chapters 0–15 plus appendices and gives about 245 nodes in its table but about 215 in its deep dive. GLM describes 15 chapters plus a “front H” measure-theory part and estimates about 330 nodes. **Verify:** the exact edition/printing, table of contents, appendix policy, and node-count rule before using any estimate.

5. **Hatcher and current Mathlib topology.** GLM says Mathlib has no homology theory, no Seifert–van Kampen, and no CW-complex chapter. Kimi cites existing CW complexes, fundamental groupoids, covering maps, basic singular homology and homotopy invariance, and an Eilenberg–Steenrod interface. **Verify:** declaration-level coverage and generality in current Mathlib; filename-level checks are insufficient for this dispute.

6. **Grinberg's completeness under the strict standard.** GLM and Argon describe *An Introduction to Algebraic Combinatorics* as 340/340 targets formalized. Kimi agrees the target coverage is extensive but says four exercises remain unattempted and flags `native_decide` use requiring an axiom audit. **Verify:** whether the 340 targets exhaust the main text only or the strict inventory, the status of exercises, and the project's transitive axioms.

7. **CLRS's completeness under the strict standard.** Argon's do-not table calls CLRS “Already Done in Lean 4” and says CLRS-Lean formalizes 35/35 chapters. Kimi says the same project reports 1,689/1,689 **selected** theorem entries across 35 chapter guides but expressly excludes every exercise/problem and full section coverage. **Verify:** the project's own scope statement against the programme's complete-main-text definition.

8. **Walters scope and estimates.** GLM describes 9 chapters and about 250 nodes. Argon describes Chapters 0–10 and gives about 275 nodes in its shortlist table but about 290 in its profile. **Verify:** edition, chapter inventory, and whether introductory/appendix material is counted.

9. **Serre, *Linear Representations of Finite Groups*: “untouched” wording.** Argon's executive summary calls the book completely unformalized in any proof assistant, while its detailed profile more narrowly says no complete book exists and discloses Coq character-theory work from the Odd Order project and Isabelle AFP Part I material. **Verify/use carefully:** the defensible claim from Argon's own evidence is “no complete book formalization found,” not “no part has ever been formalized.”

10. **Node-count comparability generally.** Serre's *A Course in Arithmetic* is estimated at 150–210 nodes by Kimi but about 300 by GLM; Atiyah–Macdonald and Williams also receive materially different totals across—and sometimes within—reports. These differences may reflect different treatment of definitions, remarks, worked examples, appendices, and unnumbered results rather than arithmetic error. **Verify:** no candidate should advance on node count alone until a Phase-0 source ledger applies one counting contract to the frozen edition.

