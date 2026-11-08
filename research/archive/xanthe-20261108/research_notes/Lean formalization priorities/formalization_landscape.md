# Cross-cutting landscape of complete-book and near-complete mathematical formalizations

## What exactly are the ATLAS book list, formal-conjectures, Prove2Me, Lean Archive and related resources, and how should their coverage be interpreted?

### Takeaway

These resources answer different questions. ATLAS and ReasBook expose book-aligned target inventories; Prove2Me exposes audited mission milestones; Lean Pool archives completed named-result projects; formal-conjectures collects statements, often intentionally without proofs. None of them, by itself, certifies the brief's strict notion of a complete book: every definition and theorem in order, zero `sorry`, standard axioms only, faithful statements, and hostile review.

**Audit window:** 2026-10-21 and 2026-10-22. **Confidence notation:** **[H]** = primary documentation/source inspected, often supplemented by a local source scan; **[M]** = bounded evidence or a project's un-rebuilt status claim; **[L]** = weak/search-only evidence. Confidence describes the evidence for the stated claim, not whether the underlying project is mathematically faithful.

### Cited Findings

#### ATLAS: a book-aligned target library, not a list of 26 finished books

- **[H]** ATLAS v1 is a Lean 4 autoformalization effort over 26 open-access books. Its archived README reports 4,007 selected target statements, 2,855 formalized targets (71.3%), 46,203 declarations, and 42,837 proved declarations (92.7%). The denominator for “proved” is declarations, not textbook nodes; the denominator for “formalized” is selected targets, not necessarily every definition and theorem in the source. Each book has `targets.yaml` and `report.json`. [ATLAS v1 README and statistics](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md).
- **[H]** The companion paper is explicit: “none of the books are fully formalized.” It also says statements whose proofs occur in the source must be proved without `sorry` or axioms, but statements whose proof is deferred to another source may be axiomatized. That policy is weaker than this programme's blanket zero-`sorry`, standard-axioms-only requirement. [Formalizing Mathematics at Scale, §§3 and 5](https://arxiv.org/html/2605.29955v1).
- **[H]** The current repository preserves v1 under `v1/`; v2 is in development. The root package currently emphasizes `MathlibExt`, `CSLibExt`, tests, and `WantedExt`, and the old `Atlas/` and `v1/` developments are outside the root build. Thus the v1 table is an audit snapshot, not a live guarantee of v2 status. [Current ATLAS repository](https://github.com/facebookresearch/atlas-lean).

**ATLAS v1 book list, all values self-reported in the archived README [H for the inventory; not evidence of strict completion]:**

| ATLAS project / principal source | Formalized / selected targets | % |
|---|---:|---:|
| AlgebraNotes — MIT Algebra I notes | 151 / 176 | 85.8% |
| AlgebraicCombinatorics — MIT 18.318 | 37 / 39 | 94.9% |
| AlgebraicGeometryI — MIT 18.725 | 112 / 186 | 60.2% |
| AlgebraicTopologyI — MIT 18.905 | 110 / 171 | 64.3% |
| AnAlgorithmistsToolkit — MIT 18.409 | 131 / 158 | 82.9% |
| ArithmeticGeometry — MIT 18.782 | 266 / 335 | 79.4% |
| BooleanFunctions — MIT 18.218 | 44 / 108 | 40.7% |
| Buildings — Paul Garrett's book | 44 / 74 | 59.5% |
| CombinatorialOptimization — MIT 18.433 | 22 / 36 | 61.1% |
| ComplexVariables — MIT 18.112 | 37 / 38 | 97.4% |
| DifferentialAnalysis — MIT 18.155 | 88 / 113 | 77.9% |
| DifferentialGeometry — MIT 18.950 | 112 / 147 | 76.2% |
| EllipticCurves — MIT 18.783 | 212 / 360 | 58.9% |
| FourierAnalysis — MIT 18.103 | 34 / 38 | 89.5% |
| GeometryOfManifolds — MIT 18.966 | 40 / 72 | 55.6% |
| HighDimensionalStatistics — MIT 18.S997 | 65 / 73 | 89.0% |
| IntroductionToFunctionalAnalysis — MIT 18.102 | 68 / 72 | 94.4% |
| IntroductionToPartialDifferentialEquations — MIT 18.152 | 86 / 105 | 81.9% |
| LieGroups — MIT 18.757 | 74 / 185 | 40.0% |
| NumberTheoryI — MIT 18.785 | 460 / 576 | 79.9% |
| ProbabilisticMethodsInCombinatorics — MIT 18.226 | 109 / 210 | 51.9% |
| ProjectionTheory — MIT 18.156 | 73 / 111 | 65.8% |
| RealAnalysis — MIT 18.100A | 175 / 177 | 98.9% |
| TensorCategories — MIT 18.769 | 137 / 229 | 59.8% |
| TheoryOfComputation — MIT 18.404J | 84 / 118 | 71.2% |
| TheoryOfProbability — MIT 18.175 | 84 / 100 | 84.0% |
| **Total** | **2,855 / 4,007** | **71.3%** |

Source for every row and the outgoing book links: [ATLAS v1 README](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md). In particular, RealAnalysis, ComplexVariables, IntroductionToFunctionalAnalysis, and AlgebraicCombinatorics are near-complete **target sets**, not completed books.

#### formal-conjectures: statements and benchmarks, not book coverage

- **[H]** Google DeepMind's `formal-conjectures` is a Lean 4/Mathlib collection of formalized statements of conjectures. Its stated motivation is the lack of open conjectures for which only the statement is formalized; it supports benchmarking, clarification of conjectures, and expansion of Mathlib. It warns that statement-only formalization can be subtly inaccurate. `@[formal_proof]` records proofs for some solved problems, but a proved conjecture is still one result, not a book inventory. [Repository goals and accuracy note](https://github.com/google-deepmind/formal-conjectures); [documentation site](https://google-deepmind.github.io/formal-conjectures/).
- **[H]** A 2026-10-22 recursive tree inspection found 2,130 entries and no paths containing `Riehl`, `Wilf`, `Generating`, `Concrete`, `Petkovsek`, `Zeilberger`, or `Gosper`. This is only a path check, not a semantic search of source citations. [Formal-conjectures tree API](https://api.github.com/repos/google-deepmind/formal-conjectures/git/trees/main?recursive=1).

#### Prove2Me and Formalpedia: completed missions, not necessarily completed books

- **[H]** Prove2Me is a collaborative Lean 4 platform in which a captain proposes a mission for a paper, textbook, or open problem. Humans audit the curated core—goal, definitions, and milestone lemmas—while agents may add unaudited intermediate lemmas. A proof must match the fixed statement and contain no `sorry` or new axiom. Formalpedia is the reusable library of proved, atomized statements produced by missions. [Prove2Me paper, §§3–4](https://arxiv.org/html/2608.28433v2); [official FAQ](https://prove2.me/faq).
- **[H]** A mission completes when its audited milestones are proved and connected so the goal resolves. That is not equivalent to proving every definition, theorem, example, and exercise in a book. The design deliberately limits human faithfulness review to the mission core. [Prove2Me paper, especially §§3.3 and 4.4](https://arxiv.org/html/2608.28433v2).
- **[H]** The live collection page reported **4,820 missions across 23 collections, 2,442 solved and 2,378 open** on 2026-10-22. Examples of partial book-aligned collections were Murota's *Discrete Convex Analysis* at 33/35 missions, Vershynin/Wainwright high-dimensional probability/statistics at 18/25, Grünbaum's *Convex Polytopes* at 4/18, and Bäuerle–Rieder Markov decision processes at 18/21. Percentages are mission counts, not source-node counts. [Prove2Me collections](https://prove2.me/collections).
- **[H]** The *Bandit Algorithms* collection displays 16/16 completed missions, and *Introduction to Linear Optimization* displays 13/13. Their own descriptions nevertheless reveal selected coverage. The bandit missions address Chapters 5–22, 24–28, and 33–38, with no missions for Chapters 1–4, 23, or 29–32, and select headline results rather than every source node. [Bandit collection](https://prove2.me/collections/bandit-algorithms). The linear-optimization missions address selected parts of Chapters 2–5, 7–9, and 11, with no missions for Chapters 6 or 12 and only selected material in Chapters 10–11. [Linear optimization collection](https://prove2.me/collections/introduction-to-linear-optimization).
- **[H]** The paper calls both “completed textbooks” in its case-study table, but the public mission inventories are the better evidence for what “completed” means operationally. Do not translate that table into strict whole-book completion. [Paper, Table 1](https://arxiv.org/html/2608.28433v2); the two collection pages above.

#### “Lean Archive”: ambiguous name; use the actual resource, not an imagined book index

- **[M]** Exact searches for `"Lean Archive" formalized mathematics books`, `"Lean Archive" mathlib`, and `site:leanprover-community.github.io "archive" projects` on 2026-10-21 did not identify an official book-coverage resource with that exact name. The Lean community does have a **Zulip chat archive**, which is not a formalization inventory. [Lean community site](https://leanprover-community.github.io/); [Lean projects page](https://leanprover-community.github.io/lean_projects.html).
- **[H]** The likely intended resource is **Lean Pool**, self-described as an AI-maintained archive. Its September 2026 paper listed 211 projects, but the live repository on 2026-10-22 listed **289 formalization projects and 9,933,135 lines of Lean**. It accepts completed, permissively licensed projects, builds them warning-free, and gates them on no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, and other quality checks. “Completed project” means a completed named result or development, not a completed source book. [Live Lean Pool repository](https://github.com/Vilin97/lean-pool); [Lean Pool paper](https://arxiv.org/html/2609.25199v1).
- **[H]** Lean Pool's paper appendix is useful for negative evidence because it names a project's mathematical source. Examples include one Turán theorem from *Proofs from THE BOOK*, factorization systems from *Category Theory in Context*, one density-one divisibility result from *Concrete Mathematics*, and Hanson–Wright from *High-Dimensional Probability*. These are theorem-level entries, not whole-book formalizations. [Lean Pool paper, project index](https://arxiv.org/html/2609.25199v1).

#### Reusable source/URL map

| Resource | What it actually contains | Coverage inference that is safe | Primary URL |
|---|---|---|---|
| Mathlib | Integrated, reviewed Lean mathematics | A theorem's presence can discharge a prerequisite; it never implies a source book was covered in order | [Mathlib](https://github.com/leanprover-community/mathlib4); [documentation](https://leanprover-community.github.io/mathlib4_docs/) |
| Lean community projects and intentions | Representative downstream projects plus early-stage intentions | Useful for collision checks; the page explicitly warns that registration is incomplete | [Lean projects](https://leanprover-community.github.io/lean_projects.html) |
| Reservoir | Registry that indexes, builds, and tests Lean/Lake packages | Package discovery and build status, not book completeness | [Reservoir](https://reservoir.lean-lang.org/) |
| ATLAS v1/v2 | Book-aligned targets, Lean declarations, provenance and automated evaluations | Compare target inventories; never equate declaration count or “proved %” with whole-book coverage | [ATLAS](https://github.com/facebookresearch/atlas-lean); [v1 list](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md) |
| ReasBook / M2F | Versioned book and paper projects with per-book `book.yml` statistics | Read the exact branch, coverage field, chapter tree, placeholders, and release status separately | [ReasBook catalog](https://github.com/optpku/ReasBook); [M2F](https://github.com/optsuite/M2F) |
| Prove2Me / Formalpedia | Audited mission cores, proof sketches, atomized proved statements | Mission completion only; compare the mission inventory to the book's table of contents | [Collections](https://prove2.me/collections); [FAQ](https://prove2.me/faq) |
| Lean Pool | Maintained archive of completed named-result projects | Strong evidence for a named result; a book citation is not whole-book evidence | [Lean Pool](https://github.com/Vilin97/lean-pool) |
| Tau Ceti | Integrated AI-authored library downstream of Mathlib, directed by human roadmaps and adversarial review | Roadmap/theorem coverage, not a book-aligned inventory | [Tau Ceti](https://github.com/TauCetiProject/TauCeti) |
| formal-conjectures | Formal statements of open and solved conjectures | Statement/benchmark coverage only | [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) |
| ProofNet | 371 Lean 3 benchmark examples with formal statement, informal statement, and informal proof, drawn largely from textbooks | A textbook-derived benchmark, not any book's complete coverage | [ProofNet](https://github.com/zhangir-azerbayev/ProofNet) |
| Lean-GAP | 430 formalized graduate-algebra problems from Dummit–Foote | Exercise-dataset coverage only | [Lean-GAP paper](https://arxiv.org/html/2606.02588v1) |
| Isabelle Archive of Formal Proofs | Refereed Isabelle proof libraries, examples, and larger developments | Strong named-development evidence in Isabelle, not automatic book completeness or Lean absence | [AFP](https://www.isa-afp.org/) |

### Inferences

- Treat **source inventory**, **proof status**, **axiom footprint**, **statement fidelity**, and **review status** as five separate fields. A project can be excellent at four and fail the fifth. ATLAS's selected-target percentage and Prove2Me's mission percentage are not interchangeable with the first field.
- The most useful audit artifacts are ATLAS `targets.yaml`/`report.json`, ReasBook `book.yml`, Prove2Me mission descriptions, and Lean Pool source attributions. README adjectives such as “complete,” “comprehensive,” and “whole” are leads to inspect, not evidence classes by themselves.
- A completed named theorem in Mathlib, Lean Pool, Formalpedia, AFP, Coq, or HOL Light reduces duplicated work but does not disqualify a book. A different-proof-assistant full book reduces novelty but remains eligible under the brief's exception if no Lean version exists.

### Gaps

- ATLAS v2 was still in development; no v2 whole-book completion claim was verified. [Current repository](https://github.com/facebookresearch/atlas-lean).
- `https://prove2.me/api/v1/missions?limit=100&offset=0` returned HTTP 401 on 2026-10-21. Public HTML collections were inspected, but individual missions for every candidate could not be exhaustively searched. This weakens all candidate-specific Prove2Me negatives.
- No official resource named exactly “Lean Archive” was identified; if the brief intended another site, that identification remains open. Lean Pool, Reservoir, the Lean community project list, and the Zulip archive should not be conflated.
- ReasBook's catalog and version branches evolve independently. Klenke's *Probability Theory: A Comprehensive Course* was marked source-only/excluded from the active release profile, and no reliable completion metrics were obtained. [ReasBook catalog](https://github.com/optpku/ReasBook).

## Which canonical books already have complete or near-complete formalizations, with direct evidence, and which commonly cited projects are only partial or theorem collections?

### Takeaway

The strongest Lean whole-book evidence found is for Spivak's *Calculus*, Leinster's *Basic Category Theory*, Beck's *First-Order Methods in Optimization*, Lebl's *Introduction to Real Analysis, Volume I*, and the main-text targets of Grinberg's *An Introduction to Algebraic Combinatorics*. Even these require different caveats: independent build/fidelity review was not performed here, Grinberg retains exercise holes and uses `native_decide`, and ReasBook coverage fields must be compared with the original book before “whole book” is accepted.

Many attractive books are instead near-complete, selected-target projects, or active mission series. They should generally be treated as residual-completion or collaboration opportunities, not as untouched new book projects.

### Cited Findings

#### Strong Lean completion claims and do-not-formalize evidence

| Book / project | Direct scope and proof evidence | Strict-standard assessment | Confidence |
|---|---|---|---|
| **Michael Spivak, _Calculus_, 3rd and 4th editions** | README claims every definition, theorem, corollary, worked example, and every problem in all 30 chapters and nine appendices, with edition concordance and corrections. `AuditAll.lean` runs `Lean.collectAxioms` over every `Spivak` declaration and expects only `propext`, `Classical.choice`, and `Quot.sound`. [README](https://github.com/stormj-UH/spivak-lean); [PROGRESS](https://github.com/stormj-UH/spivak-lean/blob/fourth-edition/PROGRESS.md); [audit code](https://raw.githubusercontent.com/stormj-UH/spivak-lean/fourth-edition/SpivakCalculus/AuditAll.lean). My clone at [`c24e9fc`](https://github.com/stormj-UH/spivak-lean/commit/c24e9fcb7e96873ea9d4769c453be1b3ca48d211) had 162 Lean files/116,120 lines and zero textual `sorry`, `admit`, custom `axiom`, or `native_decide`. | **Do not start a new book project.** This is the closest match to the strict target found. Independent build and hostile statement review remain unverified here. | [H] |
| **Tom Leinster, _Basic Category Theory_** | Repository claims Introduction, all six chapters, and GAFT appendix; 496 declarations, 26/26 checklist items, zero `sorry`, standard axioms only. [Repository](https://github.com/whoiam1101/basic-category-theory-lean4). My clone at [`64182ea`](https://github.com/whoiam1101/basic-category-theory-lean4/commit/64182ea378da340d64cee4b31a4c6975112347bb) had 19 Lean files/7,615 lines and zero textual `sorry`, `admit`, custom `axiom`, or `native_decide`. | **Do not duplicate.** Full source fidelity was not independently reviewed; the repository's own detailed checklist is the best current evidence. | [H] |
| **Amir Beck, _First-Order Methods in Optimization_** | ReasBook `book.yml` says “Complete formalization of Chapters 1–15,” with 6,227/6,227 theorem/lemma/example declarations and zero `sorry`/`admit`. [Versioned metadata](https://raw.githubusercontent.com/optpku/ReasBook/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/book.yml). | **Do not duplicate the main chapters.** Check appendices and source fidelity before calling it strict-complete. | [H for metadata; M for whole-book status] |
| **Jiri Lebl, _Introduction to Real Analysis, Volume I_, v6.2 (2025)** | ReasBook says Chapters 0–7, 1,202/1,202 declarations, zero `sorry`/`admit`. [Versioned metadata](https://raw.githubusercontent.com/optpku/ReasBook/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/book.yml). | **Do not duplicate.** This is Volume I only, not the series. | [H for metadata; M for hostile review] |
| **Darij Grinberg, _An Introduction to Algebraic Combinatorics_** | Repository reports 340 target theorems across 45 chapters; every theorem whose proof appears in the book is formalized, with four exercise targets unattempted. [Repository and chapter status](https://github.com/facebookresearch/algebraic-combinatorics); [companion paper](https://arxiv.org/html/2604.03071). My clone at [`b602231`](https://github.com/facebookresearch/algebraic-combinatorics/commit/b6022318e986a0c20764569208ba8ebbe1c04dbf) had 54 Lean files/130,245 lines, five actual `sorry` lines associated with the unattempted exercises, no actual custom `axiom` declaration, and 192 `native_decide` tokens. | **Do not restart as an untouched book.** Main-text coverage is extensive, but blanket zero-`sorry` and standard-axiom compliance are not established. A residual exercise/axiom audit is the appropriate task, not a fresh duplicate. | [H] |
| **R. Tyrrell Rockafellar, _Convex Analysis_** | ReasBook reports Chapters 1–8 and 10,666/10,666 declarations with zero `sorry`/`admit`. [Versioned metadata](https://raw.githubusercontent.com/optpku/ReasBook/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/book.yml). The README indexes Parts I–V section-by-section but lacks comparable section links for Parts VI–VIII. [Project catalog](https://github.com/optpku/ReasBook). | **Substantial existing work; do not assume either strict completeness or that the book is untouched.** Reconcile Parts VI–VIII against the original table of contents before deciding whether only residual work remains. | [H for metadata; M for whole-book interpretation] |

#### ReasBook audit list: versioned status is more informative than the catalog title

The following are direct `book.yml` or catalog values. “Proof completion” is the repository's declaration metric, not an independently verified source-node metric.

| Book | Declared scope and placeholders | Audit consequence | URL |
|---|---|---|---|
| Tao, _Analysis II_, 4th ed. | Chapters 1–8; 2,554/2,557; 3 `sorry`, 2 `admit` | Near-complete, not strict-complete | [book.yml](https://raw.githubusercontent.com/optpku/ReasBook/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/book.yml) |
| May, _A Concise Course in Algebraic Topology_ | Only Chapters 1–3 visible; 1,620/1,626; 6 `sorry`, 1 `admit` | Partial | [catalog](https://github.com/optpku/ReasBook) |
| Magnus–Karrass–Solitar, _Combinatorial Group Theory_ | 1,312/1,757; 445 `sorry`, 6 `admit` | Large skeleton/partial project | [catalog](https://github.com/optpku/ReasBook) |
| Bauschke–Combettes, _Convex Analysis and Monotone Operator Theory in Hilbert Spaces_ | Chapters 1–20 visible; 4,092/4,930; 838 `sorry`, 3 `admit` | Large partial project | [catalog](https://github.com/optpku/ReasBook) |
| Nesterov, _Introductory Lectures on Convex Optimization_ | Chapters 1–7; 14,587/14,663; 76 `sorry` | Near-complete declarations, not zero-`sorry` | [catalog](https://github.com/optpku/ReasBook) |
| Sun–Yuan, _Optimization Theory and Methods: Nonlinear Programming_ | Chapters 1–14; 8,132/8,426; 301 `sorry` | Partial | [catalog](https://github.com/optpku/ReasBook) |
| Forster, _Lectures on Riemann Surfaces_ | Only Chapter 1 visible; 129/174; 45 `sorry` | Early partial | [catalog](https://github.com/optpku/ReasBook) |
| Conforti–Cornuéjols–Zambelli, _Integer Programming_ | “Skeleton only—no chapters formalized yet”; 0/0 | Zero placeholders is meaningless here | [catalog](https://github.com/optpku/ReasBook) |
| Vogel, _Computational Methods for Inverse Problems_ | Chapters 1–9; 3,811/3,916; 105 `sorry` | Partial; catalog release status and branch metadata differ | [book.yml](https://raw.githubusercontent.com/optpku/ReasBook/v4.32.0/ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/book.yml) |
| Klenke, _Probability Theory: A Comprehensive Course_ | Source only, excluded from current release profile | No completion inference | [catalog](https://github.com/optpku/ReasBook) |
| Beck and Lebl | See strong-completion table above | Main-chapter/zero-placeholder claims | [ReasBook](https://github.com/optpku/ReasBook) |
| Rockafellar | See strong-completion table above | Zero placeholders, whole-source scope still to reconcile | [ReasBook](https://github.com/optpku/ReasBook) |

#### Other significant Lean projects that are partial, selected, or not strict-complete

- **Tao, _Analysis I_ [H].** The author's companion covers Chapters 2–11 and appendices, but Chapter 1 is explicitly not formalized and portions left to the reader are intentionally rendered as `sorry`; the author does not intend to add solutions. It is a substantial book companion, not a zero-`sorry` completed book. The same repository also hosts a work-in-progress formalization of Tao's *Measure Theory*. [teorth/analysis](https://github.com/teorth/analysis).
- **Aigner–Ziegler, _Proofs from THE BOOK_ [H].** The official repository still describes itself as work in progress and welcomes new `sorry`s. [Repository](https://github.com/mo271/FormalBook). My clone at [`626d296`](https://github.com/mo271/FormalBook/commit/626d296add63fd39e52934f682142d6f9486dcf7) had all 45 chapter files, 68 Lean files/39,886 lines, and **26 actual proof-bearing `sorry` occurrences** in Chapters 6, 43, 45, and `Ch28/SpernerBrouwer`, plus four comments containing the word. A secondary page claiming “all 40 chapters, 0 sorry” is not a reliable description of this repository snapshot. It is near-complete, not strict-complete.
- **Cormen–Leiserson–Rivest–Stein, _Introduction to Algorithms_ (CLRS) [H].** CLRS-Lean has 1,689/1,689 **selected** theorem entries across 35 chapter guides, no `sorry`/`admit`/project axiom, and standard-axiom checks for flagship declarations. It explicitly says this is not complete fourth-edition section coverage, excludes every exercise/chapter-end problem, and leaves some pointer/RAM/imperative refinements for later layers. This is a major selected proof library, not a whole-book completion. [CLRS-Lean scope and progress](https://github.com/TankTechnology/CLRS-Lean).
- **Lattimore–Szepesvári and Bertsimas–Tsitsiklis [H].** Prove2Me's 16 and 13 completed mission series are substantial but selected, as documented in the first section. Do not call either whole book done; equally, do not present either as untouched.
- **ATLAS high-percentage books [H].** RealAnalysis (175/177), ComplexVariables (37/38), IntroductionToFunctionalAnalysis (68/72), and AlgebraicCombinatorics (37/39) are residual-target projects. The ATLAS paper says none of its 26 books is fully formalized. [ATLAS v1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md); [paper](https://arxiv.org/html/2605.29955v1).
- **Dummit–Foote, _Abstract Algebra_ [H].** Lean-GAP's 430 formalized problems are an exercise dataset, not whole-book coverage. [Lean-GAP](https://arxiv.org/html/2606.02588v1).
- **Popular textbook theorem collections [H].** ProofNet's 371 examples and individual results in Lean Pool, Mathlib, or Formalpedia are not book-specific inventories. [ProofNet](https://github.com/zhangir-azerbayev/ProofNet); [Lean Pool](https://github.com/Vilin97/lean-pool).

#### Other proof assistants: completion changes novelty, but only a Lean version is an automatic disqualifier

| Source and project | What is actually covered | Consequence for a Lean book project | Confidence |
|---|---|---|---|
| **Munkres, _Topology_, general-topology Chapters 2–8, in Isabelle/HOL** | 85,472 lines, 199 definitions and 806 formal results over all 39 sections §§12–50, with zero `sorry`; exercises excluded. [Paper](https://arxiv.org/html/2604.07455v1); [code](https://github.com/JUrban/isa_top_autoform1). | Not a Lean disqualifier under the exception, and not the whole book. Novelty is reduced for the corresponding general-topology material. | [H] |
| **The same Munkres project under hostile review** | Detailed review of Chapters 2–4 and samples later found a weakened topology predicate, incomplete/mislabeled statements, omitted sequential compactness/Theorem 28.2, nets, counterexamples, and ordering differences. The authors say proofs remain sound but definitions/statements have defects. [Paper §8](https://arxiv.org/html/2604.07455v1). | Zero `sorry` does not imply faithful complete-book coverage. A Lean version must not simply inherit these scope gaps. | [H] |
| **Munkres in Megalodon** | January 2026 report covers a “large portion,” over 1.5k lemmas/theorems, not the full book. [Paper](https://arxiv.org/html/2601.03298). | Another substantial non-Lean precedent, not whole-book evidence. | [H] |
| **Landau, _Foundations of Analysis_, in Rocq** | 2025 paper states all contents from natural through complex numbers were formalized and verified in Rocq 8.16 without the standard library. [Paper](https://www.mdpi.com/2227-7390/14/1/61). Van Benthem Jutting's 1977 Automath formalization is the historic earlier whole-book project. [Automath history](https://arxiv.org/html/2203.01173v3). | No Lean whole-book version was found in the bounded searches, so the exception could apply; novelty is reduced and Spivak now covers much of the same territory. | [H for other assistants; M for Lean negative] |
| **Enderton, _Elements of Set Theory_, in Coq and Lean** | Coq repository follows the textbook with EST2–EST8 and exercise files. [Coq project](https://github.com/choukh/Set-Theory). Lean repository covers only Chapters 2, 3, and 4 §1, with 258 declarations and no `sorry`; it deliberately introduces twelve object-theory axioms and documents that higher-order comprehension departs from first-order ZF. [Lean project](https://github.com/Qinggao1729/axiomatic-set-theory). | The Lean project is partial and outside standard-axiom-only completion. A new standard-axiom Lean development remains possible but would overlap two existing efforts. | [H] |
| **Euclid, _Elements_, Book I, in Lean** | LeanEuclid manually formalized all 48 Book I theorems/proofs; the full benchmark contains 48 Euclid problems plus 125 UniGeo problems and uses an SMT-backed formal System E. [Repository](https://github.com/loganrjmurphy/LeanEuclid); [paper](https://arxiv.org/html/2405.17216v1). | Book I is not the thirteen-book *Elements*. Do not propose Book I as fresh; do not infer the whole work is done. | [H] |
| **Tarski/Schwabhäuser and Euclid in GeoCoq** | GeoCoq provides chapter-indexed Tarski developments; Rocq package documentation describes Chapters 1–8 of *Metamathematische Methoden in der Geometrie*, and project literature also includes Euclid Book I. [GeoCoq](https://geocoq.github.io/GeoCoq/); [Rocq package description](https://rocq-prover.org/p/coq-tarski-geometry/8.9.0). | Strong geometry infrastructure and prior art, not complete coverage of either entire book. | [H] |
| **Bishop, constructive analysis, in Coq** | Cruz-Filipe's thesis explicitly describes formalizing a whole **chapter**—Chapter 2 of Bishop's book—not the entire book. [Thesis](https://core.ac.uk/download/pdf/16108998.pdf). | A frequently overgeneralized “book formalization” precedent; only chapter-level evidence. | [H] |
| **Homotopy Type Theory book, in Agda** | `HoTT-Book-Agda` assumes function extensionality, univalence, and HITs, and its contribution note explicitly says “I've skipped a ton.” [Repository](https://github.com/FernandoChu/HoTT-Book-Agda). | Not complete and not standard-axiom-only. Other HoTT libraries should not be treated as chapter-by-chapter book completion without an inventory. | [H] |

#### Consolidated do-not-formalize / do-not-duplicate audit list

1. **Strongly avoid a new project:** Spivak's *Calculus*; Leinster's *Basic Category Theory*; Beck's *First-Order Methods* main chapters; Lebl's Volume I. Evidence and remaining audit caveats are above.
2. **Main text is already substantially done; only residual/audit work makes sense:** Grinberg; Rockafellar; Tao's *Analysis I* and *Analysis II*; FormalBook; Nesterov; ATLAS RealAnalysis/ComplexVariables/IntroductionToFunctionalAnalysis/AlgebraicCombinatorics. Do not describe these as strict-complete, but do not sell them as greenfield either.
3. **Large existing selected developments require collaboration or a scoped residual proposal, not a duplicate from scratch:** CLRS; the two completed Prove2Me textbook series; ReasBook's May, Bauschke–Combettes, Sun–Yuan, Magnus–Karrass–Solitar, Forster, and Vogel projects; Prove2Me's Murota, Vershynin/Wainwright, Grünbaum, and Bäuerle–Rieder collections.
4. **Other-assistant completion lowers novelty but does not itself disqualify under the brief:** Munkres general topology and Landau. A Lean claim must include a fresh Lean-specific search and must not inherit the other project's semantic omissions.
5. **Scope traps:** Euclid Book I is not the *Elements*; Lebl Volume I is not Volume II; Munkres Chapters 2–8 are not the whole book; a completed Prove2Me collection is not every source node; a formal-conjectures entry is not a book; a famous theorem from a book is not the book.

### Inferences

- The current landscape already disqualifies several titles that would have been attractive in older surveys, especially Spivak, Leinster, Beck, Lebl, and Grinberg. A 2024–2025 shortlist is not a safe 2026 shortlist.
- The most common false positive is a large book-named repository with all currently selected targets proved. The most common false negative is assuming that remaining `sorry`s mean no substantial work exists. Both lead to bad project selection.
- Strict completion claims should be versioned by commit and original edition. For Spivak, the detailed source audit and full axiom checker are exemplary; for most other projects, independent hostile review remains the missing step.

### Gaps

- **No Lean toolchain was installed in the research environment.** Local source scans were run, but `lake build`, `#print axioms`, and `AuditAll.lean` were not independently executed. Consequently, no completion claim here is represented as independently kernel-rebuilt.
- Grinberg's `native_decide` usage needs a target-level transitive axiom audit; its presence was not used to infer either compliance or noncompliance. Exercise holes are directly visible, but exact source-target mapping was not independently rebuilt.
- Rockafellar's Parts VI–VIII, Beck's appendices, and the correspondence between ReasBook declaration counts and original source nodes remain unresolved.
- The detailed Isabelle Munkres review covered Chapters 2–4 and sampled later chapters; it does not establish that every later statement is defective, nor that every defect was fixed in the latest commit.
- No exhaustive audit of every Coq/Isabelle/HOL/Agda textbook was possible. The table records directly verified, high-relevance precedents, not a universal census.

## What searches and criteria support an honest not-already-done claim, and what are the limits of negative evidence?

### Takeaway

A defensible claim is: “No complete Lean 4 formalization was found in these named sources, at these revisions, using these exact queries, on this date; these partial projects do exist; confidence is bounded.” It is not defensible to turn a null web result into “this book has never been formalized.”

Strict acceptance requires independent evidence at five layers: source-node inventory, build/proof closure, transitive axiom audit, statement fidelity, and hostile review. A repository name or a green build addresses only part of that ladder.

### Cited Findings

#### Reusable audit protocol

1. **Freeze the source.** Record author, title, edition, year, table of contents, and whether examples, exercises, appendices, and cited-but-unproved results are in scope. The brief's baseline is every definition and theorem in order; do not silently narrow it. [Programme brief](../..//BRIEF.md) (local project brief).
2. **Search exact titles and aliases.** Use author + title + `Lean`, `Lean 4`, `formalization`, `formalisation`, `Coq`, `Rocq`, `Isabelle`, `HOL`, `Agda`, and `Mizar`; repeat with abbreviated titles and repository naming variants. Include arXiv, author pages, Zulip, GitHub repositories and code, Reservoir, and project issue trackers. [Lean projects](https://leanprover-community.github.io/lean_projects.html); [Reservoir](https://reservoir.lean-lang.org/).
3. **Check the special-purpose inventories separately.** ATLAS, ReasBook, Prove2Me, Lean Pool, formal-conjectures, Lean community intentions, and Tau Ceti have different semantics, summarized above. Do not substitute one for another. [ATLAS](https://github.com/facebookresearch/atlas-lean); [ReasBook](https://github.com/optpku/ReasBook); [Prove2Me](https://prove2.me/collections); [Lean Pool](https://github.com/Vilin97/lean-pool); [formal-conjectures](https://github.com/google-deepmind/formal-conjectures); [Tau Ceti](https://github.com/TauCetiProject/TauCeti).
4. **Inspect the artifact, not the snippet.** Record default and version branches, commit, latest activity, chapter tree, `README`, progress file, `book.yml`, target ledger, and CI. Count actual proof holes, not comments. [Spivak PROGRESS](https://github.com/stormj-UH/spivak-lean/blob/fourth-edition/PROGRESS.md) is a good example of a source-level audit trail.
5. **Run mechanical checks.** Build the pinned project; scan for `sorry`, `admit`, custom `axiom`, `unsafe`, `partial`, and `native_decide`; then run `#print axioms` or `Lean.collectAxioms` transitively over every target. Spivak's [`AuditAll.lean`](https://raw.githubusercontent.com/stormj-UH/spivak-lean/fourth-edition/SpivakCalculus/AuditAll.lean) demonstrates the required transitive pattern. A grep alone is not an axiom audit.
6. **Reconcile source nodes one by one.** Map every source definition/theorem to a Lean declaration and status; list omitted examples, exercises, appendices, external citations, and changed hypotheses explicitly. ATLAS's selected targets and CLRS's selected ledger illustrate why a smaller selected set can be 100% proved while the book is incomplete. [ATLAS v1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md); [CLRS scope](https://github.com/TankTechnology/CLRS-Lean).
7. **Review faithfulness hostilely.** Check carrier/domain conditions, empty and boundary cases, total-function fallback values, added hypotheses, missing conjunction clauses, vacuous typeclass assumptions, and whether definitions bake in a theorem. The Munkres review provides concrete failures of all these kinds. [Munkres review §8](https://arxiv.org/html/2604.07455v1).
8. **Search other proof assistants and classify the result separately.** Other-assistant coverage changes novelty and may supply a blueprint, but only an existing Lean version triggers the brief's automatic disqualification exception. [AFP](https://www.isa-afp.org/); [GeoCoq](https://geocoq.github.io/GeoCoq/); [HoTT-Book-Agda](https://github.com/FernandoChu/HoTT-Book-Agda).
9. **Publish the negative evidence with the result.** Exact queries, sites, dates, branch/commit, and known partial work must travel with the recommendation. Re-run immediately before project launch because the 2026 catalogs are changing quickly. [Live Lean Pool versus its older paper](https://github.com/Vilin97/lean-pool).

#### Exact general query log

| Date | Query / site | Result and how it was used |
|---|---|---|
| 2026-10-21 | `ATLAS book list Lean formalization` — web | Found official ATLAS repository and companion paper; v1 inventory then read directly. |
| 2026-10-21 | `formal-conjectures Lean GitHub` — web | Found official repository/docs; established statement-only benchmark semantics. |
| 2026-10-21 | `Prove2Me Lean formalization` — web | Found paper, FAQ, public missions and collection pages. |
| 2026-10-21 | `"Lean Archive" formalized mathematics books`; `"Lean Archive" mathlib`; `site:leanprover-community.github.io "archive" projects` — web | No official exact-name book index identified; Lean Pool and Lean community resources inspected separately. |
| 2026-10-21 | `Lean Pool GitHub formalized mathematics archive` — web | Found live repository and paper; noted live 289 projects versus paper's 211. |
| 2026-10-21 | `Lean "Tao's Analysis I" formalization`; `Lean "Analysis II" Zichen Wang formalization` — web | Found Tao companion and ReasBook; direct scope/placeholder checks followed. |
| 2026-10-21 | `Lean Munkres topology formalization 130k`; `Lean "Munkres" formalization github` — web | Found Megalodon and Isabelle projects, not a Lean whole-book version. Negative remains bounded. |
| 2026-10-21 | `"complete textbook" "Lean 4" mathematics`; `"every theorem" "textbook" "Lean" formalization`; `"whole book" formalized Coq mathematics` — web | Found Grinberg, Leinster, Spivak, and historical/partial precedents; all completion claims then checked at source. |
| 2026-10-21 | `Lean 4 "Spivak" Calculus formalization`; `"spivak-lean" sorry axioms` — web | Found current Spivak repository, progress log, and full axiom audit. |
| 2026-10-21 | `Lean "Euclid" "Book I" formalization Hernandez Espiet`; `GeoCoq Tarski book formalization coverage chapters`; `Coq Bishop constructive analysis formalization book chapter` — web | Established Book-I/chapter-level rather than whole-book coverage. |
| 2026-10-21 | `"Elements of Set Theory" Lean formalization Enderton`; `"Elements of Set Theory" Coq formalization complete` — web | Found partial Lean and book-length Coq artifacts; distinguished intentional ZF axioms from standard-axiom completion. |
| 2026-10-21 | `"Landau" "Foundations of Analysis" Lean formalization`; `"Foundations of Analysis" Isabelle Landau formalization` — web | Found Rocq/Automath precedents; no Lean whole-book project found in those searches. |
| 2026-10-21 | `HoTT book complete formalization Coq Agda coverage` — web | Found Agda repository explicitly acknowledging omissions and nonstandard assumptions. |

#### Candidate-specific query and registry log

| Candidate | Exact checks and outcomes | Negative-evidence confidence |
|---|---|---|
| **Riehl, _Category Theory in Context_** | GitHub API query `"Category Theory in Context" Lean in:readme` on 2026-10-22 returned 27 repositories. The three relevant results were inspected: [`rkirov/category-theory-in-context-lean`](https://github.com/rkirov/category-theory-in-context-lean) is only Chapter 1 §§1–4 and inactive; [`masak/category-theory-in-context`](https://github.com/masak/category-theory-in-context) is an exercise project; [`gaxiiiiiiiiiiii/Riehl`](https://github.com/gaxiiiiiiiiiiii/Riehl) covers selected parts of Chapters 1–4 and intentionally leaves proofs as `sorry`. Lean Pool's paper contains a factorization-systems project sourced to the book, not the book. [Lean Pool index](https://arxiv.org/html/2609.25199v1). No ATLAS, ReasBook, or named Prove2Me collection for the book was found. | **Medium-high** that no complete/near-complete Lean book exists; not a universal negative. |
| **Wilf, _generatingfunctionology_** | Web query `Lean "Generatingfunctionology" formalization` on 2026-10-21 found a University of Washington talk on examples, not a book project. [Talk record](https://math.washington.edu/events/2024-05-20/generating-functions-lean). GitHub API query `generatingfunctionology Lean in:readme` on 2026-10-22 returned 68 results; the relevant [`Julian/generatingfunctionology.lean`](https://github.com/Julian/generatingfunctionology.lean) was cloned and contained only two Lean files/277 lines, with three actual `sorry`s in `Chapter1.lean`, at [`6d1998e`](https://github.com/Julian/generatingfunctionology.lean/commit/6d1998e1de117018ba9ad475c801e55b4751272b). Lean Pool path search found no `wilf`; only three unrelated `generatingfunction` paths. No named ATLAS/ReasBook/Prove2Me collection was found. | **High within the searched sources**; no claim about every private or unindexed project. |
| **Petkovšek–Wilf–Zeilberger, _A=B_** | Web query `Lean "A=B" Wilf Zeilberger formalization` on 2026-10-21 found WZ-LLM, whose paper evaluates 100 classic identities and reports 34% success, not whole-book coverage. [WZ-LLM](https://arxiv.org/html/2605.04472v1). GitHub HTML repository query `Petkovsek Wilf Zeilberger Lean` on 2026-10-22 returned [0 results](https://github.com/search?q=Petkovsek+Wilf+Zeilberger+Lean&type=repositories). Formal-conjectures path checks for `Petkovsek`/`Zeilberger`/`Gosper` were zero. No named ATLAS/ReasBook/Prove2Me collection was found. | **Medium**; GitHub code/README aliases and individual missions are not exhaustively excluded. |
| **Graham–Knuth–Patashnik, _Concrete Mathematics_** | Web query `Lean "Concrete Mathematics" formalization book` on 2026-10-21 found a Lean Pool entry for one density-one GKP divisibility result, not a book project. [Lean Pool index](https://arxiv.org/html/2609.25199v1). GitHub HTML query `"Concrete Mathematics" Lean formalization` on 2026-10-22 returned [0 repository results](https://github.com/search?q=%22Concrete+Mathematics%22+Lean+formalization&type=repositories). Current Lean Pool path search had no `concrete-mathematics` or `concrete_mathematics`; formal-conjectures had no `Concrete` path. No named ATLAS/ReasBook/Prove2Me collection was found. | **Medium**; individual theorems certainly exist and source attribution need not appear in paths. |

#### Mechanical registry checks that supplement—not replace—semantic review

- **[H]** Mathlib `master` recursive tree on 2026-10-22 contained 9,252 `.lean` paths. It included 9 `KanExtension` paths, 16 `Monad/` paths, 12 `Coherence` paths, 40 `PowerSeries` paths, and 29 `Asymptotics` paths. It had zero paths containing `Gosper`, `Zeilberger`, or `SingularityAnalysis`, and two hypergeometric paths. This is evidence about filenames, not a proof that no declaration elsewhere implements those ideas. [Mathlib tree API](https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master?recursive=1).
- **[H]** Lean Pool's live recursive tree contained 25,038 entries and was not truncated. Candidate path searches found no `riehl`, `wilf`, `concrete-mathematics`, `cauchy-schwarz`, `aeqb`, or `a_eq_b`; `martingale` appeared only in four unrelated project paths. Again, a project may cite a book without using its title in the path. [Lean Pool tree API](https://api.github.com/repos/Vilin97/lean-pool/git/trees/main?recursive=1).
- **[H]** `ordinaryHypergeometric` in Mathlib defines and analyzes the ordinary/Gaussian hypergeometric function, but its documentation does not claim to verify Gosper/Zeilberger algorithms. [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.html).

#### Limits that must accompany negative evidence

- **Indexing limits:** private, new, renamed, forked, or poorly described repositories may be invisible; GitHub repository search is not exhaustive code search.
- **Naming limits:** authors use initials, translations, shortened titles, and project names that do not mention the book. Path checks cannot see all source citations.
- **Version limits:** default branches change; version branches may hold the real code. ReasBook explicitly keeps mathematical source off `main`. [ReasBook architecture](https://github.com/optpku/ReasBook).
- **Semantic limits:** no filename match does not prove no theorem or algorithm exists under another name. Mathlib and Lean Pool checks above are leads for manual API review, not absolute absence proofs.
- **Access limits:** Prove2Me's mission API returned 401, so the public collection list does not exclude an individual candidate mission. GitHub API repository searches for *Concrete Mathematics*, *The Cauchy–Schwarz Master Class*, and *Probability with Martingales* later hit HTTP 403 rate limits; those failures are not treated as null results.
- **Time limits:** Lean Pool grew from 211 projects in its September paper to 289 in the live repository checked here. Any negative older than a few weeks needs revalidation in the current environment. [Paper](https://arxiv.org/html/2609.25199v1); [live repository](https://github.com/Vilin97/lean-pool).
- **Training-knowledge limit:** historical memories of “no such project” were never used as completion evidence. Every positive completion claim above has a current primary URL; uncertain negatives are explicitly bounded.

### Inferences

- The preferred wording for a candidate is: **“No complete or near-complete Lean 4 formalization found in the documented search; named partial projects are X/Y/Z; confidence medium-high; recheck before launch.”** Avoid the unqualified sentence “not already done.”
- A null result becomes stronger when several independent inventory types agree and relevant partial repositories are actually opened. Riehl and Wilf satisfy that stronger pattern; A=B and Concrete Mathematics have good but still more limited negative evidence.
- Completion requires a reproducible artifact: source-node ledger + pinned build + transitive axiom report + fidelity review. Anything less should receive a weaker label such as “main-text target-complete,” “near-complete,” “selected library,” or “statement skeleton.”

### Gaps

- No global code search across every GitHub repository, every Zulip message, or every proof-assistant package was completed. The query log is deliberately finite and reproducible.
- Individual Prove2Me missions and source citations inside all Lean Pool projects were not exhaustively searched; collection/path searches can miss them.
- The audit did not independently compile external projects or compare every formal statement against every printed source statement. Those remain mandatory before certifying any candidate as disqualified or any existing project as strict-complete.

## Are there cross-domain candidate books with unusually strong evidence of value and feasibility?

### Takeaway

The best balance found is **Wilf's _generatingfunctionology_**: a bounded, canonical, cross-domain text with good power-series infrastructure and only a tiny existing Lean companion. **Riehl's _Category Theory in Context_** is a larger but realistic next project, with excellent monad/Kan-extension support and several partial companions to reuse rather than duplicate. **_A=B_** is a high-value, higher-risk algorithm-verification project. **_Concrete Mathematics_** is valuable but belongs in a multi-year later tranche, not the next single-book slot.

Node ranges below are analyst estimates against the brief's PMA ≈330-node yardstick, not publisher counts. They include main-text definitions/theorems and flag where examples/exercises would materially enlarge scope.

### Cited Findings

#### 1. Herbert S. Wilf, _generatingfunctionology_ — strongest right-sized candidate

- **Canonical source and scope [H].** Use the third edition if access and licensing permit; the publisher lists 256 pages and five main parts—introductory ideas/examples, series, cards/decks/hands and the exponential formula, applications, analytic/asymptotic models—plus a Maple/Mathematica appendix. [Routledge, third edition](https://www.routledge.com/generatingfunctionology/Wilf/p/book/9781568812793). Wilf also offers the second edition for educational download, which gives a concrete fallback edition but requires an edition-difference inventory. [Author's download page](https://www.math.upenn.edu/~wilf/DownldGF.html).
- **Estimated scope [M, analyst estimate].** Approximately **120–220 main-text nodes**, a genuine single-book project smaller than PMA's ≈330-node calibration before deciding how many examples/exercises to include. The appendix and exercise policy must be fixed before a precise ledger exists.
- **Not-already-done evidence [H within bounded search].** The only relevant repository found and inspected was two files/277 lines with three `sorry`s, not a near-complete book. [Julian repository](https://github.com/Julian/generatingfunctionology.lean); [commit inspected](https://github.com/Julian/generatingfunctionology.lean/commit/6d1998e1de117018ba9ad475c801e55b4751272b). A 2024 UW talk concerns examples from the book, not complete coverage. [UW talk](https://math.washington.edu/events/2024-05-20/generating-functions-lean). No matching ATLAS/ReasBook/Prove2Me collection or Lean Pool book project was found in the logged searches.
- **Mathlib readiness [H].** Current Mathlib has 40 `PowerSeries` paths, including derivative, inverse, logarithm, exponential, Catalan, evaluation, multivariate series, and restricted/topological variants. [Mathlib tree](https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master?recursive=1); [well-known series documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PowerSeries/WellKnown.html). Stirling numbers and asymptotic relations also exist. [Stirling](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Stirling.html); [asymptotics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Basic.html).
- **Reusable adjacent work [H].** Grinberg's formalization supplies extensive formal-power-series, infinite-product, partition, q-series, and symmetric-function material, but it is a different book and does not cover Wilf's source order or its analytic/asymptotic programme. [Grinberg repository](https://github.com/facebookresearch/algebraic-combinatorics).
- **Biggest gaps and risks [M, evidence-based inference].** The exponential formula's combinatorial-species interface, analytic asymptotics/darboux and singularity-analysis methods, and numerous worked examples are the likely hard boundary. The Mathlib tree had no `SingularityAnalysis` path, but that is not proof of semantic absence and needs an API-level pilot. The Maple/Mathematica appendix and second/third edition differences are explicit scope risks.
- **Value and verdict [M].** Generating functions connect combinatorics, probability, statistics, Markov chains, and number theory, as the publisher's own description notes. The project would produce reusable enumeration infrastructure rather than another elementary-analysis companion. **Recommend first**, conditional on a short pilot of the exponential formula and one analytic-asymptotic chapter.

#### 2. Emily Riehl, _Category Theory in Context_ — strongest larger single-book candidate

- **Canonical source and scope [H].** The author's freely available text has six chapters—categories/functors/natural transformations; universal properties/representability/Yoneda; limits/colimits; adjunctions; monads and their algebras; Kan extensions—plus an epilogue on coherence, Grothendieck toposes, and abelian-category embeddings, totaling about 233 pages. [Author's PDF and table of contents](https://emilyriehl.github.io/files/context.pdf). Its preface describes use in courses and its cross-disciplinary examples; calling it a standard graduate introduction is an analyst assessment, not a usage statistic.
- **Estimated scope [M, analyst estimate].** Approximately **250–400 main-text nodes**, with additional examples and exercises. Effort is **large single-book to multi-year**, depending on the epilogue and the treatment of domain-specific examples.
- **Not-already-done evidence [H within bounded search].** Three relevant companions were found and are all partial: Chapter 1 §§1–4 in an inactive companion; an exercise repository; and selected parts of Chapters 1–4 with intentional `sorry`s. [rkirov](https://github.com/rkirov/category-theory-in-context-lean); [masak](https://github.com/masak/category-theory-in-context); [gaxiiiiiiiiiiii/Riehl](https://github.com/gaxiiiiiiiiiiii/Riehl). Lean Pool has factorization systems from the book, not the whole book. [Lean Pool index](https://arxiv.org/html/2609.25199v1).
- **Important overlap [H].** Leinster's *Basic Category Theory* now has a comprehensive Lean companion, so the first four Riehl chapters have substantial conceptual overlap even though the books are not identical. [Leinster project](https://github.com/whoiam1101/basic-category-theory-lean4). The new value is therefore concentrated in Riehl's source-specific examples, Chapter 5 monads, Chapter 6 Kan extensions, and the epilogue.
- **Mathlib readiness [H].** Mathlib has monads and multiple Beck/reflexive monadicity theorems. [Monad basics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Basic.html); [monadicity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Monadicity.html). It has left/right Kan extensions and pointwise-related modules. [Kan extension basics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html); [pointwise source](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/CategoryTheory/Functor/KanExtension/Pointwise.lean). The tree also includes monoidal/bicategory coherence modules. [Mathlib tree](https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master?recursive=1).
- **Biggest gaps and risks [M, evidence-based inference].** The main risks are exact monadicity variants, pointwise Kan-extension formulas, derived functors, size/universe management, the epilogue's topos/abelian-category results, and faithful treatment of examples drawn from algebra, topology, and analysis. Existing partial companions are reusable starts but not evidence of full coverage.
- **Value and verdict [M].** This offers broad downstream value across algebra, topology, geometry, logic, and computer science and is more distinct from the excluded analysis pipeline than another real-analysis text. **Recommend second**, after explicitly carving out what the Leinster project already supplies.

#### 3. Marko Petkovšek, Herbert Wilf, Doron Zeilberger, _A=B_ — high-risk, high-differentiation candidate

- **Canonical source and scope [H].** The publisher lists 230 pages and nine chapters: proof machines; tightening the target; the hypergeometric database; Sister Celine's method; Gosper's algorithm; Zeilberger's algorithm; the WZ phenomenon; Algorithm Hyper; and an operator-algebra epilogue. [Routledge](https://www.routledge.com/A-B/Petkovsek-Wilf-Zeilberger/p/book/9781568810638). The authors' official page offers the whole book and describes its focus on computer discovery and proof of hypergeometric identities. [Authors' page](https://www.math.upenn.edu/~wilf/AeqB.html).
- **Estimated scope [M, analyst estimate].** Approximately **120–220 main-text nodes**, but effort is **large single-book to multi-year** because correctness of algorithms and certificate-producing procedures is harder than reproducing a sequence of ordinary textbook theorems.
- **Not-already-done evidence [M within bounded search].** No book repository was returned by the logged GitHub repository query, and no named ATLAS/ReasBook/Prove2Me collection was found. WZ-LLM evaluates a neuro-symbolic framework on 100 classical identities and reports 34% proof success; it does not formalize the book's nine chapters or its complete algorithm theory. [WZ-LLM paper](https://arxiv.org/html/2605.04472v1). This negative is weaker than for Wilf because alternate repository names and individual missions remain possible.
- **Mathlib readiness [H/M].** Mathlib has ordinary and regularized hypergeometric functions, with series definitions, termination, and convergence results. [Ordinary hypergeometric documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.html). The current tree has zero `Gosper` and zero `Zeilberger` paths; that suggests a pilot is necessary but does not prove the absence of relevant declarations under other names. [Mathlib tree](https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master?recursive=1).
- **Biggest gaps and risks [M, evidence-based inference].** Hypergeometric-term representations, recurrence/creative-telescoping infrastructure, algorithm termination, proof-certificate semantics, the hypergeometric database, q-analogues, and the boundary between executable computation and kernel-checked proof are the hard parts. A collection of proved identities would not satisfy the book's algorithmic content.
- **Value and verdict [M].** This is unusually aligned with verified computation and automated theorem proving rather than duplicating elementary analysis. **Recommend as a staged, high-risk pilot**, beginning with Gosper's algorithm and the WZ certificate semantics before committing to all nine chapters.

#### 4. Graham, Knuth, Patashnik, _Concrete Mathematics_, 2nd ed. — excellent but multi-year stretch

- **Canonical source and scope [H].** Knuth's page lists xiii+657 pages, nine major areas (sums, recurrences, integer functions, elementary number theory, binomial coefficients, special numbers, generating functions, discrete probability, asymptotic methods), more than 500 answered exercises, and use in Knuth's Stanford course from 1970–1989. It also documents later print corrections, including mechanical summation material. [Author's book page](https://www-cs-faculty.stanford.edu/~knuth/gkp.html).
- **Estimated scope [M, analyst estimate].** Approximately **400–650 main-text nodes**; including exercises and their answers could push the inventory well beyond 1,000 obligations. This is **multi-year**, not a PMA-sized single-book project.
- **Not-already-done evidence [M within bounded search].** The searches found one Lean Pool result sourced to the book, not a book formalization; no dedicated repository was returned by the logged GitHub repository query. [Lean Pool index](https://arxiv.org/html/2609.25199v1); [bounded GitHub null result](https://github.com/search?q=%22Concrete+Mathematics%22+Lean+formalization&type=repositories). Individual results in Mathlib are expected and are not coverage evidence.
- **Mathlib readiness [H].** Stirling numbers, Bernoulli numbers, asymptotic relations, power series, finite sums, and substantial discrete probability infrastructure exist. [Stirling](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Enumerative/Stirling.html); [Bernoulli](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bernoulli.html); [asymptotics](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Asymptotics/Basic.html); [power series](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PowerSeries/WellKnown.html).
- **Biggest gaps and risks [M, evidence-based inference].** Mechanical summation/Gosper–Zeilberger algorithms, special-number identities, analytic asymptotics, the sheer breadth of the nine areas, and the exercise/answer inventory dominate. The zero `Gosper`/`Zeilberger` filename matches are only pilot leads, not definitive semantic gaps. [Mathlib tree](https://api.github.com/repos/leanprover-community/mathlib4/git/trees/master?recursive=1).
- **Value and verdict [M].** Canonical status and downstream value are unusually strong, but size and breadth make this a poor next single-book project. **Defer to a multi-year tranche**, potentially after Wilf and A=B have built the relevant generating-function and algorithmic infrastructure.

#### Candidate comparison

| Rank | Book | Estimated main-text nodes / effort | Not-already-done confidence | Principal feasibility risk | Recommendation |
|---|---|---|---|---|---|
| 1 | Wilf, _generatingfunctionology_ | 120–220 / single-book | High within documented search | Exponential formula and analytic asymptotics | Best immediate candidate; pilot two hard nodes first |
| 2 | Riehl, _Category Theory in Context_ | 250–400 / large single-book to multi-year | Medium-high | Kan/derived-functor/epilogue scope and Leinster overlap | Strong second; reuse partial companions |
| 3 | Petkovšek–Wilf–Zeilberger, _A=B_ | 120–220 / large single-book to multi-year | Medium | Verified algorithms and certificates, not just identities | High-risk staged pilot |
| 4 | Graham–Knuth–Patashnik, _Concrete Mathematics_ | 400–650 main; 1,000+ with exercises / multi-year | Medium | Breadth, mechanical summation, asymptotics, exercise inventory | Defer; do not underscope |

### Inferences

- Wilf offers the cleanest “new value per unit of missing infrastructure” ratio: modest size, cross-domain payoff, meaningful gaps despite substantial power-series support, and no large existing companion found.
- Riehl should not be sold as untouched category theory. Its justification is the remaining source-specific monad/Kan/epilogue programme and the value of a coherent book-order development on top of existing category theory and the Leinster companion.
- A=B is strategically attractive precisely because it tests a different capability from ordinary proof transcription. If the programme only wants theorem-by-theorem coverage, its algorithmic obligations could become a scope trap; if verified algorithms are welcome, it is unusually valuable.
- Concrete Mathematics should not be squeezed into a false small-project estimate. Its canonical status makes it worth doing eventually, but Wilf and A=B are sensible prerequisite investments.

### Gaps

- The node ranges are estimates, not source censuses. A final decision requires a chapter-by-chapter ledger for the selected edition, including an explicit examples/exercises/appendices policy.
- Other-proof-assistant searches for these four candidates were not exhaustive. No complete Coq/Isabelle/HOL/Agda version was identified in the documented searches, but that is an **unverified negative**, especially for A=B's algorithmic literature.
- Prove2Me individual-mission absence is unresolved because the API required authentication; only named collections were ruled out.
- *The Cauchy–Schwarz Master Class*, *Probability with Martingales*, and *Geometry Revisited* remain possible leads, but they are not recommended here because their not-already-done and scope checks were incomplete. In particular, GitHub API rate limits prevented the same strength of negative evidence obtained for the four candidates above.
- No licensing/access assessment for reproducing source text was performed. Wilf's second edition is explicitly available for educational download, Riehl's PDF is author-hosted, and A=B is author-host offered; that does not by itself settle the programme's preferred reproduction policy. [Wilf](https://www.math.upenn.edu/~wilf/DownldGF.html); [Riehl](https://emilyriehl.github.io/files/context.pdf); [A=B](https://www.math.upenn.edu/~wilf/AeqB.html).
