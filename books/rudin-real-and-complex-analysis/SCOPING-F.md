# Cluster F: independent printed inventory and pinned-library claims check

Authority: [issue #42](https://github.com/derekblair/formalize-everything/issues/42), [umbrella #36](https://github.com/derekblair/formalize-everything/issues/36).

This working branch establishes its own inventory from the printed third edition. It does not claim access to the separate research lanes’ inventories. Stage 2 coverage is reported independently in PROGRESS.md. Original scans, extraction, and build logs are held in the lane workdir `/home/derekblair/lane-work/codex-rca-f-proton/evidence/`; the scans and book proofs are not committed.


---

# Chapter 13 printed-node inventory — 2026-10-29

Scope: Walter Rudin, *Real and Complex Analysis*, third edition (1987), Chapter 13, printed pp. 266–276, excluding exercises. This is a fresh reading of the printed text, not an inherited Stage 1 inventory. No Mathlib coverage or Lean completion is asserted here.

## Source and method

- Primary mathematical source: [printed third-edition book PDF](https://absinthe.tuxfamily.net/openmathdep/analysis_complex/Real_and_Complex_Analysis-Rudin.pdf).
- Lane copy: `evidence/source-rudin.pdf`; SHA-256 `fde4a952137aaa406ffb1e3e35dfc99a2dada5c51b10d27eed71ad7bfa820358`.
- Text extraction: `evidence/source-rudin.txt`, generated with installed `pdftotext -layout`. Chapter text occupies approximately lines 14510–15112. PDF one-based page = printed page + 13 in this range.
- Chapter headings and all numbered blocks were read in sequence. The 13.11 statement was also visually verified in `evidence/ch13-p274.png`, rendered from PDF page 287; its final condition is labeled **(j)**, not (i).
- Independent readable mirror: [third-edition transcription](https://studylib.net/doc/28312702/real-and-complex-analysis), identifying third edition and 1987 on its title/copyright pages. The original PDF hostname currently presents a mismatched certificate; the public, unauthenticated download used `curl -k`. No credentials were involved.

## Count and issue discrepancy

There are **12 numbered nodes, 13.1–13.12**: **8 Theorem blocks**, **3 named exposition/definition blocks containing mathematical assertions**, and **1 Remark block containing a converse/necessity assertion**. Every numbered block is counted, including definitions and the remark; displayed equation numbers and exercises are not separate nodes.

Issue #42 calls Runge 13.10 and Mergelyan 13.12. In this edition:

- **13.6** is compact-set Runge approximation with prescribed poles; **13.7** its polynomial corollary; **13.9** the open-set Runge theorem.
- **13.10** is **Mittag-Leffler**, with prescribed principal parts.
- **13.12** is harmonicity of `log |f|` for a zero-free holomorphic function.
- **Mergelyan is 20.5, printed p. 390**, in Chapter 20. This was checked only to resolve the ticket discrepancy; it is outside the authorized Chapter 13–14 implementation scope.

## Complete inventory

Notation: `S² = ℂ ∪ {∞}` with the Riemann-sphere topology; `H(Ω)` means complex-valued holomorphic functions on the open set `Ω`; `U = {z : |z| < 1}`. A plane *region* means nonempty connected open set. Summaries below use mathematical notation and original paraphrase rather than copied book prose.

| Node | Printed page(s) | Printed kind | Mathematical content / required faithful scope |
|---|---:|---|---|
| **13.1** | 266–267 | Named exposition: Riemann sphere | Define `D′(∞;r)={z∈ℂ:|z|>r}`, `D(∞;r)=D′(∞;r)∪{∞}` for `r>0`; usual finite-centered discs together with these neighborhoods give the topology on `S²`, restricting to the plane topology. The map `φ(∞)=(0,0,1)`, `φ(z)=(2 Re(z)/(1+|z|²), 2 Im(z)/(1+|z|²), (|z|²−1)/(1+|z|²))` is a homeomorphism to the unit sphere in `ℝ³`. Classify a singularity at infinity by `z↦f(1/z)` at zero. Boundedness of holomorphic `f` outside a disc gives a finite limit and holomorphic extension at infinity. A pole of order `m` there has a polynomial principal part of degree `m`; subtracting it removes the singularity. An entire nonpolynomial has an essential singularity at infinity. The horizontal strip `0<Im z<1` illustrates that connectedness of the spherical complement differs from connectedness of the planar complement. |
| **13.2** | 267 | Named exposition: rational functions | Rational `f=P/Q`, with polynomial numerator and nonzero denominator, admits cancellation to relatively prime numerator/denominator. Its finite poles are exactly denominator zeros, with matching multiplicities. If `a₁,…,aₖ` are those distinct zeros, there are polynomials `A₀,…,Aₖ` such that `Aⱼ(0)=0` for `j≥1` and `f(z)=A₀(z)+Σⱼ Aⱼ((z−aⱼ)⁻¹)` wherever finite values are defined. Subtracting all finite principal parts leaves the polynomial `A₀`. |
| **13.3** | 267–268 | Theorem | Every open `Ω⊆ℂ` has compact sets `Kₙ⊆Ω` (`n≥1`) whose union is `Ω`, with `(a) Kₙ⊆interior Kₙ₊₁`; `(b) ∀ compact K⊆Ω, ∃n, K⊆Kₙ`; `(c) every connected component of S²\Kₙ contains a connected component of S²\Ω`. No connectedness of `Ω` is required. |
| **13.4** | 268 | Named exposition: oriented intervals | A finite collection of directed line intervals is *balanced* when, at each vertex, the number starting there equals the number ending there. Its intervals can be ordered and partitioned into finitely many closed polygonal paths; their formal sum is a cycle. The assertion concerns the supplied intervals, preserving multiplicities, and is stronger than merely constructing some closed path. |
| **13.5** | 268–269 | Theorem | For compact `K⊆Ω`, with `Ω⊆ℂ` nonempty open, there exists one cycle `Γ` supported in `Ω\K` satisfying `f(z)=(2πi)⁻¹∫Γ f(ζ)/(ζ−z) dζ` simultaneously for all `f∈H(Ω)` and `z∈K`. Its proof constructs a polygonal cycle with index `1` on `K` and `0` outside `Ω`. |
| **13.6** | 270–271 | Theorem | Given compact `K⊆ℂ`, prescribed points `A⊆S²\K` selecting a point in each connected component of that complement, open `Ω⊇K`, `f∈H(Ω)`, and `ε>0`, there exists a rational function `R` whose spherical poles all lie in `A`, with `∀z∈K, |f(z)−R(z)|<ε`. Infinity is an admissible prescribed pole. The compact complement has at most countably many components. |
| **13.7** | 271 | Theorem | If compact `K⊆ℂ` has connected `S²\K`, and `f` is holomorphic on an open neighborhood of `K`, a sequence of complex polynomials converges uniformly to `f` on `K`. No connectedness of `K` is required. |
| **13.8** | 271–272 | Remark with proof | If compact `K⊆ℂ` has disconnected spherical complement, choose a bounded complementary component `V` and `α∈V`. The holomorphic-near-`K` function `f(z)=(z−α)⁻¹` cannot be uniformly approximated by polynomials on `K`. Quantitatively, for `m=max_{z∈K}|z−α|>0`, no polynomial has pointwise error `<1/m` throughout `K`; otherwise the maximum principle applied to `(z−α)P(z)−1` contradicts its value at `α`. The prescribed representative in each component in 13.6 is likewise necessary for approximation of all functions. |
| **13.9** | 272 | Theorem | For arbitrary open `Ω⊆ℂ`, a pole set `A⊆S²\Ω` selecting a point from each connected component, and `f∈H(Ω)`, there exists a sequence of rational functions `Rₙ`, all with poles in `A`, converging uniformly to `f` on every compact subset of `Ω`. If `S²\Ω` is connected, `A={∞}` gives a polynomial sequence. Neither `Ω` nor the compact sets in the convergence statement are assumed connected; the open-set complement may have uncountably many components. |
| **13.10** | 273–274 | Theorem | Let `Ω⊆ℂ` be open and `A⊆Ω` have no accumulation point in `Ω`. For each `α∈A`, prescribe an integer `m(α)>0` and a principal-part expression `Pα(z)=Σ_{j=1}^{m(α)} c_{j,α}(z−α)^(−j)`. There is a meromorphic function on `Ω` whose principal part at every `α` is `Pα` and which has no poles elsewhere in `Ω`. Zero principal parts are allowed by the literal hypotheses; do not strengthen the conclusion to a pole at every `α` without a nonzero coefficient assumption. |
| **13.11** | 274–275 | Theorem | For a plane region `Ω`, nine conditions are equivalent: **(a)** `Ω` is homeomorphic to `U`; **(b)** `Ω` is simply connected; **(c)** every closed path in `Ω` has index zero at every point of `S²\Ω`; **(d)** `S²\Ω` is connected; **(e)** every holomorphic function on `Ω` is a compactwise uniform limit of polynomials; **(f)** every holomorphic function has integral zero over every closed path in `Ω`; **(g)** every holomorphic function on `Ω` has a holomorphic primitive there; **(h)** every zero-free holomorphic function on `Ω` has a holomorphic logarithm there; **(j)** every zero-free holomorphic function on `Ω` has a holomorphic square root there. The book prints the reciprocal-holomorphic condition in (h)/(j); its mathematical meaning includes that the reciprocal is defined, hence zero-freeness. |
| **13.12** | 276 | Theorem | For any open `Ω⊆ℂ` and `f∈H(Ω)` satisfying `∀z∈Ω, f(z)≠0`, the real-valued function `z↦log |f(z)|` is harmonic throughout `Ω`. Neither connectedness nor simple connectedness is assumed. |

## Dependency and formalization cautions

1. The printed proof chain is 13.3 and 13.4 → 13.5 → 13.6 → 13.7/13.8 and 13.9 → 13.10 and 13.11; 13.12 uses local holomorphic logarithms from 13.11(h). Definitions and prior-chapter tools are also dependencies.
2. The final implication **13.11(j) → 13.11(a)** explicitly invokes **14.8**, as printed on p. 275. Hence “first chapter first” cannot mean proving the entire book proof chain without arranging this forward dependency. A foundational result may be proved independently and reused, or the corresponding direction can await Chapter 14; it must not be silently assumed.
3. In Lean, totalized field inverse means `DifferentiableOn ℂ (fun z => (f z)⁻¹) Ω` alone does not express Rudin's zero-free reciprocal hypothesis. Use explicit `∀z∈Ω, f z≠0` where needed.
4. Rational identities and principal-part equalities apply off poles or as meromorphic identities. A totalized rational evaluation at denominator zero is not a faithful replacement for a pole.
5. 13.3(c), 13.6, 13.8, 13.9, and 13.11(c)/(d) use complements in **the sphere**, not interchangeable planar complements. In particular, the strip example in 13.1 makes that distinction explicit.
6. Definitions/exposition 13.1, 13.2, 13.4 and the proved remark 13.8 remain part of the 12-node scope; proving one incidental assertion does not discharge a whole numbered block.


---

# Printed inventory: RCA Chapter 14, Conformal Mapping

Checked 2026-10-29 against Walter Rudin, *Real and Complex Analysis*, third edition, McGraw-Hill, 1987. This is an independently produced printed-text inventory, not a claim to possess the programme's separate Stage 1 inventory. No Lean implementation or Mathlib-coverage claim is made here.

## Evidence

- Primary mathematical source: the printed book in [this third-edition scan](https://absinthe.tuxfamily.net/openmathdep/analysis_complex/Real_and_Complex_Analysis-Rudin.pdf).
- Local scan: `evidence/rudin-rca-third-edition-ch14-source.pdf`; SHA-256 `fde4a952137aaa406ffb1e3e35dfc99a2dada5c51b10d27eed71ad7bfa820358`; 430 PDF pages. The certificate hostname does not match the host; retrieval used `curl -k` for this public, unauthenticated file. A separate agent independently retrieved the same bytes as `evidence/source-rudin.pdf`.
- Local extraction: `evidence/rudin-rca-third-edition-ch14-source.txt` (`pdftotext -layout`). Relevant printed pages are 278-293, corresponding to one-based PDF pages 291-306. Text extraction was supplemented by rendered inspection of printed pp. 281, 285, 286, and 289, saved as `evidence/ch14-p281.png`, `evidence/ch14-p285.png`, `evidence/ch14-p286.png`, and `evidence/ch14-p289.png`.
- Scope authority read in full: [cluster F issue #42](https://github.com/derekblair/formalize-everything/issues/42) and [umbrella issue #36](https://github.com/derekblair/formalize-everything/issues/36).

## Count and ticket comparison

**22 numbered nodes, 14.1 through 14.22 inclusive.** Classification by printed heading: 10 Theorems, 4 Definitions, 2 Examples/Example, 2 Remarks, and 4 other numbered discussions (including the explicitly titled Conformal Equivalence discussion). The unnumbered corollary immediately following 14.13 is included with 14.13, not counted as an additional numbered node. Exercises start on p. 293 and are excluded.

The ticket's **Riemann mapping theorem = 14.8 is correct**, on p. 283. Chapter 14 does not contain a separately numbered corner theorem. Its boundary material is 14.16-14.20, and its final numbered theorem is the annulus classification 14.22. The ticket's mention of Mergelyan is not a Chapter 14 theorem: p. 285 explicitly describes 14.15 as an ingredient for Mergelyan's theorem in Chapter 20. Chapter 13's mistaken headline numbering is recorded by the Chapter 13 inventory agent.

## Conventions needed for faithful formal statements

Write `U = {z : C | norm z < 1}`, `T = {z : C | norm z = 1}`, and `H(Omega)` for complex-valued holomorphic functions on the open set `Omega`. A region is nonempty, open, and connected. Every function equality or derivative claim is restricted to the indicated domain; the book's notation suppresses such restrictions. `S^2` denotes the Riemann sphere, including infinity.

The table specifies mathematical facts in fresh notation; it does not transcribe the book's prose or proofs. Rows that contain multiple subclaims remain one printed node, but all those subclaims must remain visible in a Stage 2 coverage report.

| Node | Printed page(s) | Printed kind | Mathematical content and statement obligations |
|---|---:|---|---|
| 14.1 | 278 | Definition | For nonzero `z`, set `A(z)=z/norm z`. Suppose `z0` belongs to a region `Omega`, and some deleted disc around `z0` is contained in `Omega` and has `f(z) != f(z0)`. Angle preservation means that `lim_(r -> 0+) exp(-i theta) A(f(z0+r exp(i theta))-f(z0))` exists and has the same value for every real `theta`. The accompanying global characterization is that a holomorphic function preserves angles everywhere exactly when its derivative is everywhere nonzero, with the local statements addressed in 14.2. |
| 14.2 | 278-279 | Theorem | If the complex derivative `f'(z0)` exists and is nonzero, `f` preserves angles at `z0`. Conversely, a nonzero real Frechet differential at `z0`, together with angle preservation there, implies existence and nonvanishing of the complex derivative. The real differential is a real-linear map `L : R^2 -> R^2`, with error `o(norm h)`. The following note also asserts that a holomorphic function with zero derivative cannot preserve angles at that point, while `f(z)=norm z * z` preserves angles at zero despite zero real differential. |
| 14.3 | 279-281 | Numbered discussion / definitions and claims | For `a*d-b*c != 0`, `M(z)=(a*z+b)/(c*z+d)` defines a bijection of the Riemann sphere with the pole/infinity values understood. It is a composition of translations, rotations, positive real dilations, and inversion. It preserves generalized circles (ordinary circles and straight lines with infinity). A generalized circle has equation `alpha*z*conj z + beta*z + conj beta*conj z + gamma = 0`, where `alpha,gamma` are real and `norm beta^2 > alpha*gamma`. For any two ordered triples of distinct sphere points, there is exactly one such `M` carrying one triple to the other; for finite distinct `a,b,c`, `(b-c)*(z-a)/((b-a)*(z-c))` carries `(a,b,c)` to `(0,1,infinity)`. Consequences: any circle can map to any circle or line, and any open disc is conformally equivalent to any open half-plane. Explicit Cayley map `(1+z)/(1-z)` bijects `U` with `{w | Re w > 0}` and carries `(-1,0,1)` to `(0,1,infinity)`. The stereographic-circle characterization is stated but its proof is expressly omitted. |
| 14.4 | 281 | Numbered discussion / circular reflection | For a region `Omega` inside `U` having a unit-circle boundary arc `L`, and `f` continuous on its closure, holomorphic inside, and real on `L`, Schwarz reflection across `L` gives a holomorphic extension satisfying `F(z)=conj(f(1/conj z))` on the reflected side. The proof transfers reflection in the real axis through `psi(z)=(z-i)/(z+i)`, which maps the upper half-plane to `U` and satisfies `psi(conj z)=1/conj(psi(z))` where finite expressions are defined. The printed geometric setup is informal; a formal theorem must specify an open reflected neighborhood of the arc and the relevant nonzero-domain conditions, rather than claim extension across arbitrary other boundary points. |
| 14.5 | 281-282 | Definition | A family `F subset H(Omega)` is normal when every sequence in `F` admits a subsequence converging uniformly on every compact subset of `Omega`; the finite holomorphic limit need not belong to `F`. The alternate meromorphic convention allowing convergence to infinity is mentioned but is not the convention adopted here. |
| 14.6 | 282 | Theorem | If `F subset H(Omega)` and, for each compact `K subset Omega`, one finite constant bounds `norm(f(z))` for every `f in F` and `z in K`, then `F` is normal in the finite-valued sense of 14.5. This is the locally bounded-family normality theorem (Montel). |
| 14.7 | 282-283 | Conformal Equivalence | Regions `Omega1,Omega2` are conformally equivalent when a holomorphic bijection `phi : Omega1 -> Omega2` exists. Its inverse is holomorphic, and the regions are homeomorphic. Pullback `f -> f compose phi` is a bijection `H(Omega2) -> H(Omega1)` preserving addition and multiplication. |
| 14.8 | 283-284 | Theorem | Every simply connected region `Omega` properly contained in the complex plane admits a holomorphic bijection onto `U`. The whole plane is excluded; it is homeomorphic to `U` but is not conformally equivalent to it, by Liouville. The proof only needs that every zero-free member of `H(Omega)` has a holomorphic square root, and so also supplies the pending implication 13.11(j) -> 13.11(a). |
| 14.9 | 285 | Remarks | Fix `z0 in Omega` and choose the extremal map `h : Omega -> U` from the proof of 14.8. It satisfies `h(z0)=0`. For every holomorphic `f : Omega -> U`, including noninjective ones, `norm(f'(z0)) <= norm(h'(z0))`. Equality holds exactly when `f=lambda*h` throughout `Omega` for a constant `lambda` with `norm lambda=1`. The base point is the fixed one used to normalize `h`; the statement must not be read as holding at arbitrary other points for a single normalization. |
| 14.10 | 285 | Definition | `S` consists of all injective holomorphic `f : U -> C` with `f(0)=0` and `f'(0)=1`. Every such `f` has expansion `f(z)=z+sum_(n>=2) a_n*z^n` throughout `U`. `S` is neither addition-closed nor multiplication-closed. |
| 14.11 | 285 | Example | For every complex `alpha` with `norm alpha <= 1`, the function `f_alpha(z)=z/(1-alpha*z)^2` belongs to `S`, and has expansion `sum_(n>=1) n*alpha^(n-1)*z^n` on `U`. For `norm alpha=1`, these are Koebe functions. The request to determine all image regions is explicitly left as an exercise and is excluded. |
| 14.12 | 285-286 | Theorem | (a) If `f in S` and `norm alpha=1`, then `g(z)=conj alpha * f(alpha*z)` belongs to `S`. (b) For each `f in S`, there exists `g in S` satisfying `g(z)^2=f(z^2)` for every `z in U`. The proof constructs an odd normalized square root via `f(z)=z*phi(z)`, `h^2=phi`, `h(0)=1`, and `g(z)=z*h(z^2)`. |
| 14.13 | 286-287 | Theorem (area theorem); unnumbered Corollary | Let `F` be holomorphic and injective on the punctured unit disc, with Laurent expansion `F(z)=1/z+sum_(n>=0) a_n*z^n`, convergent there, and pole value `F(0)=infinity` understood when discussing the whole disc. Then `sum_(n>=1) n*norm(a_n)^2 <= 1`. The following unnumbered corollary gives `norm(a_1) <= 1`, and the sharp examples `F(z)=1/z+alpha*z` are injective for `norm alpha <= 1`. A Lean formulation needs summability or a nonnegative extended-real sum/finite-partial-sum formulation; an unguarded `tsum` on an unproved nonsummable series is inadequate. |
| 14.14 | 288 | Theorem | If `f in S` has expansion `f(z)=z+sum_(n>=2) a_n*z^n`, then (a) `norm(a_2) <= 2`, and (b) the open radius-`1/4` disc centered at zero is contained in `f(U)`. Both constants are sharp, witnessed by 14.11. The accompanying contrast constructs, for each `alpha != 0`, an entire function `alpha*(1-exp(-z/alpha))` with value zero and derivative one at zero which omits `alpha`; if `norm alpha < 1/4`, such a function cannot be injective on `U`. |
| 14.15 | 288-289 | Theorem | If `F` is injective and holomorphic on `U minus {0}`, has a simple pole at zero of residue one, and omits complex values `w1,w2`, then `norm(w1-w2) <= 4`. The meromorphic value at zero is infinity, as in 14.13. Sharpness: `F(z)=1/z+z` omits exactly the real interval `[-2,2]` from its finite image. |
| 14.16 | 289 | Definition | For a simply connected region `Omega` and `beta in boundary Omega`, simplicity means: for every sequence `alpha_n in Omega` tending to `beta`, there is a continuous curve `gamma : [0,1] -> C` and a strictly increasing sequence `0<t_1<t_2<...` tending to `1`, with `gamma(t_n)=alpha_n` and `gamma(t) in Omega` for every `0<=t<1`. Continuity forces `gamma(1)=beta`. Passing to a subsequence of `alpha_n` is not permitted by this definition. |
| 14.17 | 289 | Examples | (i) `Omega=U minus [0,1)` is simply connected, and every real `beta` with `0<beta<=1` is a nonsimple boundary point. (ii) Start with the open square `{x+i*y | 0<x<1, 0<y<1}`. For every integer `n>=1`, remove the vertical closed segments from `1/(2*n)` to `1/(2*n)+((n-1)/n)*i`, and from `1/(2*n+1)+i/n` to `1/(2*n+1)+i`. The resulting region is simply connected, and each `i*y` with `0<=y<=1` is a nonsimple boundary point. |
| 14.18 | 289-290 | Theorem | Let `Omega` be a bounded simply connected region and `f : Omega -> U` a holomorphic bijection. (a) At each simple boundary point `beta`, `f` extends continuously to `Omega union {beta}`, and its new value has norm one. (b) The extension values at any two distinct simple boundary points are distinct. |
| 14.19 | 290-291 | Theorem | If `Omega` is a bounded simply connected region and every boundary point is simple, every holomorphic bijection `f : Omega -> U` extends to a homeomorphism `closure Omega -> closure U`. |
| 14.20 | 291 | Remarks | (a) Under 14.19's hypotheses the boundary is a Jordan curve and `closure Omega` is homeomorphic to the closed disc. The converse, that a Jordan boundary makes all boundary points simple, is stated but expressly not proved. (b) Given three distinct boundary points and three distinct target points on `T` in compatible cyclic order, there is a unique extension homeomorphism holomorphic in `Omega` with those three boundary values. (c) The conclusion and three-point normalization extend to simply connected regions in the Riemann sphere whose boundary points are simple and whose complement has nonempty interior; a half-plane may replace `U` as target. (d) Composing two such disc maps gives a holomorphic interior map extending to a homeomorphism between the two region closures. |
| 14.21 | 291-292 | Numbered discussion / annulus definition | Any two proper simply connected plane regions are conformally equivalent. For `0<r<R`, define `A(r,R)={z | r<norm z<R}`. Positive real dilation by `lambda` bijects `A(r,R)` holomorphically with `A(lambda*r,lambda*R)`. Therefore annuli with equal outer/inner radius ratios are conformally equivalent; the necessity is 14.22. |
| 14.22 | 292-293 | Theorem | For positive radii `r1<R1` and `r2<R2`, `A(r1,R1)` and `A(r2,R2)` are conformally equivalent if and only if `R1/r1=R2/r2`. The proof normalizes both inner radii to one, allows inversion to choose the boundary correspondence, obtains `f'(z)/f(z)=alpha/z` where `alpha=log R2/log R1`, and uses winding-number integrality and injectivity to deduce `alpha=1`. |

## Encoding cautions and unresolved checks

1. The scan really does print `F in H(U minus {0})` together with injectivity "in U" in 14.13 and 14.15. The proof calls `F(U_r)` a neighborhood of infinity. This is the meromorphic/sphere convention, not a license to use Lean's arbitrary zero value for division. Encode injectivity on the punctured disc and the pole explicitly, or provide a sphere-valued extension. The local formula need only be asserted at nonzero `z`.
2. 14.4 is expressly an informal reflection discussion. A formal domain hypothesis spelling out the boundary arc is a necessary explication and must be disclosed, rather than silently pretending the printed prose specifies a particular global extension domain.
3. 14.20(a)'s converse is a printed assertion without a book proof. It remains within the numbered-node coverage obligation. No assumption that it is automatic should be made.
4. This inventory identifies no false numbered theorem. It does not certify all informal remarks as independently proved. Axioms audits, Mathlib matching, clean builds, and Lean proof status are separate evidence.


---

# Pinned Mathlib claims check: RCA Chapters 13–14

Checked 2026-10-29 against the actual checkout at
`formalize-everything/books/rudin-real-and-complex-analysis/.lake/packages/mathlib`.
`git rev-parse HEAD` returned **d13f23b723b8a846827a245b89c10fc7d3f11612**.
The project toolchain is **leanprover/lean4:v4.34.1**. This is a source-level
claims audit, not a claim that any new book module has passed a build or axiom audit.
Printed scope is supplied by `inventory-ch13.md` and `inventory-ch14.md` in this directory:
**12 + 22 = 34 numbered nodes**. In particular Runge is 13.6/13.9,
13.10 is Mittag-Leffler, and 13.12 is harmonicity of log modulus.

## Classification and limits

- **Usable** means the mathematical assertion is already present in a usable
  theorem; routine domain restatement remains.
- **Partial** means relevant variants or parts exist, but the whole printed node
  is not supplied. The missing parts are named explicitly.
- **Missing** means no theorem proving the principal assertion was identified
  after searching the entire pinned source tree and reading the candidate files.
  It does not claim mathematical impossibility or absence from all other projects.

No row implies Stage 2 completion. Numbered definitions also carry the accompanying
printed assertions; a definition alone does not complete such a node.
Paths below are relative to `Mathlib/` at the verified pin. Exact source anchors
are supplied in the detailed evidence after the tables.

## Chapter 13: every numbered node

| Node | Status | Pinned source evidence and remaining obligation |
|---|---|---|
| 13.1 | Partial | `OnePoint ℂ`, its topology and compactness, and `onePointEquivSphereOfFinrankEq` give the sphere infrastructure. `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under` gives removability after inversion. `MeromorphicAt` and meromorphic order give a local singularity vocabulary. The exact printed stereographic coordinates, polynomial principal part at infinity, nonpolynomial-entire essential singularity, and strip-complement example still require proofs/restatement. |
| 13.2 | Partial | `RatFunc.num_div_denom`, `RatFunc.isCoprime_num_denom`, complex polynomial splitting, and `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` supply the algebraic ingredients. Must specialize to complex linear factors, package each principal part as a polynomial in `(z-a)⁻¹` with zero constant coefficient, identify pole orders, and restrict evaluation off poles. |
| 13.3 | Partial | `CompactExhaustion.choice`, `.subset_interior_succ`, and `.exists_superset_of_isCompact` supply (a),(b) for an appropriate open subtype. They do **not** supply (c), the spherical complement component condition. The book's explicit exhaustion or an equivalent construction remains needed. |
| 13.4 | Missing | `Combinatorics/SimpleGraph/Trails.lean` has undirected Eulerian-trail necessary conditions and explicitly lists the converse as a TODO. It does not give decomposition of a finite balanced directed multiset of intervals into cycles. |
| 13.5 | Missing | `Analysis/Complex/CauchyIntegral.lean` gives rectangle/circle Cauchy formulas, but not existence of one polygonal cycle in `Ω \\ K` serving all points of an arbitrary compact `K` and all holomorphic functions on `Ω`. |
| 13.6 | Missing | No Runge/rational-approximation theorem in the source search or candidate complex-analysis files. Prescribed spherical pole sets, compact approximation, and countability of complement components remain. |
| 13.7 | Missing | No complex-polynomial approximation on an arbitrary compact set with connected spherical complement was found. Real Stone–Weierstrass is not this assertion. |
| 13.8 | Missing | Maximum-modulus ingredients exist in `Analysis/Complex/AbsMax.lean`, but the bounded-complement obstruction and necessity of prescribed poles are not packaged/proved as this node. |
| 13.9 | Missing | Locally uniform convergence and `CompactExhaustion` exist. They do not prove existence of rational approximants with the prescribed poles. The Runge core and exhaustion condition remain. |
| 13.10 | Missing | `Analysis/Meromorphic/*` supplies meromorphic definitions and calculus, but no existence theorem with arbitrary discrete prescribed principal parts. `CategoryTheory/CofilteredSystem.lean` concerns a different Mittag-Leffler condition; `Trigonometric/Cotangent.lean` only a particular expansion. |
| 13.11 | Partial | `Analysis/Complex/BranchLogRoot.lean` gives continuous logarithm/root branches on simply connected open sets. `Analysis/Complex/HasPrimitives.lean` supplies local/convex primitive tools. The nine-way equivalence, spherical-complement equivalence, polynomial approximation direction, and disc homeomorphism direction are not one existing theorem. The printed final implication depends on 14.8. |
| 13.12 | Usable | `AnalyticAt.harmonicAt_log_norm` proves the pointwise assertion for a nonzero analytic function. On an open set, `DifferentiableOn.analyticOnNhd` converts the book hypothesis; apply the pointwise theorem at every domain point. |

## Chapter 14: every numbered node

| Node | Status | Pinned source evidence and remaining obligation |
|---|---|---|
| 14.1 | Partial | Standard derivatives, normalization of nonzero complex vectors, and conformality infrastructure exist. The book's oriented-angle limiting definition is not `ConformalAt`: Mathlib deliberately includes antiholomorphic conjugation. The exact definition and global characterization need a faithful encoding. |
| 14.2 | Partial | `DifferentiableAt.conformalAt` and the Cauchy–Riemann characterization are available, but the converse for book-oriented angles is not the existing unoriented conformality equivalence. The zero-derivative holomorphic exclusion and `|z|z` example remain. |
| 14.3 | Partial | Real-coefficient upper-half-plane Möbius action and projective-line/one-point equivalences exist; Euclidean inversion carries spheres through its center to hyperplanes. These are not a complete complex Riemann-sphere Möbius classification, generalized-circle preservation, unique three-point interpolation, or explicit Cayley-map package. |
| 14.4 | Missing | No Schwarz-reflection principle was found in the full-tree search. The circle version also requires a precise reflected-open-neighborhood/arc formulation. |
| 14.5 | Partial | `TendstoLocallyUniformlyOn` and its equivalence with uniform convergence on every compact subset exist. The finite-valued normal-family definition can be stated using them; the adoption of this convention and associated holomorphic-limit claim still need book declarations. |
| 14.6 | Missing | Arzelà–Ascoli and Cauchy estimates exist, but no Montel theorem for locally bounded holomorphic families was found. `Analysis/LocallyConvex/Montel.lean` concerns Montel topological vector spaces. |
| 14.7 | Partial | Open mapping and inverse-function theorem infrastructure exist. A holomorphic-bijection equivalence, holomorphic inverse, and pullback ring isomorphism require assembly; no exact book package found. |
| 14.8 | Missing | `Analysis/Complex/RiemannMapping.lean` expressly contains only partial results, with injective maps **into** the disc and no surjectivity. Its documentation points to unmerged PR 33505; that is outside the pinned dependency. The proper-domain Riemann mapping theorem is not supplied by this file. |
| 14.9 | Partial | `Analysis/Complex/Schwarz.lean` gives derivative bounds and affine equality cases on balls. Transport through the normalized conformal map remains, and its existence depends on 14.8. |
| 14.10 | Partial | Taylor expansion of holomorphic functions on discs exists in `Analysis/Complex/TaylorSeries.lean`; the normalized univalent class, its expansion restatement, and failure of algebra closure need declarations/proofs. |
| 14.11 | Missing | No Koebe/univalent-family theorem found. Rational differentiation and geometric-series tools are available but do not establish the full normalized injectivity and coefficient expansion claim. |
| 14.12 | Partial | Composition/rotation calculus and continuous square-root branches exist. They do not already prove membership of the rotated or odd square-root transforms in the normalized univalent class. |
| 14.13 | Missing | No univalent area theorem found. This also needs a faithful Laurent/pole formulation and a summability or nonnegative-series encoding, plus the sharp corollary. |
| 14.14 | Missing | No coefficient-two bound or Koebe quarter theorem found. The normalization and sharp examples are not a substitute for either inequality. |
| 14.15 | Missing | No omitted-value diameter bound for normalized simple-pole univalent functions found. |
| 14.16 | Missing | No matching simple-boundary-point predicate/sequence-interpolating-curve theorem found. Must encode the whole sequence, not an arbitrary subsequence. |
| 14.17 | Missing | No slit-disc/comb-domain boundary examples with the printed assertions found. |
| 14.18 | Missing | No boundary extension theorem at Rudin-simple boundary points, nor boundary injectivity theorem, found. |
| 14.19 | Missing | No matching conformal homeomorphic extension to closures found. |
| 14.20 | Missing | No matching Jordan-boundary converse, three-point conformal boundary normalization, or sphere-domain generalization found. All printed subclaims remain in scope, including the converse omitted from the book's proof. |
| 14.21 | Partial | Dilation and annulus-set facts can use elementary norm/scalar calculus. The assertion that all proper simply connected regions are conformally equivalent depends on the missing full 14.8. |
| 14.22 | Missing | Circle integration and annulus Cauchy theorems exist; no classification of conformal annuli by radius ratio was found. |

## Exact early-node APIs

### Riemann sphere and topology (13.1)

`Topology/Compactification/OnePoint/Sphere.lean:35`:

```lean
def onePointEquivSphereOfFinrankEq {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (h : finrank ℝ V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1
```

Use `V := ℂ`, `ι := Fin 3`. This gives existence of a homeomorphism;
it does not assert equality with Rudin's specific coordinate map.
`Geometry/Manifold/Instances/Sphere.lean:249` constructs `stereographic` as an
`OpenPartialHomeomorph`; `stereographic_apply` is at line 271 and the reverse-map
formula is in the same file. Its normalization has to be checked against the book.

`Topology/Compactification/OnePoint/Basic.lean`:

- `OnePoint.isOpen_def` (220), `.isOpen_iff_of_mem` (228): neighborhood topology.
- `.isOpenEmbedding_coe` (272): ordinary plane embeds openly.
- `.nhdsNE_infty_eq` (300): punctured infinity is the image of `coclosedCompact`.
- `.hasBasis_nhds_infty` (325): complements of closed compact sets are a basis.
- `.continuousAt_infty` (359): continuity at infinity is a cocompact limit condition.

`Analysis/Complex/RemovableSingularity.lean:123`:

```lean
theorem Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f)
```

At line 101, `Complex.differentiableOn_update_limUnder_of_bddAbove` also proves
holomorphicity of the extension. Compose with inversion and prove the exterior-disc
and punctured-disc filter transport; do not confuse a raw value at zero with the
continuous extension value. `Analysis/Meromorphic/Basic.lean:38` defines
`MeromorphicAt` by multiplication with a sufficiently large power to obtain an
analytic function. `Analysis/Meromorphic/Order.lean` supplies signed orders, with
`tendsto_cobounded_iff_meromorphicOrderAt_neg` at line 234.

### Rational functions and partial fractions (13.2)

`FieldTheory/RatFunc/Basic.lean`:

```lean
RatFunc.monic_denom (x : K⟮X⟯) : x.denom.Monic
RatFunc.denom_ne_zero (x : K⟮X⟯) : x.denom ≠ 0
RatFunc.num_div_denom (x : K⟮X⟯) :
  algebraMap _ _ x.num / algebraMap _ _ x.denom = x
RatFunc.isCoprime_num_denom (x : K⟮X⟯) : IsCoprime x.num x.denom
```

Source lines are 945, 952, 977, and 991, respectively.
`Algebra/Polynomial/Splits.lean:307` gives
`Polynomial.Splits.eq_prod_roots_of_monic`.
`Algebra/Polynomial/Roots.lean:810` gives
`Polynomial.prod_multiset_root_eq_finset_root`:

```lean
(p.roots.map fun a => X - C a).prod =
  p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p
```

`Algebra/Polynomial/PartialFractions.lean:407` gives the main general algebraic result:

```lean
theorem Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    [Nontrivial R] {ι : Type*} {s : Finset ι}
    (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    (n : ι → ℕ) {gi : ι → K}
    (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      algebraMap R[X] K f * ∏ i ∈ s, gi i ^ n i =
        algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
          algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1)
```

Ambient assumptions include `[CommRing R] [CommRing K] [Algebra R[X] K]`.
For a faithful global identity use `K := RatFunc ℂ`, rather than choosing a
point-evaluation algebra separately for every `z` (that risks obtaining
point-dependent coefficients). Specialize `g a := X - C a`; degree `< 1`
forces constant numerators. Package their inverse powers as polynomials with
zero constant coefficient, then evaluate off the denominator zero set.
The denominator pole-order identification is a separate analytic obligation.

### Compact exhaustion (13.3)

`Topology/Compactness/SigmaCompact.lean`:

```lean
CompactExhaustion.choice (X : Type*) [TopologicalSpace X]
  [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] : CompactExhaustion X
CompactExhaustion.subset_interior_succ (K : CompactExhaustion X) (n : ℕ) :
  K n ⊆ interior (K (n + 1))
CompactExhaustion.exists_superset_of_isCompact (K : CompactExhaustion X)
  {s : Set X} (hs : IsCompact s) : ∃ n, s ⊆ K n
```

Source lines 418, 353, and 376. The structure at line 323 has only compactness,
nested interiors, and union equal to the whole space. There is no complement
component field; (c) cannot be claimed by wrapping this structure.

## Other exact useful signatures

`Analysis/Complex/LocallyUniformLimit.lean:159`:

```lean
TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
  (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
  (hU : IsOpen U) : DifferentiableOn ℂ f U
```

At line 178, `.deriv` gives locally uniform convergence of derivatives. These
are usable closure results; they do not construct any approximation sequence.

`Analysis/InnerProductSpace/Harmonic/Constructions.lean:109`:

```lean
theorem AnalyticAt.harmonicAt_log_norm {f : ℂ → ℂ} {z : ℂ}
    (h₁f : AnalyticAt ℂ f z) (h₂f : f z ≠ 0) :
    HarmonicAt (Real.log ‖f ·‖) z
```

`Analysis/Complex/BranchLogRoot.lean:37,67` gives continuous branches:

```lean
Complex.exists_continuousOn_eqOn_exp_comp
  (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
  ∃ f, ContinuousOn f U ∧ EqOn (Complex.exp ∘ f) g U
Complex.exists_continuousOn_pow_eq
  (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (hn : n ≠ 0) :
  ∃ f, ContinuousOn f U ∧ ∀ x, f x ^ n = g x
```

Holomorphicity is not the literal conclusion of these two declarations; derive
it using local inverses or existing analytic lifting lemmas before claiming
13.11(h)/(j).

`Analysis/Complex/Conformal.lean:150`:

```lean
DifferentiableAt.conformalAt (h : DifferentiableAt ℂ f z)
  (hf' : deriv f z ≠ 0) : ConformalAt f z
```

At line 161 its iff theorem permits either holomorphicity **or antiholomorphicity**.
The warning in that file explicitly states that conjugation counts as conformal.
Book14.1's oriented-angle preservation therefore needs its own predicate or
an additional orientation condition.

`Analysis/Complex/RiemannMapping.lean:120` has only the weaker preparatory result:

```lean
exists_mapsTo_unitBall_injOn_deriv_ne_zero
  (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
  ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧
    ∀ z ∈ U, deriv f z ≠ 0
```

The file's lines 24–31 explicitly describe the incompleteness and a separate PR.
It has no `public section` for these preparatory declarations. In particular,
neither this result nor its name is evidence of a public full Riemann-mapping API.

## Search record

The entire `Mathlib/` tree was searched case-insensitively for `Runge`, `Mergelyan`,
`Mittag-Leffler`, `RiemannMapping`, `normal family`, `Montel`, `Koebe`, `univalent`,
`Schwarz reflection`, `reflection principle`, Möbius variants, annulus and boundary
terms. Candidate files for rational functions, partial fractions, stereographic
projection, one-point compactification, meromorphic orders, Cauchy integration,
locally uniform limits, harmonicity, conformality, Schwarz estimates,
Arzelà–Ascoli, compact exhaustion, and Eulerian trails were inspected directly.
Negative headline claims above are supported by these content checks, not merely
by absence of a theorem with the book's name. No dependency was modified or
replaced with an unpinned external theorem during this check.
