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
| **13.8** | 271–272 | Remark with proof | If compact `K⊆ℂ` has disconnected spherical complement, choose a bounded complementary component `V` and `α∈V`. The holomorphic-near-`K` function `f(z)=(z−α)⁻¹` cannot be uniformly approximated by polynomials on `K`. Quantitatively, for `m=max_{z∈K}|z−α|>0`, no polynomial has pointwise error `<1/m` throughout `K`; otherwise the maximum principle applied to `(z−α)P(z)−1` contradicts its value at `α`. With the preceding disconnected-spherical-complement hypothesis retained, the prescribed representative in each component in 13.6 is likewise necessary for approximation of all holomorphic-near-`K` functions. An unrestricted converse for every compact `K` would add a quantifier not justified by this paragraph (a singleton admits exact constant approximation without any poles). |
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
