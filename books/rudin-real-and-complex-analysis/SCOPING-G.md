# RCA cluster G: independent printed-node inventory

Checked 2026-10-29 against Walter Rudin, *Real and Complex Analysis*, third edition (1987). This is an independent inventory, not the missing Stage 1 deliverable and not a claim that any node is formalized.

## Evidence and counting convention

- Printed text and page images: <https://ru.djvu.online/file/NKmAEzkLVs8Io>. The title page explicitly says Third Edition; publication page gives 1987. The scanned page numbers, not viewer positions, are used below.
- Direct page images follow `https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/{p+12}.webp` for printed page `p`. Example: [printed p. 300](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/312.webp). Selected images were downloaded into this workdir as `rudin-scan-pNNN.webp` and visually checked to resolve OCR-lost inequalities/formulas. These scans are research evidence outside the repository; do not commit them.
- All numbered nodes count, including definitions, notation, remarks, examples, and numbered exposition. Unnumbered corollaries and qualifications are recorded with their containing node. Exercises are excluded.
- `U` is the open unit disc, `T` its boundary, `H(Ω)` the holomorphic functions on open `Ω`, and `σ` normalized Lebesgue measure on `T`. A region is connected and open. Statements below are mathematical paraphrases, not transcriptions.

| Chapter | Numbered range | Count | Printed body pages | Exercises begin |
| --- | --- | ---: | --- | --- |
| 15 | 15.1–15.27 | 27 | 298–315 | 315 |
| 16 | 16.1–16.22 | 22 | 319–332 | 332 |
| 17 | 17.1–17.26 | 26 | 335–352 | 352 |
| Total | | **75** | | |

**Inventory correction (2026-10-29):** the initial count omitted the numbered Remark **15.27**, immediately before Exercises on printed p.315. Visual reinspection of [p.315](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/327.webp) confirms the corrected Chapter 15 count **27** and cluster total **75**. The other chapter endings were rechecked visually: [p.332](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/344.webp) ends 16.22 directly before Exercises; [p.351](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/363.webp) starts 17.26 and [p.352](https://djvu.online/jpg/N/K/m/NKmAEzkLVs8Io/364.webp) ends its proof directly before Exercises. Hence Chapter 16 remains **22** and Chapter 17 remains **26**. These pages are saved as `rudin-scan-p315.webp`, `rudin-scan-p332.webp`, `rudin-scan-p351.webp`, and `rudin-scan-p352.webp` in the lane research directory.

**Ticket discrepancy:** issue #43 labels F. and M. Riesz as 17.11. In this printed third edition, it is **17.13**, pp. 341–342. Node 17.11 is the Hardy-space boundary convergence theorem, pp. 340–341. Both belong to the stated chapter scope.

## Chapter 15 — Zeros of Holomorphic Functions

Types: 15 theorems, 3 lemmas, 3 definitions, 1 remark, 5 numbered expository nodes.

| Node | Printed type | Pages | Mathematical content and required qualifications |
| --- | --- | --- | --- |
| 15.1 | Exposition | 298 | Recalls absence of interior accumulation points of the zeros of a nonconstant holomorphic function on a region. Announces the converse zero-set construction of 15.11 and motivates construction by infinite products. |
| 15.2 | Definition | 298–299 | An infinite product `∏(1+u_n)` is the limit of its finite initial products when that sequence converges. **A zero limit counts as convergence** in Rudin's convention. |
| 15.3 | Lemma | 299 | For finitely many complex `u_n`, put `p=∏(1+u_n)` and `p*=∏(1+|u_n|)`. Then `p*≤exp(Σ|u_n|)` and `|p−1|≤p*−1`. |
| 15.4 | Theorem | 299–300 | If each complex function `u_n` is bounded on arbitrary set `S` and `Σ|u_n(s)|` converges uniformly on `S`, then `∏(1+u_n(s))` converges uniformly to `f`. At each `s`, `f(s)=0` iff some factor vanishes. Every permutation of the factors gives the same product. |
| 15.5 | Theorem | 300 | For real `0≤u_n<1`, the partial products of `1−u_n` have a limit; that limit is positive iff `Σu_n<∞`. The non-strict lower bound is visually confirmed. |
| 15.6 | Theorem | 300–301 | If `f_n∈H(Ω)`, no `f_n` is identically zero on any component of `Ω`, and `Σ|1−f_n|` converges uniformly on compact subsets, then `∏f_n` converges locally uniformly to `f∈H(Ω)`. At each point, its zero multiplicity equals the sum of factor multiplicities; only finitely many positive summands occur locally. |
| 15.7 | Definition | 301 | Weierstrass elementary factors: `E₀(z)=1−z`; `E_p(z)=(1−z)exp(Σ_{k=1}^p z^k/k)` for positive integer `p`. Their only zero is `1`; 15.8 quantifies their approach to `1`. |
| 15.8 | Lemma | 301–302 | `|1−E_p(z)|≤|z|^(p+1)` whenever `|z|≤1` and integer `p≥0`. The boundary `|z|=1` is included. |
| 15.9 | Theorem | 302–303 | Given nonzero `z_n` with `|z_n|→∞` and nonnegative integers `p_n` such that `Σ(r/|z_n|)^(1+p_n)<∞` for every `r>0`, the product `∏E_{p_n}(z/z_n)` is entire with exactly those zeros, counting repetitions as multiplicities. The choice `p_n=n−1` always works (book indexing starts at `1`). Constant admissible `p_n` give the canonical-product discussion. |
| 15.10 | Theorem | 303 | Every entire `f` with `f(0)≠0` factors as `exp(g)∏E_{p_n}(z/z_n)` for entire `g` and suitable `p_n`, where `z_n` lists all zeros with multiplicity. If `0` has order `k`, first remove `z^k`. Finite/empty zero lists must also be handled. |
| 15.11 | Theorem | 303–304 | For a **proper open subset of the Riemann sphere** `Ω≠S²`, a set `A⊆Ω` without limit points in `Ω`, and positive multiplicities `m(a)`, there exists `f∈H(Ω)` whose zero set is exactly `A`, with order `m(a)` at each `a`. A plane-only restatement would omit printed scope. |
| 15.12 | Theorem | 304 | Every meromorphic function on open `Ω` is a quotient of two holomorphic functions on `Ω`. Conversely such a quotient is meromorphic when its denominator is not identically zero on any component. Equality at poles requires the appropriate meromorphic interpretation. |
| 15.13 | Theorem | 304–305 | On a plane open set `Ω`, for discrete `A⊆Ω`, nonnegative integers `m(a)`, and arbitrary complex data `w_{n,a}` for `0≤n≤m(a)`, a holomorphic `f` exists with `f^(n)(a)=n!w_{n,a}` at every prescribed jet. |
| 15.14 | Definition | 305 | The ideal generated by finitely many `g_i∈H(Ω)` consists of sums `Σf_i g_i` with `f_i∈H(Ω)`. Principal means one generator. Defines/recalls zero multiplicity `m(f,a)=0` when `f(a)≠0`. |
| 15.15 | Theorem | 306 | Every finitely generated ideal of `H(Ω)` is principal: for generators `g_i`, there are holomorphic `g,f_i,h_i` satisfying `g=Σf_i g_i` and `g_i=h_i g`. Printed theorem covers arbitrary open `Ω`, including disconnected sets and identically zero generators. |
| 15.16 | Exposition | 307 | Explains how growth conditions impose quantitative zero restrictions and introduces Jensen's formula as the tool. No independent additional theorem beyond the referenced zero-set and following Jensen results. |
| 15.17 | Lemma | 307 | The normalized circle integral of `log|1−exp(iθ)|` is zero. Endpoint logarithmic singularities must be represented using a legitimate integral convention. |
| 15.18 | Theorem | 307–308 | For `f∈H(D(0,R))`, `f(0)≠0`, `0<r<R`, and the zeros `a₁,…,a_N` in the **closed** disc of radius `r`, with multiplicities: `|f(0)|∏(r/|a_n|)=exp((2π)⁻¹∫log|f(re^{iθ})|dθ)`. Boundary zeros are allowed; their factors equal `1`. |
| 15.19 | Theorem | 308–309 | For bounded nonzero holomorphic `f` on `U`, let `μ_r` be the mean of `log|f(re^{iθ})|` and `μ*` that of its radial boundary limits. Then `μ_r≤μ_s` for `r<s`, `μ_r→log|f(0)|` as `r→0`, and `μ_r≤μ*`. Consequently `log|f*|∈L¹(T)` and `f*≠0` almost everywhere. `log 0` here is `−∞`. |
| 15.20 | Exposition with results | 309–310 | For entire `f` normalized by `f(0)=1`, maximum modulus `M(r)`, and zero count `n(r)`, Jensen gives `n(r)log 2≤log M(2r)`. A bound `M(r)≤exp(Ar^k)` for all large `r` implies `limsup log n(r)/log r≤k`. The example `1−exp(z^k)` illustrates sharp growth after accounting for the zero at `0`. |
| 15.21 | Theorem and definition | 310 | If nonzero `a_n∈U` satisfy `Σ(1−|a_n|)<∞` and `k≥0`, then `B(z)=z^k∏[(|a_n|/a_n)(a_n−z)/(1−conj(a_n)z)]` is bounded holomorphic with precisely the prescribed zeros and multiplicities. Defines Blaschke products, including finite and empty products. |
| 15.22 | Exposition and definition | 310–311 | Introduces `log⁺t=log t` for `t>1` and `0` otherwise, and the Nevanlinna class `N={f∈H(U):sup_{0<r<1}∫log⁺|f_r|dσ<∞}`. Notes `H∞⊆N`; introduces necessity of the Blaschke condition, proved in 15.23. |
| 15.23 | Theorem | 311–312 | Every nonzero `f∈N` has zeros satisfying `Σ(1−|a_n|)<∞`, with multiplicities. Its unnumbered corollary is uniqueness: a function of `N` whose zeros violate this condition must be identically zero; this includes `H∞`. |
| 15.24 | Theorem | 312 | For every Blaschke product, `|B*|=1` almost everywhere and the mean of `log|B(re^{iθ})|` tends to `0` as `r↑1`. |
| 15.25 | Exposition | 312–313 | Recalls polynomial density in `C([0,1])`, defines spanning by dense finite linear combinations, and poses the generalized-power density question answered by 15.26. |
| 15.26 | Theorem | 313–315 | If `0<λ₁<λ₂<…`, let `X` be the uniform closure of the span of `1,t^{λ₁},…` in complex `C([0,1])`. If `Σ1/λ_n=∞`, then `X=C([0,1])`. If the sum is finite, `t^λ∉X` for each nonzero exponent `λ` not in the list (for exponents yielding a continuous function, implicitly `λ>0` in this real-exponent context). |

| 15.27 | Remark | 315 | With the increasing positive exponents and uniform-closed-span convention of 15.25–15.26, if `{1,t^λ₁,t^λ₂,…}` spans `C([0,1])`, an infinite subcollection of its nonconstant powers can be deleted while retaining that span; thus there is no minimal spanning family of this form. In contrast, deleting any vector from an orthonormal family strictly reduces its closed span. If the power family does not span `C([0,1])`, deletion of any one element strictly reduces its closed span, by 15.26(b) (and evaluation at zero for deletion of `1`). |

## Chapter 16 — Analytic Continuation

Types: 11 theorems, 1 proposition, 4 definitions, 2 remarks, 1 example, 3 numbered expository/definition nodes.

| Node | Printed type | Pages | Mathematical content and required qualifications |
| --- | --- | --- | --- |
| 16.1 | Definition | 319 | A boundary point of a disc is regular for a holomorphic function when it extends holomorphically across that point on a centered disc; all other boundary points are singular. Regular points form a relatively open boundary subset. |
| 16.2 | Theorem | 320 | A power series with radius of convergence exactly `1`, representing `f∈H(U)`, has at least one singular point on `T`. |
| 16.3 | Definition | 320 | `T` is a natural boundary if every point of it is singular. Then no holomorphic extension exists to a larger region containing `U`. |
| 16.4 | Remark | 320–321 | Any plane region admits a holomorphic function with no extension to a larger region. The explicit lacunary series `Σ_{n≥0}z^(2^n)` has natural boundary `T`; its functional equation and divergence along dyadic-root radii establish this. |
| 16.5 | Theorem (Ostrowski) | 321–322 | Positive integers `λ,p_k,q_k` satisfy increasing `p_k` and `λq_k>(λ+1)p_k`. A radius-one series whose coefficients vanish for `p_k<n<q_k` has subsequence of partial sums `s_{p_k}` converging in a neighborhood of every regular boundary point. The following note strengthens this to uniform convergence on some neighborhood. |
| 16.6 | Theorem (Hadamard) | 322 | If positive integers `p_k` obey `p_{k+1}>(1+1/λ)p_k` for some positive integer `λ`, then any radius-one series `Σc_k z^{p_k}` has natural boundary `T`. |
| 16.7 | Example | 322–323 | Taking coefficients `exp(−√n)` when `n` is a power of `2` and `0` otherwise gives natural boundary `T`, although every derivative series converges uniformly on the closed disc and boundary values are smooth. |
| 16.8 | Theorem | 323 | If a region cut by a line or circular arc is the union of two regions, a continuous function on the original region, holomorphic on both pieces, is holomorphic everywhere. |
| 16.9 | Definitions | 323–324 | Defines function elements `(f,D)`, direct continuation by agreement on nonempty disc overlaps, disc chains, continuation along a chain, chains covering curves, and continuation along curves. Chain continuation is unique. Direct continuation is not generally transitive; a square-root example is given. |
| 16.10 | Proposition | 324 | Direct continuation is transitive for three function elements whose three discs have a common point. |
| 16.11 | Theorem | 324–325 | Continuation of a given function element along a given curve starting at the disc center is unique, in the sense of equality of terminal functions on their overlap / equality of terminal germs. |
| 16.12 | Definition | 325 | A one-parameter family of curves with common endpoints is a continuous map from `[0,1]²` with those endpoints fixed on the two vertical sides. |
| 16.13 | Theorem | 325–326 | If a function element can be continued along every curve in such a family, all terminal germs coincide; in particular the first and last continuations agree. |
| 16.14 | Theorem | 326 | Any two curves with the same endpoints in a simply connected topological space are joined by an endpoint-fixed one-parameter family of curves. |
| 16.15 | Theorem (monodromy) | 327 | A function element in a simply connected region that can be continued along every curve from its center extends to one holomorphic function on the whole region. |
| 16.16 | Remark | 327 | The universal monodromy conclusion fails on every nonsimply connected plane region: local logarithms of `z−w` continue along paths, but nonzero winding around a suitable omitted `w` obstructs a global extension. |
| 16.17 | The Modular Group | 328 | Defines integral determinant-one Möbius transformations; shows they form a group preserving the upper half-plane, with inverse formula. States generation by `z↦z+1` and `z↦−1/z`; defines modular functions by invariance under this group or a nontrivial subgroup. |
| 16.18 | A Subgroup | 328–329 | Defines `Γ` generated by `σ(z)=z/(2z+1)` and `τ(z)=z+2`. Its proposed fundamental set is `Q={x+iy:y>0, −1≤x<1, |2z+1|≥1, |2z−1|>1}`. The mixed strict/non-strict boundary conventions are essential. |
| 16.19 | Theorem | 329–330 | Distinct `Γ` translates of `Q` are disjoint, their union is the upper half-plane, and `Γ` contains every determinant-one integral Möbius map with odd diagonal entries and even off-diagonal entries (hence equals that subgroup). |
| 16.20 | Theorem | 330–331 | A holomorphic `λ` on the upper half-plane exists that is `Γ` invariant, injective on `Q`, has range `ℂ\{0,1}`, and has the real line as a natural boundary. |
| 16.21 | Exposition | 331–332 | States little Picard and distinguishes big Picard: an essential isolated singularity cannot omit two complex values in a punctured neighborhood; a nonpolynomial entire function takes every value infinitely often, with at most one exception. The book explicitly does **not** prove big Picard here. This is still a numbered exposition node and must not silently disappear from the inventory. |
| 16.22 | Theorem (little Picard) | 332 | An entire function omitting two distinct complex values is constant. |

## Chapter 17 — Hᵖ-Spaces

Types: 16 theorems, 1 lemma, 3 definitions, 1 notation node, 2 remarks, 3 numbered expository/definition nodes.

| Node | Printed type | Pages | Mathematical content and required qualifications |
| --- | --- | --- | --- |
| 17.1 | Definition | 335–336 | Subharmonic `u:Ω→[−∞,∞)` is upper semicontinuous and satisfies the submean inequality on each **closed** disc contained in `Ω`; none of those circle integrals is `−∞`. Real harmonic functions are subharmonic. |
| 17.2 | Theorem | 336 | An increasing convex real function composed with a subharmonic function is subharmonic, defining its value at `−∞` by the corresponding limit. |
| 17.3 | Theorem | 336 | If nonzero `f` is holomorphic on a region, then `log|f|`, `log⁺|f|`, and `|f|^p` for every `p>0` are subharmonic; `log 0=−∞`. |
| 17.4 | Theorem | 336–337 | A continuous subharmonic `u` on `Ω` below a continuous real `h` on the boundary of compact `K⊆Ω`, with `h` harmonic in the interior of `K`, remains below `h` on all of `K`. Printed inequalities are non-strict. |
| 17.5 | Theorem | 337 | Circle means of a continuous subharmonic function on `U` are nondecreasing with radius. |
| 17.6 | Notation | 337 | Defines radial functions `f_r(e^{iθ})=f(re^{iθ})`, normalized circle measure `σ(T)=1`, their `L^p` norms and supremum norm, and the size `‖f_r‖₀=exp∫log⁺|f_r|dσ`. The `p=0` quantity is not a norm. |
| 17.7 | Definition | 337–338 | Defines `‖f‖_p=sup_{0≤r<1}‖f_r‖_p` for `0≤p≤∞`, Hardy `H^p` by finiteness for `0<p≤∞`, and `N` by finiteness of the `p=0` size. Gives inclusions `H∞⊆H^p⊆H^s⊆N` for `0<s<p<∞`. |
| 17.8 | Remarks | 338 | (a) Radial sizes increase and their limit is the Hardy size. (b) For `1≤p≤∞`, the Hardy size is a norm. (c) These spaces are complete. (d) For `0<p<1` they are vector spaces but the indicated size does not satisfy the triangle inequality. |
| 17.9 | Theorem | 338–339 | For nonzero `f∈N`, dividing out the Blaschke product of all its zeros gives zero-free `g∈N` with unchanged `p=0` size. If `f∈H^p`, then `g∈H^p` with equal norm/size, for **`0<p≤∞`**. |
| 17.10 | Theorem | 339 | For `0<p<∞` and nonzero `f∈H^p`, `f=B h^(2/p)` for its zero Blaschke product `B` and a zero-free `h∈H²`, using a holomorphic branch. In particular every `H¹` function is a product of two `H²` functions. |
| 17.11 | Theorem | 340–341 | For `0<p<∞`, `f∈H^p` has nontangential maximal functions in `L^p(T)` (every aperture parameter `α<1` in the earlier definition), almost-everywhere nontangential limits `f*∈L^p(T)`, radial `L^p` convergence, and `‖f*‖_p=‖f‖_p`. For `H¹`, both Cauchy and Poisson representations by `f*` hold. |
| 17.12 | Theorem | 341 | A holomorphic power series on `U` belongs to `H²` iff its coefficients are square summable; its squared Hardy norm equals their squared sum. |
| 17.13 | Theorem (F. and M. Riesz) | 341–342 | A complex Borel measure on `T` whose Fourier coefficients vanish at every negative integer is absolutely continuous with respect to Lebesgue measure. This is the node misnumbered in issue #43. |
| 17.14 | Definition | 342 | Inner means bounded holomorphic with boundary modulus `1` almost everywhere. Outer functions have form `c exp∫(e^{it}+z)/(e^{it}−z) log φ(e^{it})dσ(t)` for `|c|=1`, positive measurable `φ`, and `log φ∈L¹(T)`. |
| 17.15 | Theorem | 342–343 | Every inner function, and only such functions, has form `c B(z) exp(−∫(e^{it}+z)/(e^{it}−z)dμ(t))`, with `|c|=1`, Blaschke `B`, and finite positive circle measure `μ` singular relative to Lebesgue measure. |
| 17.16 | Theorem | 343 | For an outer function constructed from `φ`, `log|Q|` is the Poisson integral of `log φ`, radial boundary modulus equals `φ` almost everywhere, and `Q∈H^p` iff `φ∈L^p(T)`, with equal sizes (`0<p≤∞`). |
| 17.17 | Theorem | 344–345 | Nonzero `f∈H^p`, **`0<p≤∞`**, has integrable boundary log modulus and factorization `f=M_f Q_f` with inner `M_f` and normalized outer `Q_f` from `|f*|`. Also `log|f(0)|≤∫log|f*|dσ`, with equality exactly when the inner factor is constant. |
| 17.18 | Theorem | 345 | For nonzero `f∈H^p`, `0<p≤∞`, the boundary function is nonzero almost everywhere. Consequently two `H^p` functions agreeing on a positive-measure boundary set are equal throughout `U`. |
| 17.19 | Exposition with results | 345–346 | Nonzero Nevanlinna functions have a Blaschke/exponential representation using a finite signed real measure, and can be written `b₁/b₂` for bounded holomorphic functions with zero-free denominator. They have finite nonzero radial limits a.e. and integrable boundary log modulus. The Jensen-type inequality of 17.17 can fail: `exp((1+z)/(1−z))` has size `e`, boundary modulus `1` a.e., but `log|f(0)|=1`. |
| 17.20 | Invariant Subspaces | 346–348 | Defines closed invariant subspaces and the unilateral shift on `ℓ²`; its norm is `1`. The coefficient map is a Hilbert-space isomorphism `ℓ²≅H²` conjugating the shift to multiplication by `z`. Gives zero-condition invariant subspaces, including finite-Blaschke multiples. |
| 17.21 | Beurling's Theorem | 348–349 | Each inner `φ` gives a closed shift-invariant space `φH²`. Equal spaces from two inner functions imply their quotient is constant. Every **nonzero** closed shift-invariant subspace has this form. |
| 17.22 | Remark | 349 | Combining inner-function factorization with Beurling identifies nonzero invariant subspaces by a Blaschke zero multiset and a positive singular boundary measure. The zero subspace is the explicit exception inherited from 17.21; the containment-condition exercise is out of scope. |
| 17.23 | Theorem | 350 | If `M_f` is the inner factor of `f∈H²`, its generated closed shift-invariant subspace is `M_f H²`; it equals `H²` iff `f` is outer. Equivalently polynomial multiples approximate precisely functions divisible by `M_f` within `H²`. Existence of the inner factor implicitly excludes `f=0`. |
| 17.24 | Formulation of the Problem | 350–351 | Defines the normalized harmonic conjugate (`v(0)=0`) and introduces `ψh(z)=∫(e^{it}+z)/(e^{it}−z)h(e^{it})dσ(t)`. Asks when bounded radial `L^p` size transfers to the conjugate; states the positive range `1<p<∞` and endpoint failure (`p=1,∞`, delegated to exercises). |
| 17.25 | Lemma | 351 | For `1<p≤2`, set `δ=π/(1+p)`, `α=1/cos δ`, `β=α^p(1+α)`. Then `1≤β(cos φ)^p−α cos(pφ)` for `−π/2≤φ≤π/2`. All endpoint inequalities were checked visually. |
| 17.26 | Theorem (M. Riesz) | 351–352 | For every `1<p<∞`, a finite constant `A_p` exists such that `ψ:L^p(T)→H^p` is bounded with `‖ψh‖_p≤A_p‖h‖_p`, for complex-valued `h` too. Equivalently the corresponding radial integral bound holds uniformly for `0≤r<1`. |

## Formalization cautions from the printed text

1. The literal numbered-node inventory is larger than a theorem-only list. Numbered expositions may announce results proved later; record which later formal result discharges which claim, and do not count prose labels as proofs.
2. Node 15.2 allows zero-limit products. An unconditional `tprod` whose convergence notion differs is not by itself a faithful formalization of this convention.
3. Node 15.11 explicitly works on proper open subsets of the Riemann sphere. Omitting neighborhoods of infinity silently narrows its scope.
4. Node 15.18 includes zeros on the circle, and 15.19 allows `f(0)=0` with extended-real log limit. A real-valued `log 0=0` library convention requires an explicit bridge.
5. In 15.20 the sharpness example has a zero at the origin, whereas the preceding normalization was `f(0)=1`; apply the usual removal of the zero at the origin or disclose the different normalization instead of treating the example as satisfying the earlier hypothesis.
6. Node 16.21 states big Picard without proof. Numbered scope includes the exposition, but no implementation should falsely claim that little Picard alone proves its stronger assertions.
7. Printed p-ranges repeatedly include `∞` where OCR shows `<∞`: notably 17.7–17.9, 17.17, and 17.18. In contrast 17.10–17.11 require finite positive `p`.
8. Node 17.22's invariant-subspace classification inherits a nonzero-subspace qualification. Node 17.23 inherits nonzero `f` from the existence of its inner factor. State these dependencies explicitly.

## Stage 2 coverage in this branch

No chapter is complete. Nodes 15.3 and 15.4 have passed separate Lean checks with all audited declarations using only `propext`, `Classical.choice`, and `Quot.sound`; their integration and the clean-slate module build are pending. All other nodes remain under development or unstarted. The workdir `STATUS.md` records the current state and evidence paths.

The corresponding theorem families are `finite_product_estimates` (15.3), `uniform_product_of_uniform_norm_series`, `product_eq_zero_iff_of_uniform_norm_series`, and `uniform_product_reindex_of_uniform_norm_series` (15.4). The latter retains uniform convergence of the norm series and boundedness of each summand on an arbitrary underlying set; it does not replace those hypotheses by summable sup norms.

The upstream progress table defines Done as merged on main. Its Done column remains zero until independently reviewed code lands.
