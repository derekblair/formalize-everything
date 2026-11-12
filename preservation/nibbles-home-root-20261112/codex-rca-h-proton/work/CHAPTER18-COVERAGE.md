# Chapter 18 integration map (in progress)

Printed third edition, pp. 356–368. 21 top-level nodes and three local corollaries. This is an implementation map, not a chapter-pass claim. The ideals fragment (18.12–17) has a successful CLI check; the Wiener fragment (18.21) has zero errors and permitted axioms in completed combined LSP check all-02. The overall combined module is not yet passing.

| Printed node | Required coverage | Principal declarations / fragment | Validation |
|---|---|---|---|
| 18.1 | Algebra and Banach structures; continuity of multiplication; identity and inverse uniqueness; units group; spectrum | Core: typeclass setup, `isUnit_iff_two_sided_inverse`, `inverse_unique`, `unit_unique`, `units_mul_inverse`, `multiplication_continuous`, `multiplication_tendsto`, `bookSpectrum` | Draft |
| 18.2 | Expository connections to holomorphy and spectral theory; no separate formal proposition | Cross-reference 18.5–9 in chapter documentation; retain this row in inventory | Documentation pending integration |
| 18.3 | Neumann series and full quadratic error estimate | Core: `neumann_series`, `neumann_series_alternating`, `neumann_series_remainder` | Draft |
| 18.4 | Perturbation invertibility and exact α,β remainder bound | Core: `perturbation_isUnit`, `perturbation_remainder` | Draft |
| 18.4 C1 | Open units and inversion homeomorphism | Core: `units_isOpen`, `inversionHomeomorph`, `units_subspace_topology` | Draft |
| 18.4 C2 | Noncommutative derivative −x⁻¹hx⁻¹ | Core: `inversion_hasFDerivAt` | Draft |
| 18.4 C3 | Compact spectrum and spectral norm bound | Core: `spectrum_compact_and_bound` | Draft |
| 18.5 | Scalarized resolvent holomorphy and decay at infinity | Core: `scalarized_resolvent` | Draft |
| 18.6 | Compact, nonempty spectrum | Core: `spectrum_nonempty_compact` | Draft |
| 18.7 | Isometric Gelfand–Mazur equivalence under merely submultiplicative norm | Core: `gelfandMazur`, `gelfandMazur_isometry` | Draft |
| 18.8 | Real spectral radius | Core: `bookSpectralRadius`, `bookSpectralRadius_eq` | Draft |
| 18.9 | Limit of real nth roots of norms of powers | Core: `spectral_radius_formula` | Draft |
| 18.10 | Algebraic invariance, ambient spectrum inclusion, inherited-norm spectral-radius equality | Core: `algebraic_spectrum_invariant`, `ambient_spectrum_subset`, `ambient_spectralRadius_eq` | Draft |
| 18.11 | Closed boundary disc algebra; coordinate spectra closed disk vs circle; unequal spectra but equal radii | Disc: `discBoundarySubalgebra_isClosed`, `discBoundaryCoordinate_subalgebra_spectrum`, `discBoundaryCoordinate_spectrum`, `discCoordinate_spectra_differ`, `discCoordinate_spectralRadii_equal` | Draft |
| 18.12 | Ideals/subspaces, no units in proper ideals, nonunital homomorphism kernels | Ideals: `RudinHom`, `definition18_12_*` | Passed scratch check04 |
| 18.13 | Maximal ideal containment and closedness | Ideals: `theorem18_13_*` | Passed scratch check04 |
| 18.14 | Vector-space cosets and quotient; operations, kernel, surjectivity; quotient field iff maximal | Ideals: `definition18_14_coset`, `theorem18_14_*` | Passed scratch check04 |
| 18.15 | Quotient norm as infimum/distance; norm/completeness; quotient Banach algebra and unit norm | Ideals: `definition18_15_*`, `theorem18_15_*` | Passed scratch check04 |
| 18.16 | Algebraic nonzero multiplicative complex linear functionals, initially no continuity assumption | Ideals: `RudinCharacter`, `definition18_16_*` | Passed scratch check04 |
| 18.17 | All five character/maximal-ideal/spectrum/invertibility/boundedness parts; automatic continuity | Ideals: `theorem18_17_a` through `_e` and helpers | Passed scratch check04 |
| 18.18 | Polynomial density; characters and maximal ideals are evaluations; finite closed-disc Bezout identity | Disc: `disc_polynomial_approx`, `disc_character_evaluation`, `disc_maximal_iff_evaluation_kernel`, `disc_bezout`, `disc_bezout_positive` | Draft |
| 18.19 | Closed proper boundary algebra, Fourier iff, maximality among closed subalgebras | Fejer uniform convergence + Disc boundary adapter + BoundaryCharacterization `theorem18_19_circle_*` | Draft |
| 18.20 | Adjoining a function with a nonzero negative Fourier coefficient gives every continuous circle function as a uniform limit of finite sums Pᵢ(z)g(z)ⁱ | Maximality `theorem18_20*`, BoundaryCharacterization `theorem18_20_circle`; exact interval coefficient normalization | Draft |
| 18.21 | Absolutely summable Laurent series, nowhere zero on circle, absolutely summable reciprocal series | Wiener ℓ¹ convolution algebra and `theorem18_21` | LSP all-02 family checked; clean CLI pending |

Final integration order: Core → Ideals → Disc → Fejer → Maximality → BoundaryCharacterization → Wiener. Collect Mathlib imports at the top; omit scratch-module imports; retain namespaces and all axiom audits. Only one published module, `RudinRCA/Chapter18.lean`.

No chapter is eligible for a normal PR until all rows are accounted for, the combined module passes, every printed theorem family has an allowed-axiom audit, and a clean-slate module build exits zero. Chapters 19 and 20 have independent inventories but no implementation yet.
