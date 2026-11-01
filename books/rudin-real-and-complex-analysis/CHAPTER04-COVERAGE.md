# Chapter 4 declaration coverage

All declarations below are in `RudinRCA/Chapter04.lean`. This ledger maps the
26 printed nodes to their mathematical statements. It is the implementation's
scope check, not independent review. Build and axiom evidence are recorded
separately; a statement appearing in the source alone does not certify it.
The inventory and disclosed corrections are in `INVENTORY-B.md` and
`SCOPING-B.md`. Printed proof routes may be replaced by other proofs of the
same statements; the 4.24 row identifies the main such substitution.

| Node | Declarations / representation | Statement-level assessment |
|---|---|---|
|4.1|`rudinInner`, defining identity and linearity/conjugacy lemmas, `innerFunctional`|Book first-linear convention faithfully mapped; norm/seminorm split explicit.|
|4.2|`schwarz`, `schwarz_from_axioms`|Semidefinite generality retained; the algebraic Core form assumes no preexisting norm.|
|4.3|`triangle`, `triangle_from_axioms`|Matches, including derivation of the seminorm triangle inequality from algebraic inner-product axioms.|
|4.4|`hilbert_distance`, `difference_triangle`, `hilbert_cauchy`, `CompleteSpace`|Canonical metric and Cauchy convergence represented.|
|4.5|Euclidean and general-measure L² lemmas; `continuous_interval_integral_not_complete`|All three examples addressed, including inherited integral norm and noncompleteness of continuous interval functions.|
|4.6|continuity and both Lipschitz estimates; norm 1-Lipschitz|Faithful, including uniform-continuity strengthening.|
|4.7|generic subspace criterion, empty-set counterexample, bounded-function examples, real-three-space dimension classification, closure|Printed omission of nonemptiness is explicitly disclosed and counterexample given; bounded-by-one domain caveat explicit.|
|4.8|`convex_criterion`, `subspace_convex`, `convex_translate`, `complex_subspace_convex_combinations`|Prior scope gap resolved: convex statements now use arbitrary real modules, and the complex-subspace combination theorem assumes only an arbitrary complex module. No topology or inner product is required.|
|4.9|orthogonal symmetry, closed complement, vector orthogonal kernel, intersection|Faithful.|
|4.10|`theorem_4_10`|Nonempty closed convex, unique minimum; faithful. Parallelogram identity is a proof ingredient rather than a separately exported declaration.|
|4.11|`theorem_4_11`, `corollary_4_11`, `theorem_4_11_nearest_unique`|All four parts, unique decomposition, both nearest points, linearity through continuous-linear map type, Pythagoras, proper-subspace corollary.|
|4.12|`theorem_4_12`|Unique Riesz representative with correct convention.|
|4.13|`finiteLinearCombination`, `span_least`, `span_iff_finite_linear_combination`, `independent_iff_finite_combinations`, orthonormality/coefficient definitions|Prior scope gap resolved: the purely algebraic definitions and statements use arbitrary complex modules. Orthonormality and Fourier coefficients retain the appropriate inner-product assumptions.|
|4.14|coefficient, norm, finite Bessel, residual, remainder, strict best-approximation lemmas|All indices covered for finite synthesis; strict inequality for every distinct competitor, faithful.|
|4.15|extended nonnegative sums/counting integral, ℓ² membership/norm/inner/countable support/finite-support density, `theorem_4_15_complete`|The earlier completeness bridge is now named. The inner-product theorem explicitly gives both absolute and ordinary summability, with the first-linear convention. Arbitrary index sets retained.|
|4.16|`theorem_4_16`|Domain complete only; dense subset/image; isometry and surjectivity, faithful.|
|4.17|`fourierAnalysis`, `fourierSynthesis`, coefficient and range bridges, `theorem_4_17`|Arbitrary orthonormal family, Bessel and onto analysis, isometry on closed span, faithful.|
|4.18|three iff statements and combined theorem|Four printed conditions represented including actual set maximality. Absolute product summability follows directly from `theorem_4_15_inner` applied to the two `fourierAnalysis` images and `fourierAnalysis_coefficient`; no additional maximality assumption is needed for summability. Polarization is a printed proof ingredient, not a missing endpoint.|
|4.19|Coefficient isomorphism, maximal-family form, general ℓ² representation, cardinal classification|All principal statements represented, including the printed cardinal classification whose book proof was omitted.|
|4.20|partial-order laws, origin-disc chain, empty/whole-plane nonmembership, proper chain extensions, nonmaximality|Printed false maximality explicitly replaced by proved counterexample branch, using whole plane to avoid radius-zero ambiguity. All witnesses elaborated with permitted-axiom audits in integrated run 1.|
|4.21|Hausdorff chain extension/existence, unit vector existence|Faithful within ordinary Lean classical foundations; elaborated with permitted-axiom audits in integrated run 1. Meta-equivalence to choice is explanatory foundation commentary.|
|4.22|`orthonormal_set_extension`|Extends a specified set, not merely existence from empty set. Elaborated with permitted-axiom audit in integrated run 1.|
|4.23|circle homeomorphism/periodic descent, `continuous_circleFunction`, `continuous_periodicFunction_descends`, `circleIntegral_interval`, finite/infinite `circleLp_*norm_formula`, `circleContinuous_norm_formula`, `circleLp_constant_one_norm`, `trigPolynomial_sineCosine_iff`, orthonormality|Prior gaps resolved in the statements: normalized interval and essential-supremum norms, norm of one, and equivalence of cosine/sine and exponential finite sums are explicit. The trig-polynomial equivalence uses unrestricted complex coefficients on both sides.|
|4.24|`circleContinuous_dense_L2`, `circleContinuous_L2_norm_le`, `trigonometricSystem_complete`, plus uniform approximation under 4.25|The conclusion that the trigonometric system is complete is represented using Mathlib's alternate density proof. The printed argument's particular `Q_k = c_k((1+cos t)/2)^k` construction and its intermediate identities are **not reproduced**. They are a proof route to the density/uniform-approximation endpoints, not an additional theorem being silently claimed. The subsequent Fejér argument supplies another concrete approximate-identity proof. No density or uniform-approximation endpoint is missing.|
|4.25|`uniform_trigonometric_approximation`, pointwise/exponential versions; `fejerFourierPartialSum`, `fejerMean`, `fejerConvolution_eq_mean`, `fejerMean_tendsto`, `fejerMean_error_tendsto`|Prior endpoint gap resolved: `fejerMean` is explicitly `(N+1)⁻¹ Σ_{k=0}^N s_k`, with the actual symmetric Fourier partial sums; the kernel convolution is identified with these arithmetic means; convergence is in the norm of `C(T,ℂ)`, hence uniform.|
|4.26|generic `circleFourierCoeff`/`circleFourierPartialSum`, pointwise/toLp/a.e. bridges, `circleL2_integrable`, Hilbert isometry, Riesz–Fischer, absolute/integral Parseval, symmetric partial-sum convergence and exact error tail|Prior gaps resolved: the coefficients and pointwise partial sums are defined for arbitrary functions, hence for all L¹ functions, and L²⊆L¹ is explicit. The tail subtype is integers outside `[-N,N]`, exactly equivalent to `abs(n)>N`. All listed L² endpoints retain their intended scope.|

