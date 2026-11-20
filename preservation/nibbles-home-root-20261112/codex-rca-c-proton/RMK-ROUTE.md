# Pinned-Mathlib route for RCA 6.19

Researched directly in pin d13f23b723b8a846827a245b89c10fc7d3f11612, 2026-10-29. This is a route and API map, not a completed proof.

## Exact usable core

`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`:

- `RealRMK.rieszMeasure (L : C_c(X, ℝ) →ₚ[ℝ] ℝ)` constructs a measure on arbitrary locally compact Hausdorff X (Borel measurable structure).
- `RealRMK.integral_rieszMeasure L f` (line345) gives `∫x,f x ∂rieszMeasure L = L f` for all real Cc f.
- `RealRMK.regular_rieszMeasure` (line357) supplies full measure regularity.
- `RealRMK.rieszMeasure_le_of_eq_one` (line90): for compact K and nonnegative Cc f with f=1 on K, the measure of K is at most `ENNReal.ofReal (L f)`.
- `Measure.ext_of_integral_eq_on_compactlySupported` (line412) proves uniqueness for positive measures that are regular and finite on compact sets.
- Automatic global finiteness for `rieszMeasure L` appears only under `CompactSpace X` (line445); arbitrary LCH requires a new proof using the functional's sup-norm bound and Urysohn cutoffs. Restricting to compact X would weaken 6.19.

`Mathlib/Topology/ContinuousMap/CompactlySupported.lean` provides pointwise lattice operations `sup`/`inf` (lines453–529), `nnrealPart`, and importantly:

- `CompactlySupportedContinuousMap.toRealPositiveLinear` (line799): an NNReal-linear map `C_c(X,ℝ≥0) →ₗ[ℝ≥0] ℝ≥0` extends canonically to a positive real linear functional on real Cc.
- `eq_toRealPositiveLinear_toReal` gives its value on nonnegative functions.

I searched pinned `Analysis`, `Topology`, and `Algebra/Order/Module` for order-bounded duals, lattice structures on continuous duals, positive parts of functionals, Jordan decompositions of functionals, and C*-positive functional decomposition. `Analysis/CStarAlgebra/PositiveLinearFunctional.lean` only characterizes and estimates already-positive functionals. No ready-made positive-part/Jordan decomposition of an arbitrary bounded functional was located. This is the main new proof obligation, not a missing positive RMK theorem.

## Recommended real-positive-part route

For a real bounded functional L on real C₀ restricted to real Cc, define for nonnegative f:

`P(f) = sup { L(g) : g ∈ Cc(X,ℝ), 0 ≤ g ≤ f }`.

1. The set contains0 and is bounded above by `‖L‖‖f‖∞` (use `Cc.toBoundedContinuousFunction`/the compact-support submodule norm).
2. Prove P additive on nonnegative functions. One inequality adds admissible g,h. For the other, if0≤u≤f+h, split `u₁=min(u,f)` and `u₂=u−u₁`; both are real Cc, `0≤u₁≤f`, `0≤u₂≤h`. This lattice split is much easier to formalize than Rudin's complex quotient split `fh/(f+g)`.
3. Prove NNReal homogeneity, splitting scalar0 from positive scalars and using division for the reverse inequality.
4. Convert to an NNReal-linear map with valuesNNReal, then use `toRealPositiveLinear`. It yields L⁺. The inequality L(f)≤P(f) for f≥0 makes L⁻=L⁺−L positive.
5. Apply real RMK separately to L⁺ and L⁻. Show each measure finite: for every compact K choose a cutoff0≤u≤1,u=1 onK; `rieszMeasure_le_of_eq_one` and the sup-norm bound give mass(K)≤C. Take the supremum over compacts using `IsOpen.measure_eq_iSup_isCompact` at univ (Regular.lean:1112).
6. Apply this twice to real and imaginary restrictions of the original complex Φ. Assemble four finite regular positive measures into two signed measures and then one complex measure using `SignedMeasure.toComplexMeasure` (Measure/Complex.lean:65). This requires no sigma compactness.

## Assembly / regularity / norm APIs and remaining work

- `Measure.toSignedMeasure` constructs a signed measure from a finite positive measure (VectorMeasure/Operations.lean:44).
- `SignedMeasure.toComplexMeasure_apply` is the direct real/imaginary formula.
- `VectorMeasure.integral_toSignedMeasure` (VectorMeasure/Integral.lean:671) identifies integration against a finite positive measure's signed lift with ordinary Bochner integration.
- `integral_add_vectorMeasure`, `integral_sub_vectorMeasure`, and `integral_smul_vectorMeasure` supply linearity in the measure; `integral_fun_add`, `integral_fun_sub` handle the integrand.
- For regularity of total variation, prove a reusable lemma: a finite positive measure dominated by a finite regular measure is regular. Approximate E by compact K with small dominating mass of E\K; infer inner regularity of the dominated measure. `InnerRegularWRT.weaklyRegular_of_finite` then supplies outer regularity; combine with compact inner regularity. No ready `Regular.of_le`/`Regular.of_absolutelyContinuous`/with-density regularity theorem was found in the pin, so do not silently assume it.
- The assembled complex measure's variation is dominated by the sum of the four regular finite positive measures. Root resolved the sum API: finite regular measures induce `InnerRegular`, which has an add instance (Regular.lean:773); finite inner-regular measures induce `Regular` (line902). Thus regularity of a finite sum is `by infer_instance`. Root's `Scratch619Regular.lean` implements the domination argument and this sum result.
- `Integrable.exists_hasCompactSupport_integral_sub_le` (Function/ContinuousMapDense.lean:226) gives L¹ approximation by continuous compact-support functions for any regular measure on an R1 weakly locally compact space. This supplies the classical uniqueness argument by approximating the conjugate unit polar density (6.12).
- Exact norm equality needs bounded test functions: truncate the above approximants with radial map `T(z)=z/max(1,‖z‖)`. T is continuous, T(0)=0, ‖T(z)‖≤1; for ‖w‖≤1, `‖w−T(z)‖≤2‖w−z‖`. Then approximate the conjugate polar density by Cc tests of sup norm≤1, obtaining `|μ|(X)≤‖Φ‖`; the converse is the integration bound. The located general compact-support L¹ approximation theorem does not itself preserve sup-norm≤1.

The alternate route is to follow Rudin's complex modulus functional directly and use 6.16 at p=1, but its quotient decomposition at f+g=0 is a larger initial continuity proof. It avoids four-measure assembly and makes regularity/norm equality easier once the modulus functional is built. Either full route has substantial new work beyond importing `RealRMK`.
