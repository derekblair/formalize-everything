# Wiener 18.21 source review

Reviewed source: `work/Chapter18Wiener.lean`, SHA-256 `c8c449022065aa5792c44407e4e33a8e53a6317a21a4b61be0f7c9dddf2ded1e`.

The completed combined-server pass `all-02` accepted this exact source with zero Wiener errors or warnings. Its two principal declarations, `Wiener.reciprocal` and `theorem18_21`, each depend only on `propext`, `Classical.choice`, and `Quot.sound`. Evidence is recorded in `evidence/wiener-lsp-audit.json`. This is a completed **Lean LSP development check**, not the final CLI clean build. Other chapter fragments had errors in that combined pass, and the final chapter CLI gate remains pending. The earlier individual CLI pass failed before the repairs described below.

## Exact Banach-algebra hypotheses

`Coefficients : Type` is the existing Mathlib space `ℓ¹(ℤ, ℂ)`. Its additive group, complex scalar action, norm, metric, and completeness are inherited from `lpSpace`; no completeness conclusion is assumed as an extra theorem hypothesis. `summable_norm` and `norm_eq_tsum` specialize the actual `lp.memℓp` and `lp.norm_eq_tsum_rpow` results to exponent 1.

Convolution is a sum **in the complete ℓ¹ space** of the vectors `single (i+j) (a i * b j)`. The proof first establishes summability of the norms of this double family, using the product of the two absolutely summable scalar coefficient families. Consequently its sum is an element of ℓ¹. The norm estimate follows from the norm-of-sum bound and the absolutely summable product formula. This does not assume closure of a pointwise-defined Cauchy product.

The multiplication is bundled as a continuous complex-bilinear map. Commutativity, associativity, and the identity law are proved by reducing continuous linear maps, one variable at a time, to the single-coordinate vectors via `lp.ext_continuousLinearMap`. The relevant basis identity is `δ_i(a) * δ_j(b) = δ_(i+j)(ab)`. This establishes actual ring laws for the new multiplication rather than inferring them from evaluation at circle points.

The multiplicative identity is `single 0 1`, **not** the constant sequence 1 (which would not belong to ℓ¹ on ℤ). Its norm is exactly 1 by `lp.norm_single`. The `NormedCommRing` constructor retains the existing additive normed structure and supplies the proved submultiplicative estimate. `Algebra.ofModule` uses the proved scalar-compatibility laws for convolution and the existing complex module. The `NormedAlgebra` instance uses its existing scalar-norm bound. These are precisely the hypotheses of checked `theorem18_17_nonunit_character`: `NormedCommRing`, `NormedAlgebra ℂ`, and `CompleteSpace`.

## Characters and the reciprocal conclusion

For every circle point `z`, evaluation is a bounded complex-linear map: the norm of each term is the coefficient norm because `‖z‖=1`. Absolute summability is proved before any evaluation sum is used. Mapping the convergent vector-valued convolution sum through evaluation, followed by the absolutely summable product formula, proves multiplicativity. Evaluation of the coefficient unit is 1.

For an arbitrary unital algebra homomorphism `φ` to ℂ, the general Banach-algebra bound gives `‖φ(δ_1)‖≤1` and `‖φ(δ_-1)‖≤1`. Their product is 1, so `‖φ(δ_1)‖=1`. The resulting point lies on `Circle`. Multiplication of the single-coordinate vectors gives the positive powers, and their inverses give the negative powers. Finally, `lp.hasSum_single` and automatic continuity of `φ` identify its value on every ℓ¹ sequence with the absolutely convergent circle evaluation. No Fourier-coefficient uniqueness assumption is used.

If a coefficient sequence were a nonunit, Chapter 18.17 would give a nonzero multiplicative linear functional vanishing on it. The checked conversion `definition18_16_characterAlgHom` supplies the unital algebra homomorphism used by the classification. This contradicts nowhere-zero evaluation. Its algebraic inverse is then chosen **inside `Coefficients`**, and `summable_norm` supplies the required absolute summability of the inverse coefficients. Evaluating the product-one relation gives the pointwise reciprocal identity.

The public `theorem18_21` assumes exactly an absolutely summable Laurent-series representation on `Circle` and nowhere-zero values. It concludes an absolutely summable coefficient family representing the reciprocal. It does not substitute invertibility in `C(Circle, ℂ)`, assume a reciprocal-series representation, or weaken the conclusion to continuity or pointwise invertibility. The source's use of unordered `tsum` is justified by absolute summability and matches the printed bilateral series.

## API repairs accepted by the completed development check

- Explicit coefficient `Type` and explicit `lp.single` family parameters address the first pass's subgroup/type inference and heartbeat failure.
- The new `change` steps expose the exact functions inside `LinearMap.mkContinuous` and `mkContinuous₂` before applying the norm bounds.
- Continuous-linear-map extensionality now introduces the scalar argument explicitly; zero multiplication uses the relevant map-zero law directly.
- Circle membership is reduced explicitly to membership in `Metric.sphere 0 1` and `mem_sphere_zero_iff_norm`.
- Integer powers use the actual `zpow_natCast` and `zpow_negSucc` APIs. The negative-index comparison relies only on definitional equality between `Int.negSucc n` and `-((n+1 : ℕ) : ℤ)`.
- Final cancellation names the nonzero factor as `eval z a`, avoiding the first pass's mismatch between this expression and its expanded coefficient sum.
- The usual pinned-Mathlib `backward.isDefEq.respectTransparency false` option permits the relevant definitional-coercion reductions; it does not add a logical assumption or bypass kernel checking.

No mathematical gap was identified in this source audit. The completed `all-02` pass accepted these API repairs for the recorded source hash. The convolution instances are globally registered on the transparent ℓ¹ abbreviation; no conflicting ℓ¹ ring instance was found in the inspected pinned `lpSpace` source (its existing multiplication/ring instances are for exponent infinity). This is a possible future instance-scope concern, not an identified conflict in the current pinned chapter.
