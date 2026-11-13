# Rectangle Cauchy kernel: implementation in progress

`SquareKernel.lean` is an independent scratch implementation for the analytic
normalization needed by printed RCA 13.5. Its first aggregate check passed the
pointwise square-kernel algebra, scaling substitution, rectangle Goursat and
outside-zero formulas, boundary integrability, and boundary linearity helpers.
It reported errors in the unit-square integration rewrite, unspecified measures
in rectangle splitting, a minimum-positivity lemma name, and translation proof
elaboration. These have been corrected in the source; revalidation is pending.
The complete first output is `all-pending-check-1.log`. This document does not claim
that 13.5, or the draft kernel theorem, is complete.

The draft proves the following chain:

1. The sum of the four unit-square kernel integrands is
   `4 * I / (1 + t^2)`, for real `t`.
2. Its integral over `[-1,1]` is `2 * π * I`, by the real arctangent integral.
3. Affine substitution proves scale invariance, giving every centered square.
4. Rectangle boundary integrals split along horizontal and vertical cuts.
5. Given a rectangle containing zero, choose a smaller centered square.
   Cauchy–Goursat makes each of the four surrounding strips' kernel integrals
   zero. Cancellation then gives the kernel integral on the full rectangle.
6. Translation yields `rectangle_kernel_at` for every interior complex point.

The final drafted theorem has hypotheses `a < z.re < b` and `c < z.im < d`
and conclusion

```
rectangleIntegral (fun w => (w-z)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I
```

`rectangleIntegral` is the standard counterclockwise sum of four ordinary
interval integrals, in exactly the form used by Mathlib's rectangle
Cauchy–Goursat theorem. No winding-number or general polygon Cauchy theorem
is assumed.

The same scratch file now also drafts `rectangle_cauchy_formula`, applying
`Complex.differentiableOn_dslope` on the given open set Ω, rectangle
Cauchy–Goursat for the removable divided difference, and boundary-integral
linearity. Its hypotheses are that Ω is open, f is holomorphic on Ω,
the full closed rectangle lies in Ω, and z is an interior point. Its conclusion
is the counterclockwise boundary integral of `f(w)/(w-z)` equal to
`2 * π * I * f(z)`. Its proof elaborated in the first check, but its audit still
inherits failed helper proofs; it therefore awaits the corrected aggregate recheck.

The finite grid selection, cancellation of internal edges, and continuity
extension across grid lines remain separate requirements of printed 13.5.
