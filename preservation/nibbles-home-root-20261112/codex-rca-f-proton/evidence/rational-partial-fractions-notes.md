# Rudin RCA 13.2 implementation evidence

Printed source: Walter Rudin, *Real and Complex Analysis*, third edition, p. 267,
node 13.2 (PDF page 280 in `source-rudin.pdf`). The node is an exposition block,
not a numbered theorem. Its mathematical claims are reduced rational
representations, poles at denominator zeros with the corresponding
multiplicities, and partial fractions with polynomial principal parts in
reciprocal linear factors.

Development file: `RationalPartialFractions.lean`, namespace
`RudinRCA.Chapter13`. This is lane evidence outside the chapter module.

## Coverage

| Declaration | Mathematical content |
| --- | --- |
| `rational_reduced_representation` | Every element of the complex rational-function field has a monic nonzero denominator, a coprime numerator, and the resulting quotient represents that element. |
| `rational_partial_fractions_coefficients` | Linear-factor partial fractions in the rational-function field, with complex scalar coefficients and inverse powers bounded by the corresponding denominator-root multiplicities. |
| `rational_partial_fractions_polynomials` | Grouped field identity with polynomials `A a` satisfying `(A a).coeff 0 = 0`. The finite pole set is the set of distinct roots of the reduced denominator. |
| `linear_partial_fractions_in_algebra` | Supporting specialization of Mathlib's partial-fractions theorem to linear denominators in a polynomial algebra containing their inverses. |
| `rational_partial_fractions_with_evaluation` | One fixed collection of polynomials gives both the field identity and the pointwise formula at every point where the reduced denominator is nonzero. |
| `rational_principal_part_remainder` | At each denominator root, subtracting its grouped summand leaves a punctured germ that extends analytically across the root. This identifies the summand as its principal part. |
| `rational_quotient_evaluation` | For arbitrary polynomials `P,Q`, the reduced representative of `P/Q` has the same pointwise value wherever the original denominator is nonzero; its reduced denominator is also nonzero there. |
| `polynomial_meromorphic_order` | For a nonzero polynomial, analytic meromorphic order equals algebraic root multiplicity. |
| `rational_pole_order` | At each zero of the reduced denominator, the quotient's meromorphic order is the negative of that zero's multiplicity. |
| `rational_tendsto_cobounded_at_pole` | Every reduced-denominator root is an actual pole: along its punctured neighborhood the quotient leaves every bounded subset of the complex plane. |
| `rational_differentiableAt_of_denom_ne_zero` | The quotient is complex differentiable at every point outside the denominator's zero set. |

The pointwise theorem restricts to nonzero denominator values. It does not use
Lean's totalized inverse at a pole as a mathematical value of the rational
function. Its proof specializes the algebraic identity once to a product
algebra: the rational-function field together with functions on the complement
of the denominator's zero set. The polynomial coefficients are consequently
the same for the field identity and for every permitted evaluation point.

The implementation uses Mathlib's general partial-fractions theorem and proves
that every remainder modulo a linear polynomial is constant. Splitting of
complex polynomials supplies the denominator factorization. Exact pole order
uses coprimeness to exclude a numerator zero at a denominator root.

Behavior at infinity belongs to the separately implemented node 13.1. The
formula in 13.2 already supplies a polynomial remainder after the finite
principal parts are removed.

## Verification state

All eleven listed families passed in the parent lane's aggregate check, with
only `propext`, `Classical.choice`, and `Quot.sound`. Evidence:
`all-pending-check-1.log`, lines 3–17, mapped to the unchanged source by
`all-pending-sources.json`; source SHA-256
`0a135732f17de70e3449a114169e1b7ea24b7f9f0a4f1d6d84c094795002090f`.
The aggregate has diagnostics in other source sections, so this is a verified
section and axiom-audit result, not a claim that the aggregate exited zero.
The earlier standalone waiter was deliberately superseded by this aggregate
to share import loading under host memory pressure. No source `sorry`, `admit`,
or custom axiom is present.

The scratch-file check is not a chapter clean-slate build or an integration
claim. Those gates remain the parent lane's responsibility.
