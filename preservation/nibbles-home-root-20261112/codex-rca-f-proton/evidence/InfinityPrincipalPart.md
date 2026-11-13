# Exact principal part at infinity: proof evidence

Source node: Rudin RCA third edition, 13.1, printed p. 267. Scratch source: `evidence/InfinityPrincipalPart.lean`.

The theorem `polynomial_principal_part_at_infinity_with_limit` assumes that `z -> f(z^(-1))` is meromorphic at zero and that its meromorphic order is exactly `-m`, where `m>0`. It produces a complex polynomial `p` with **`p.natDegree = m`** and **`p.coeff 0 = 0`**, plus a complex value `c`, such that:

- updating `z -> f(z^(-1)) - p.eval(z^(-1))` at zero to `c` makes it analytic at zero;
- `z -> f(z) - p.eval(z)` tends to `c` along `cocompact C`.

The proof uses `meromorphicOrderAt_eq_int_iff` to factor the inverse-coordinate germ as `z^(-m)*g(z)` with `g` analytic and `g(0)!=0`. Taylor expansion to order `m` produces the polynomial

`p(X) = sum_(i<m) monomial (m-i) (iteratedDeriv i g 0 / i!)`.

Three supporting theorems prove its exact degree, its zero constant coefficient, and the evaluation identity after multiplication by `z^m`. The coefficient of degree `m` is `g(0)`, so the degree conclusion is exact rather than a bound. The Taylor remainder gives the analytic extension; inversion transfers its punctured limit to infinity.

Validation: serialized command `flock /home/derekblair/lane-work/codex-rca-f-proton/evidence/lean-compile.lock lake env lean -j1 /home/derekblair/lane-work/codex-rca-f-proton/evidence/InfinityPrincipalPart.lean` completed with **exit 0** on 2026-10-29. The final compiler output is `evidence/InfinityPrincipalPart.check.log`; all five theorem-family axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`, or custom axioms in the source.

Pins: Lean v4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. This is a scratch compilation, not a clean-slate build of a chapter module. No chapter or clone files were modified by this subtask.
