# F1 normalization check

Checked before proof development on base
`653e691f67b3d48afacf3c153d6540f1e58ada9d`, branch
`f1-printed-bound-main`, initially clean working tree.

The base source establishes:

- `RudinRCA/Chapter04.lean:1244`: `FourierCircle = AddCircle (2 * Real.pi)`.
- `Chapter04.lean:1280`: `circleMeasure = AddCircle.haarAddCircle`.
- `Chapter04.lean:1288–1294`: `circleIntegral_interval` identifies integration
  against this measure with `(1/(2*pi))` times the integral on `[-pi,pi]`.
- `Chapter04.lean:1336–1337`: `trigMonomial n t = exp(i*n*t)`.
- `RudinRCA/Chapter05.lean:941–942`: `dirichletKernel N` sums the frequencies
  `-N,...,N`, with no shift in the kernel index.
- `Chapter05.lean:1059`: `lebesgueConstant N` integrates the kernel's complex norm
  against that normalized measure.
- `Chapter05.lean:1596–1604`: `dirichletL1_norm` proves that this is the L1 norm
  of the kernel's almost-everywhere equivalence class.
- `Chapter05.lean:1696–1706`: the existing sine quotient is
  `sin((N+1/2)*t)/sin(t/2)`; the value at zero is `2*N+1`.

Thus `lebesgueConstant N = (1/(2*pi))*integral_{-pi}^{pi}|D_N(t)| dt`, exactly
the normalized norm in the requested printed bound. There is no normalization
or kernel-index discrepancy.

## Provenance

[Coordinator's record on PR #48](https://github.com/derekblair/formalize-everything/pull/48#issuecomment-6557306253):
PR #48 merged on 2026-11-01 on an Argon crossed-review PASS. A separate
independent Codex hostile review completed with FAIL on blocking finding F1,
but its verdict did not reach the PR thread before the merge. The coordinator
subsequently posted the verdict, finding, and coverage gap. The Argon report
listed the 5.11 items without comparing the implemented coefficient to the
printed bound, so its PASS did not evaluate F1; the verdicts do not conflict
on F1 itself. This lane is the forward proof fix.
