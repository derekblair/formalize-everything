# Rudin RCA 13.11 logarithm and square-root implications

These scratch developments cover selected implications in the nine-condition
equivalence on printed pp. 274–275. They do **not** establish the entire node.
The printed list uses `(j)` for the square-root condition and skips `(i)`.

`HolomorphicLog.lean` develops five theorem families:

1. `differentiableAt_of_continuousAt_exp`: continuity of a logarithm lift and
   complex differentiability of its exponential imply complex differentiability
   of the lift. The proof uses a differentiable local inverse of the exponential
   and pulls its eventual left-inverse identity back along the continuous lift.
2. `holomorphic_of_continuous_log`: the corresponding open-set statement.
3. `exists_holomorphic_log_of_simply_connected`: **(b) implies (h)**. Mathlib's
   topological lifting theorem supplies a continuous logarithm on an open simply
   connected set; the preceding result supplies holomorphicity.
4. `exists_holomorphic_sqrt_of_holomorphic_log`: **(h) implies (j)** for every
   function to which the logarithm condition applies, using `exp(g/2)`.
5. `exists_holomorphic_sqrt_of_simply_connected`: the resulting **(b) implies
   (j)** statement.

`PrimitiveLog.lean` develops two theorem families:

1. `exists_holomorphic_log_of_primitive_logDeriv`: on an open connected set,
   a primitive of `f'/f` for a zero-free holomorphic function gives a
   holomorphic logarithm. Equality of logarithmic derivatives gives
   `f = c · exp(g)` with `c ≠ 0`; adding `log(c)` to `g` supplies the logarithm.
2. `primitives_imply_holomorphic_logarithms`: **(g) implies (h)**, with the
   universal primitive property explicitly assumed and applied to the
   holomorphic function `f'/f`.

The first file assumes `IsSimplyConnected Ω` and `IsOpen Ω` for the
simply-connected-domain assertions. The second only needs `IsPreconnected Ω`
and `IsOpen Ω`, because its hypothesis already supplies the required
primitive. Zero-freeness is explicit in each existence theorem that needs it.

All five families in `HolomorphicLog.lean` passed the parent lane's aggregate
check with only `propext`, `Classical.choice`, and `Quot.sound`; see
`all-pending-check-1.log` lines 262–272 and `all-pending-sources.json`.
`PrimitiveLog.lean` reached one elaboration error: the constant-function
differentiability theorem needed its explicit constant argument. That argument
has been supplied in the original source; its two families await a new check.
Neither source contains `sorry`, `admit`, or custom axioms. These are source
section checks, not chapter integration or clean-slate verification, and the
aggregate has diagnostics in other sections.
