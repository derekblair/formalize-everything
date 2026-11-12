# Rudin 8.9(a): exact construction and statement map

Source: `evidence/Ch08BumpExample.lean`. Every declaration elaborated without errors in `evidence/Ch08BumpCombinedCheck.lean` check 2; `evidence/ch08-bump-combined-check2.log` contains no bump-fragment diagnostics. The combined command exited 1 solely because the separate maximal-constant limit fragment had errors; this is not yet a claim of a complete module build or final axiom audit.

The indexing starts at 0 instead of 1. Define `bumpDivision n = 1 - (1/2)^n`. `bumpDivision_zero`, `bumpDivision_strictMono`, and `bumpDivision_tendsto` provide the printed subdivision assumptions. `rudinBumpFunction n` is an explicit smooth bump centered halfway between successive subdivision points, with outer radius one quarter their gap and inner radius one eighth their gap, normalized by its Lebesgue integral.

| Printed claim | Declaration |
|---|---|
| Continuous real bumps, topological support in the assigned open intervals | `rudinBumpFunction_continuous`, `rudinBumpFunction_tsupport` |
| Each bump has integral 1 on [0,1] | `rudinBumpFunction_integral` |
| Exact displayed difference-series | `rudinBumpSeries` |
| At most one nonzero summand at each point | `rudinBumpSeries_unique_nonzero_term` |
| Both section integrals exist for every section | `rudinBumpSeries_sections_integrable` |
| Integrate in y first to obtain the first bump | `rudinBumpSeries_integral_right` |
| Integrate in x first to obtain zero | `rudinBumpSeries_integral_left` |
| Outer integrals exist, with values 1 and 0 | `rudin_bump_counterexample` |
| Continuous away from the exceptional corner | `rudinBumpSeries_continuousAt` |
| Actually discontinuous at the corner | `rudin_bump_not_continuousAt_corner` |
| Displayed iterated absolute integral equals infinity | `rudin_bump_absolute_iterated` |

Every one-dimensional integral uses `volume.restrict (Icc 0 1)`, so the unit-square domain is literal. The absolute integral is naturally valued in `ENNReal`; it is not a real-valued Bochner integral assigned an artificial infinity. The proof computes finite sums for each section and uses eventual local finite sums for continuity. Tonelli converts the infinite product absolute integral to the exact iterated form printed by Rudin.

No discrete substitute or existence hypothesis replaces the bump construction. The normalized bumps are constructed from Mathlib's `ContDiffBump`; the hypotheses required for their normalization are established by the real Lebesgue instances. The final impossibility of absolute integrability follows from the proved unequal iterated integrals and Fubini.
