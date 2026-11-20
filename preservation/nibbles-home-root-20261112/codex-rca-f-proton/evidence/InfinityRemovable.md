# Removable singularity at infinity: proof evidence

Source node: Rudin RCA third edition, 13.1. Scratch source: `evidence/InfinityRemovable.lean`.

The statement takes a complex-valued function holomorphic on `{z | r < norm z}` and bounded there by a single real constant `M`. It concludes existence of `c` such that the function tends to `c` along `cocompact C`, and `Function.update (fun z => f z^(-1)) 0 c` is complex analytic at zero. It does not silently assert that Lean's totalized expression `f 0` equals the limiting value.

Proof route: inversion sends the punctured zero-neighborhood filter to the cobounded filter, so exterior holomorphy and the bound yield punctured holomorphy and boundedness of `g(z)=f(z^(-1))`. Apply `Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`; transfer the limit back to infinity by inversion; use `continuousAt_update_same` and `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` for the updated analytic extension.

The exact inversion lemmas used are `Filter.tendsto_inv₀_nhdsNE_zero` and `Filter.tendsto_inv₀_cobounded'`. The latter targets the punctured neighborhood, which avoids an unnecessary proof that an eventual inverse is nonzero.

Validation status: the first `lake env lean /home/derekblair/lane-work/codex-rca-f-proton/evidence/InfinityRemovable.lean` invocation completed with **exit 0** on 2026-10-29. Its entire diagnostic output is saved in `evidence/InfinityRemovable.check.log`: the theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Dependencies are pinned to Lean v4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. This scratch check is not a clean-slate chapter build.
