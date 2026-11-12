# Chapter 7.16(b): Cantor staircase preparation

Research checkpoint: 2026-10-29. No Lean compiler, dependency change, installation, vendoring, or external communication was performed for this investigation. This is a source/API plan, not a checked proof.

## Finding

No ready permissively licensed Lean proof of the complete singular-continuous staircase claim was located. The pinned Mathlib already supplies enough independent ingredients for a short probability-measure construction; this is the recommended route. It proves the actual counterexample: a continuous monotone real function with values 0 and 1 at the endpoints and derivative zero off a compact Lebesgue-null set. The arbitrary sequence of interval lengths in Rudin is one construction of this example, rather than a necessary hypothesis of the counterexample statement.

## Pinned-only construction

Mathlib pin: `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. The following names and statements were inspected in that source.

1. **The Cantor set and its coding map.** `Mathlib.Topology.Instances.CantorSet` defines `cantorSet`, proves `isCompact_cantorSet`, `isClosed_cantorSet`, `cantorSet_subset_unitInterval`, and `cantorSet_eq_union_halves`, and provides `cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (ℕ → Bool)`. Let `T ω := ((cantorSetHomeomorphNatToBool.symm) ω : ℝ)`. It is continuous and injective, with range exactly `cantorSet`. This avoids constructing or adapting an external staircase series.

2. **Fair-coin product.** In `Mathlib.Probability.Distributions.Bernoulli`, `ProbabilityTheory.bernoulliMeasure false true p` is a probability measure for `p : unitInterval`; set `p=⟨1/2, by norm_num⟩`. `bernoulliMeasure_apply` gives both singleton masses `1/2` by cases on the Boolean. In `Mathlib.Probability.ProductMeasure`, `Measure.infinitePi (fun _ : ℕ => fair)` has an `IsProbabilityMeasure` instance and `Measure.infinitePi_singleton` identifies each singleton mass with the infinite product of these masses.

3. **Product atomlessness.** Rewrite the product with `ENNReal.tprod_eq_iInf_prod` (all factors ≤1). For each `n`, `iInf_le` at `Finset.range n` bounds it by `(1/2)^n`. `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one` from `Mathlib.Analysis.SpecificLimits.Basic` and `le_of_tendsto` imply mass zero. The current class name is `MeasureTheory.NullSingletonClass` from `Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass`; `NoAtoms` is only a deprecated alias there. The obsolete `Typeclasses.NoAtoms` file itself supplies no import of the new class.

4. **Pushforward measure.** Put `ν := fairProduct.map T`. Continuity gives measurability, and the standard map probability instance applies. `Measure.map_apply` evaluates all Borel sets. For a singleton `{x}`, the preimage is subsingleton because `T` is injective; `Set.Subsingleton.preimage` and `Set.Subsingleton.measure_zero` prove `NullSingletonClass ν`. Also `ν cantorSetᶜ=0` since its preimage under `T` is empty. This is a complete finite probability measure construction in the existing Borel spaces; no additional choice of measure is assumed.

5. **Lebesgue-null support.** Let `v := volume cantorSet`, finite because the set is compact (or contained in `[0,1]`). Its self-similarity yields
   `v ≤ volume ((·/3) '' cantorSet) + volume ((fun x => (2+x)/3) '' cantorSet) = (2/3)*v`.
   `MeasureTheory.addHaar_smul` in `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` handles the factor `1/3`; `image_add_left` and `measure_preimage_add` handle translation. An alternative using narrower imports is `Real.volume_preimage_mul_left` in `Lebesgue.Basic`, rewriting each affine image as an affine preimage. Pass the finite ENNReal inequality to `toReal` and use linear arithmetic to obtain `v=0`. Disjointness of the halves is unnecessary.

6. **CDF continuity and monotonicity.** Set `F := ProbabilityTheory.cdf ν`. `Mathlib.Probability.CDF` supplies `monotone_cdf`, `cdf_eq_real`, `ofReal_cdf`, and `measure_cdf`. For continuity at `x`, `StieltjesFunction.measure_singleton` gives
   `0 = ENNReal.ofReal (F x - Function.leftLim F x)`.
   Monotonicity gives `leftLim F x ≤ F x`, hence equality. Apply `Monotone.continuousAt_iff_leftLim_eq_rightLim` and `StieltjesFunction.rightLim_eq`. These are in `MeasureTheory.Measure.Stieltjes` and `Topology.Order.LeftRightLim`. There is no need to assume differentiability or invoke any differentiation theorem to obtain continuity.

7. **Endpoints.** All values of `T` lie in `[0,1]`. Thus `ν (Iic 1)=1`; `ν (Iic 0)=0`, because its preimage under `T` is contained in the preimage of `{0}`, which is null. `ofReal_cdf`/`cdf_eq_real` give `F 0=0`, `F 1=1`. The same argument gives `F x=0` for `x≤0` and `F x=1` for `1≤x`.

8. **Zero derivative outside the Cantor set.** For `x∉cantorSet`, choose an open interval about `x` disjoint from the closed Cantor set. If `y` lies in a smaller such interval, then for every `ω`, `T ω≤x ↔ T ω≤y`: any failure places `T ω` in the interval. Therefore the preimages of `Iic x` and `Iic y` agree; `Measure.map_apply` and `cdf_eq_real` imply `F y=F x`. Use `hasDerivAt_const` and `HasDerivAt.congr_of_eventuallyEq` (`Mathlib.Analysis.Calculus.Deriv.Basic`). Since the exceptional compact set has volume zero, `HasDerivAt F 0 x` holds a.e.; its derivative is a.e. zero and integrable on `[0,1]`, yet the endpoint difference is one.

9. **Attached compact-null-set image claim.** The remark preceding 7.18 additionally says the example maps a compact null set onto `[0,1]`. Continuity and the endpoints first give each intermediate value at some `x∈[0,1]`. If `x∉cantorSet`, move to an endpoint of its complementary interval (equivalently, the maximal Cantor point ≤x, using compactness and `0∈cantorSet`); the CDF has the same value there because ν gives the intervening gap measure zero. This short additional lemma is still required for that attached claim and is not silently supplied by the a.e. derivative result.

## External source audit

### Principia Fractalis

Exact source: [FractalDevTeam/Principia-Fractalis, commit 4154d374591d6f211c07a8f343756ddb863e1c39](https://github.com/FractalDevTeam/Principia-Fractalis/tree/4154d374591d6f211c07a8f343756ddb863e1c39). Actual `PF_Lean4_Code/lean-toolchain` is Lean **4.24.0-rc1**, with Mathlib `eed770a434957369c6262aa3fb1d6426419016d4`. The root [license](https://github.com/FractalDevTeam/Principia-Fractalis/blob/4154d374591d6f211c07a8f343756ddb863e1c39/LICENSE) is a custom noncommercial research license, with same-license derivative terms and notification conditions. It is not a permissive software license; no source was copied into the worktree.

The source `PF_Lean4_Code/PF/CantorFunction_r207.lean` proves continuity, monotonicity, endpoint values, middle-third flatness, and an image/Hölder package. It does **not** state derivative zero a.e. Full non-Mathlib import closure:

| File | Lines | SHA-256 |
|---|---:|---|
| `PF/CantorFunction_r207.lean` | 689 | `db5fca0e9f6eb63bcaf51bb98786501c5f17a71bd5b1df655746eccb44a85745` |
| `PF/CantorDimension_r206.lean` | 246 | `3e59b9b87d70f0e99e4605aafbad8e5fde6a0f253f08dbee3bafdad8e1a90def` |
| `PF/HausdorffIFS_r205.lean` | 513 | `bc84b001b95472961f012c8096296063ac85f770600329f82b5d76bd53bc69c2` |

A comment-stripped token scan of all three files found no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `decide_cbv`, `reduceBool`, `reduceNat`, `bv_decide`, `run_tac`, `run_elab`, `Lean.ofReduce`, or ordinary `decide`. This is a source scan, not a kernel axiom audit or local build.

### Cantor Measure Frames

[jaumededios/Cantor_Measure_Frames](https://github.com/jaumededios/Cantor_Measure_Frames/tree/f9b80c7e9640bcd320707b84cffe86d672ed0409), exact commit `f9b80c7e9640bcd320707b84cffe86d672ed0409`, uses Lean 4.30.0/Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. Its measure module constructs a fair-coin pushforward and proves cylinder masses. No license file or repository license declaration was found, and no ready atomlessness/CDF staircase theorem was found in its proof modules. Its showcase intentionally contains a `sorry`; the companion imports proofs. We did not copy source or treat the showcase as a proof. A full closure trust scan is unnecessary because no source from this repository is proposed for reuse.

### Newer Mathlib

Latest inspected Mathlib tree: `f1a9649a26d5e38c8c835c901abee97c56cdfa78` (2026-10-29). Its paths contain Cantor set/scheme/cardinal files but no Cantor-staircase module. The cardinal/topological `cantorFunction` names refer to embeddings of binary sequences, not a real singular distribution function. Web searches for Lean Cantor function/staircase implementations found no additional usable complete theorem. This does not claim that every unindexed Lean repository was exhaustively searched.
