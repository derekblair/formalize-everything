# Chapter 9 interface contract (planning only until Chapter 8 gate passes)

All declarations will live in `RudinRCA.Chapter09`, and the final deliverable is
one module `RudinRCA/Chapter09.lean`. Authors develop fragments in lane/evidence;
root integrates them in dependency order. No new Lean code is claimed here.

Root owns 9.1–9.6 and the exact normalization bridge. Intended common definitions:

- `normalizationScale : ℝ := Real.sqrt (2 * Real.pi)`.
- `normalizationWeight : ℝ≥0∞ := ENNReal.ofReal normalizationScale⁻¹`.
- `rudinMeasure : Measure ℝ := normalizationWeight • volume`.
- `fourierTransform (f : ℝ → ℂ) (t : ℝ) := Fourier.fourierIntegral Real.probChar rudinMeasure f t`.
- `inverseFourierTransform (f : ℝ → ℂ) (x : ℝ) := fourierTransform f (-x)`.
- `convolution (f g : ℝ → ℂ) (x : ℝ) := ∫ y, f (x - y) * g y ∂rudinMeasure`.
- `translation (y : ℝ) (f : ℝ → ℂ) (x : ℝ) := f (x - y)`.

The generic library notation `𝓕` continues to mean Mathlib's volume transform;
never overload it to silently change normalization. A local notation for m is
fine inside a section, but exported theorem types must visibly use rudinMeasure.

Root supplies `normalizationScale_pos`, `normalizationScale_sq`, positive/finite
weight, the scaled-measure instances, integrability equivalence with volume,
`fourierTransform_eq_integral`, positive-sign inverse integral, continuity/norm
and C0 conclusions, exact same-coordinate and isometric-coordinate adapters,
convolution integrability/norm, and translation continuity. Exact theorem names
beyond the definitions will be finalized in the first root fragment.

The Lp pullback isometry is f(u) ↦ f(s*u), with s=normalizationScale and no
amplitude factor. Root will supply `normalizationLpEquiv` for p≥1 between
Lp(rudinMeasure) and Lp(volume). The L2 author defines `fourierL2` by conjugating
Mathlib's L2 Fourier isometry with this equivalence and proves the full L1∩L2
compatibility statement. No pointwise representative assumptions may be added.

Assignments after the Chapter 8 gate:

- root: 9.1–9.6, normalization, common definitions;
- chapter08_support: 9.7–9.10, exact Poisson kernel, two approximation results;
- chapter09_claims: 9.11–9.17, inversion/uniqueness, L2 transform and closed
  translation-invariant subspaces;
- printed_inventory: 9.18–9.23, nonunital Banach algebra examples, automatic
  continuity and classification of convolution characters.

Only one compiler runs in this lane. Build queues and fragment integration are
coordinated by root. All hypotheses needed from another fragment must be real
proved interfaces, never temporary axioms or sorry placeholders. Unsupported
proof text stays outside production until integrated source checks pass.
