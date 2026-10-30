import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Denumerable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.UniformSpace.HeineCantor
import RudinRCA.Chapter15

/- Generated scratch assembly; requires Chapter15 through 15.11.
Uncompiled source is not a Stage 2 result. -/

-- Source draft: MeromorphicQuotientWork.lean

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The removable-singularity step used in 15.12: a meromorphic function with
no negative orders has a holomorphic representative of its meromorphic class. -/
theorem holomorphic_regularization_of_nonnegative_orders {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hord : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ f =ᶠ[codiscreteWithin Ω] g := by
  refine ⟨toMeromorphicNFOn f Ω, ?_, toMeromorphicNFOn_eqOn_codiscrete hf⟩
  intro z hz
  apply ((meromorphicNFOn_toMeromorphicNFOn f Ω) hz)
    .meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hf hz]
  exact hord z hz

/-- Finite analytic orders exclude an identically zero component, so zeros may
be removed on a codiscrete set even when the domain is disconnected. -/
theorem holomorphic_nonzero_codiscrete {Ω : Set ℂ} {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g Ω) (hfinite : ∀ z ∈ Ω, analyticOrderAt g z ≠ ⊤) :
    ∀ᶠ z in codiscreteWithin Ω, g z ≠ 0 := by
  have hΩ : Ω ∈ codiscreteWithin Ω := by simp
  filter_upwards [hg.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top, hΩ] with z hz hzΩ
  exact (hg z hzΩ).analyticOrderAt_eq_zero.mp (hz.resolve_right (hfinite z hzΩ))

/-- The denominator assembly for 15.12. The remaining existence obligation is
to construct h with exactly the pole multiplicities, using 15.11. This helper
must not itself be counted as the numbered quotient theorem. -/
theorem meromorphic_quotient_of_canceling_denominator {Ω : Set ℂ} {f h : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (hfinite : ∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤)
    (hcancel : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z + meromorphicOrderAt h z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧
      f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z) := by
  have hprod : MeromorphicOn (f * h) Ω := hf.mul hh.meromorphicOn
  have hprodorder : ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt (f * h) z := by
    intro z hz
    rw [meromorphicOrderAt_mul (hf z hz) (hh z hz).meromorphicAt]
    exact hcancel z hz
  obtain ⟨g, hg, heq⟩ := holomorphic_regularization_of_nonnegative_orders hprod hprodorder
  refine ⟨g, hg, ?_⟩
  filter_upwards [heq, holomorphic_nonzero_codiscrete hh hfinite] with z hz hh0
  change f z * h z = g z at hz
  rw [← hz, mul_div_cancel_right₀ _ hh0]

/-- The converse accompanying 15.12. The standard meromorphic interpretation
ignores isolated arbitrary values at poles; componentwise nonvanishing gives
finite denominator orders and is retained explicitly as in the printed text. -/
theorem quotient_holomorphic_meromorphic {Ω : Set ℂ} {g h : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hh : DifferentiableOn ℂ h Ω)
    (hnonzero : ∀ z ∈ Ω, ∃ w ∈ connectedComponentIn Ω z, h w ≠ 0) :
    MeromorphicOn (fun z ↦ g z / h z) Ω ∧ ∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤ := by
  refine ⟨?_, fun z hz ↦ analyticOrderAt_ne_top_of_component_nonzero hΩ hh hnonzero hz⟩
  intro z hz
  exact ((hg.analyticOnNhd hΩ) z hz).meromorphicAt.div
    ((hh.analyticOnNhd hΩ) z hz).meromorphicAt

#print axioms holomorphic_regularization_of_nonnegative_orders
#print axioms holomorphic_nonzero_codiscrete
#print axioms meromorphic_quotient_of_canceling_denominator
#print axioms quotient_holomorphic_meromorphic

end RudinRCA.Chapter15

-- Source draft: MeromorphicPoleDataWork.lean

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The poles used as zero data for the denominator in 15.12. The divisor is
zero outside the domain and on locally identically-zero components. -/
def meromorphicPoleSet (f : ℂ → ℂ) (Ω : Set ℂ) : Set ℂ :=
  {z | MeromorphicOn.divisor f Ω z < 0}

/-- The positive pole order, extended by zero at all other points. -/
def meromorphicPoleMultiplicity (f : ℂ → ℂ) (Ω : Set ℂ) (z : ℂ) : ℕ :=
  (-MeromorphicOn.divisor f Ω z).toNat

theorem meromorphicPoleSet_subset_support (f : ℂ → ℂ) (Ω : Set ℂ) :
    meromorphicPoleSet f Ω ⊆ (MeromorphicOn.divisor f Ω).support := by
  intro z hz
  exact ne_of_lt hz

theorem meromorphicPoleSet_subset (f : ℂ → ℂ) (Ω : Set ℂ) :
    meromorphicPoleSet f Ω ⊆ Ω :=
  (meromorphicPoleSet_subset_support f Ω).trans
    (MeromorphicOn.divisor f Ω).supportWithinDomain

/-- Local finiteness is retained explicitly; mere discreteness would not exclude
an accumulation at another point of the domain. -/
theorem meromorphicPoleSet_locallyFinite (f : ℂ → ℂ) (Ω : Set ℂ) :
    ∀ z ∈ Ω, ∃ t ∈ 𝓝 z, (t ∩ meromorphicPoleSet f Ω).Finite := by
  intro z hz
  obtain ⟨t, ht, hfin⟩ := (MeromorphicOn.divisor f Ω).supportLocallyFiniteWithinDomain z hz
  exact ⟨t, ht, hfin.subset (inter_subset_inter_left _
    (meromorphicPoleSet_subset_support f Ω))⟩

/-- The precise no-interior-accumulation hypothesis required by 15.11. -/
theorem meromorphicPoleSet_no_accPt (f : ℂ → ℂ) (Ω : Set ℂ) :
    ∀ z ∈ Ω, ¬ AccPt z (𝓟 (meromorphicPoleSet f Ω)) := by
  have hcod : (meromorphicPoleSet f Ω)ᶜ ∈ codiscreteWithin Ω := by
    filter_upwards [(MeromorphicOn.divisor f Ω).eq_zero_codiscreteWithin] with z hz
    change ¬ MeromorphicOn.divisor f Ω z < 0
    change MeromorphicOn.divisor f Ω z = 0 at hz
    rw [hz]
    exact lt_irrefl 0
  have hset : Ω \ (meromorphicPoleSet f Ω)ᶜ = meromorphicPoleSet f Ω := by
    ext z
    simp only [mem_sdiff, mem_compl_iff, not_not]
    exact ⟨fun hz ↦ hz.2, fun hz ↦ ⟨meromorphicPoleSet_subset f Ω hz, hz⟩⟩
  simpa only [hset] using mem_codiscreteWithin_accPt.mp hcod

theorem meromorphicPoleMultiplicity_pos {f : ℂ → ℂ} {Ω : Set ℂ} {z : ℂ}
    (hz : z ∈ meromorphicPoleSet f Ω) : 0 < meromorphicPoleMultiplicity f Ω z := by
  exact Int.pos_iff_toNat_pos.mp (neg_pos.mpr hz)

theorem meromorphicPoleMultiplicity_eq_zero {f : ℂ → ℂ} {Ω : Set ℂ} {z : ℂ}
    (hz : z ∉ meromorphicPoleSet f Ω) : meromorphicPoleMultiplicity f Ω z = 0 := by
  apply Int.toNat_eq_zero.mpr
  exact neg_nonpos.mpr (le_of_not_gt hz)

/-- Outside the actual pole set, the meromorphic order is nonnegative, including
order infinity on an identically-zero component. -/
theorem meromorphicOrderAt_nonneg_of_not_pole {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) {z : ℂ} (hz : z ∈ Ω)
    (hpole : z ∉ meromorphicPoleSet f Ω) : 0 ≤ meromorphicOrderAt f z := by
  by_cases htop : meromorphicOrderAt f z = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hnonneg : 0 ≤ n := by
      have hd : MeromorphicOn.divisor f Ω z = n := by
        rw [hf.divisor_apply hz, ← hn]
        rfl
      change ¬ MeromorphicOn.divisor f Ω z < 0 at hpole
      rw [hd] at hpole
      exact le_of_not_gt hpole
    rw [← hn]
    exact_mod_cast hnonneg

/-- Zero-set data and the positive multiplicities supplied by 15.11 determine
the denominator order at every point, including nonpoles. -/
theorem denominator_order_of_pole_data {Ω : Set ℂ} {f h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h Ω)
    (hzeros : ∀ z ∈ Ω, h z = 0 ↔ z ∈ meromorphicPoleSet f Ω)
    (horders : ∀ z ∈ meromorphicPoleSet f Ω,
      analyticOrderAt h z = (meromorphicPoleMultiplicity f Ω z : ℕ∞)) :
    ∀ z ∈ Ω, analyticOrderAt h z = (meromorphicPoleMultiplicity f Ω z : ℕ∞) := by
  intro z hz
  by_cases hpole : z ∈ meromorphicPoleSet f Ω
  · exact horders z hpole
  · have hne : h z ≠ 0 := fun hzero ↦ hpole ((hzeros z hz).mp hzero)
    rw [(hh z hz).analyticOrderAt_eq_zero.mpr hne,
      meromorphicPoleMultiplicity_eq_zero hpole]
    simp

/-- The actual pole data cancels every negative order. No finite-order condition
is imposed on f: order infinity on an identically-zero component is allowed. -/
theorem nonnegative_order_of_pole_denominator {Ω : Set ℂ} {f h : ℂ → ℂ}
    (hf : MeromorphicOn f Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (horders : ∀ z ∈ Ω,
      analyticOrderAt h z = (meromorphicPoleMultiplicity f Ω z : ℕ∞)) :
    (∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤) ∧
      ∀ z ∈ Ω, 0 ≤ meromorphicOrderAt f z + meromorphicOrderAt h z := by
  refine ⟨fun z hz ↦ by simp [horders z hz], ?_⟩
  intro z hz
  rw [(hh z hz).meromorphicOrderAt_eq, horders z hz, ENat.map_natCast]
  by_cases htop : meromorphicOrderAt f z = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hd : MeromorphicOn.divisor f Ω z = n := by
      rw [hf.divisor_apply hz, ← hn]
      rfl
    rw [← hn]
    dsimp only [meromorphicPoleMultiplicity]
    rw [hd]
    have hnonneg : 0 ≤ n + ((-n).toNat : ℤ) := by omega
    exact_mod_cast hnonneg

#print axioms meromorphicPoleSet_subset_support
#print axioms meromorphicPoleSet_subset
#print axioms meromorphicPoleSet_locallyFinite
#print axioms meromorphicPoleSet_no_accPt
#print axioms meromorphicPoleMultiplicity_pos
#print axioms meromorphicPoleMultiplicity_eq_zero
#print axioms meromorphicOrderAt_nonneg_of_not_pole
#print axioms denominator_order_of_pole_data
#print axioms nonnegative_order_of_pole_denominator

end RudinRCA.Chapter15

-- Source draft: MeromorphicQuotientAssemblyWork.lean

/-!
Final 15.12 assembly against the planned Chapter15 interface. This file requires
the actual 15.11 existence theorem and the pole-data/quotient prerequisites to
have been integrated; no denominator-existence hypothesis is assumed here.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- Theorem 15.12 in Mathlib's meromorphic-class interpretation. A scalar-valued
`MeromorphicOn` function may have arbitrary isolated point values, so the identity
is initially stated as equality outside a codiscrete set. The denominator has
exactly the actual poles as its zeros and finite order everywhere. -/
theorem meromorphic_function_quotient {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicOn f Ω) :
    ∃ g h : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ AnalyticOnNhd ℂ h Ω ∧
      (∀ z ∈ Ω, h z = 0 ↔ z ∈ meromorphicPoleSet f Ω) ∧
      (∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤) ∧
      f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z) := by
  obtain ⟨h, hhol, hzeros, horders⟩ := prescribed_zeros_on_plane hΩ
    (meromorphicPoleSet_subset f Ω) (meromorphicPoleSet_no_accPt f Ω)
    (meromorphicPoleMultiplicity f Ω) (fun z hz ↦ meromorphicPoleMultiplicity_pos hz)
  have hhan : AnalyticOnNhd ℂ h Ω := hhol.analyticOnNhd hΩ
  have hall := denominator_order_of_pole_data hhan hzeros horders
  obtain ⟨hfinite, hcancel⟩ := nonnegative_order_of_pole_denominator hf hhan hall
  obtain ⟨g, hga, heq⟩ := meromorphic_quotient_of_canceling_denominator hf hhan hfinite hcancel
  exact ⟨g, h, hga, hhan, hzeros, hfinite, heq⟩

/-- At an analytic nonpole, equality of meromorphic classes is actual equality.
This supplies the printed identity on Ω minus its pole set. -/
theorem quotient_eq_at_of_codiscrete {Ω : Set ℂ} {f g h : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : AnalyticOnNhd ℂ g Ω) (hh : AnalyticOnNhd ℂ h Ω)
    (heq : f =ᶠ[codiscreteWithin Ω] (fun z ↦ g z / h z))
    {z : ℂ} (hz : z ∈ Ω) (hfz : AnalyticAt ℂ f z) (hhz : h z ≠ 0) :
    f z = g z / h z := by
  have hnear : f =ᶠ[𝓝[≠] z] (fun w ↦ g w / h w) := by
    have hlocal := eventuallyEq_codiscreteWithin_iff_forall_eventuallyEq_nhdsNE.mp heq z hz
    filter_upwards [hlocal, (hΩ.mem_nhds hz).filter_mono nhdsWithin_le_nhds] with w hw hwΩ
    exact hw hwΩ
  exact (hfz.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (((hg z hz).div (hh z hz) hhz).continuousAt)).mp hnear |>.eq_of_nhds

/-- The pointwise form of 15.12 for the normal-form representative of a
meromorphic function: f=g/h at every point outside its actual poles. This
convention removes Mathlib's arbitrary isolated values, not any mathematical
domain components. -/
theorem meromorphic_function_quotient_off_poles {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hf : MeromorphicNFOn f Ω) :
    ∃ g h : ℂ → ℂ, AnalyticOnNhd ℂ g Ω ∧ AnalyticOnNhd ℂ h Ω ∧
      (∀ z ∈ Ω, h z = 0 ↔ z ∈ meromorphicPoleSet f Ω) ∧
      (∀ z ∈ Ω, analyticOrderAt h z ≠ ⊤) ∧
      ∀ z ∈ Ω, z ∉ meromorphicPoleSet f Ω → f z = g z / h z := by
  obtain ⟨g, h, hg, hh, hzeros, hfinite, heq⟩ :=
    meromorphic_function_quotient hΩ hf.meromorphicOn
  refine ⟨g, h, hg, hh, hzeros, hfinite, ?_⟩
  intro z hz hpole
  have hfz : AnalyticAt ℂ f z :=
    (hf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (meromorphicOrderAt_nonneg_of_not_pole hf.meromorphicOn hz hpole)
  have hhz : h z ≠ 0 := fun hzero ↦ hpole ((hzeros z hz).mp hzero)
  exact quotient_eq_at_of_codiscrete hΩ hg hh heq hz hfz hhz

#print axioms meromorphic_function_quotient
#print axioms quotient_eq_at_of_codiscrete
#print axioms meromorphic_function_quotient_off_poles

end RudinRCA.Chapter15

-- Source draft: MittagLefflerKernelWork.lean

/-!
Explicit rational approximations for the Mittag-Leffler construction underlying
15.13. No Runge or Mittag-Leffler existence theorem is assumed. The finite
geometric expansion moves an approximate simple pole from a to the omitted
point b, with a uniform geometric error outside a controlled disc about b.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

def reciprocalExpansion (N : ℕ) (a b z : ℂ) : ℂ :=
  ∑ k ∈ range N, ((a - b) / (z - b)) ^ k / (z - b)

/-- Exact remainder after replacing a simple pole at a by poles at b. -/
theorem reciprocalExpansion_error (N : ℕ) (a b z : ℂ)
    (hza : z ≠ a) (hzb : z ≠ b) :
    1 / (z - a) - reciprocalExpansion N a b z =
      ((a - b) / (z - b)) ^ N / (z - a) := by
  induction N with
  | zero => simp [reciprocalExpansion]
  | succ N hN =>
    rw [reciprocalExpansion, sum_range_succ]
    change 1 / (z - a) - (reciprocalExpansion N a b z +
      ((a - b) / (z - b)) ^ N / (z - b)) = _
    rw [sub_add_eq_sub_sub, hN, pow_succ]
    field_simp [sub_ne_zero.mpr hza, sub_ne_zero.mpr hzb]
    ring

/-- Every approximant is analytic away from the chosen omitted point. -/
theorem analyticAt_reciprocalExpansion (N : ℕ) (a b : ℂ) {z : ℂ} (hzb : z ≠ b) :
    AnalyticAt ℂ (reciprocalExpansion N a b) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ ↦ w - b) z :=
    analyticAt_id.sub analyticAt_const
  exact Finset.analyticAt_fun_sum _ fun k _ ↦
    ((analyticAt_const.div hd (sub_ne_zero.mpr hzb)).pow k).div hd
      (sub_ne_zero.mpr hzb)

/-- On the exterior disc used by the construction, both the true pole and its
finite expansion stay a definite distance from their singularities. -/
theorem reciprocalExpansion_exterior_geometry {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    z ≠ a ∧ z ≠ b ∧ ‖a - b‖ ≤ ‖z - a‖ ∧
      ‖(a - b) / (z - b)‖ ≤ (1 / 2 : ℝ) := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hden : 0 < ‖z - b‖ := by linarith
  have htri : ‖z - b‖ ≤ ‖z - a‖ + ‖a - b‖ := by
    calc
      ‖z - b‖ = ‖(z - a) + (a - b)‖ := by congr 1; ring
      _ ≤ ‖z - a‖ + ‖a - b‖ := norm_add_le _ _
  have hdist : ‖a - b‖ ≤ ‖z - a‖ := by linarith
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp (hD.trans_le hdist)),
    sub_ne_zero.mp (norm_pos_iff.mp hden), hdist, ?_⟩
  rw [norm_div, div_le_iff₀ hden]
  linarith

theorem norm_reciprocalExpansion_error_le (N : ℕ) {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    ‖1 / (z - a) - reciprocalExpansion N a b z‖ ≤
      (1 / 2 : ℝ) ^ N / ‖a - b‖ := by
  obtain ⟨hza, hzb, hdist, hratio⟩ := reciprocalExpansion_exterior_geometry hab hz
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  rw [reciprocalExpansion_error N a b z hza hzb, norm_div, norm_pow]
  calc
    ‖(a - b) / (z - b)‖ ^ N / ‖z - a‖ ≤ (1 / 2 : ℝ) ^ N / ‖z - a‖ :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hratio N) (norm_nonneg _)
    _ ≤ (1 / 2 : ℝ) ^ N / ‖a - b‖ :=
      div_le_div_of_nonneg_left (pow_nonneg (by norm_num) _) hD hdist

/-- Uniform simple-pole approximation on the whole exterior region, rather than
only on a particular compact set. -/
theorem reciprocalExpansion_tendstoUniformlyOn {a b : ℂ} (hab : a ≠ b) :
    TendstoUniformlyOn (fun N z ↦ reciprocalExpansion N a b z)
      (fun z ↦ 1 / (z - a)) atTop {z : ℂ | 2 * ‖a - b‖ ≤ ‖z - b‖} := by
  have hlim : Tendsto (fun N : ℕ ↦ (1 / 2 : ℝ) ^ N / ‖a - b‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).div_const ‖a - b‖
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with N hN z hz
  rw [dist_eq_norm]
  exact (norm_reciprocalExpansion_error_le N hab hz).trans_lt hN

theorem reciprocalExpansion_uniform_bounds (N : ℕ) {a b z : ℂ} (hab : a ≠ b)
    (hz : 2 * ‖a - b‖ ≤ ‖z - b‖) :
    ‖1 / (z - a)‖ ≤ 2 / ‖a - b‖ ∧
      ‖reciprocalExpansion N a b z‖ ≤ 2 / ‖a - b‖ := by
  have hD : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hdist := (reciprocalExpansion_exterior_geometry hab hz).2.2.1
  have hinv : ‖1 / (z - a)‖ ≤ 1 / ‖a - b‖ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hD hdist
  have herr : ‖1 / (z - a) - reciprocalExpansion N a b z‖ ≤ 1 / ‖a - b‖ :=
    (norm_reciprocalExpansion_error_le N hab hz).trans
      (div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) hD.le)
  constructor
  · exact hinv.trans (div_le_div_of_nonneg_right (by norm_num) hD.le)
  · calc
      ‖reciprocalExpansion N a b z‖ =
          ‖(reciprocalExpansion N a b z - 1 / (z - a)) + 1 / (z - a)‖ := by
            congr 1; ring
      _ ≤ ‖reciprocalExpansion N a b z - 1 / (z - a)‖ + ‖1 / (z - a)‖ := norm_add_le _ _
      _ ≤ 1 / ‖a - b‖ + 1 / ‖a - b‖ := by
        rw [norm_sub_rev]
        exact add_le_add herr hinv
      _ = 2 / ‖a - b‖ := by ring

/-- Every finite principal-part polynomial has an arbitrarily accurate rational
approximation with poles only at b. This is the approximation step needed in the
direct Mittag-Leffler series; it does not assume a global approximation theorem. -/
theorem exists_polynomial_reciprocal_approximation (P : Polynomial ℂ)
    {a b : ℂ} (hab : a ≠ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z : ℂ, 2 * ‖a - b‖ ≤ ‖z - b‖ →
      ‖P.eval (1 / (z - a)) - P.eval (reciprocalExpansion N a b z)‖ < ε := by
  have huc : UniformContinuousOn P.eval (closedBall 0 (2 / ‖a - b‖)) :=
    (isCompact_closedBall (0 : ℂ) (2 / ‖a - b‖)).uniformContinuousOn_of_continuous P.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (reciprocalExpansion_tendstoUniformlyOn hab) δ hδ).exists
  refine ⟨N, fun z hz ↦ ?_⟩
  obtain ⟨htrue, happ⟩ := reciprocalExpansion_uniform_bounds N hab hz
  have htrue' : 1 / (z - a) ∈ closedBall 0 (2 / ‖a - b‖) := by
    simpa only [mem_closedBall, dist_zero_right] using htrue
  have happ' : reciprocalExpansion N a b z ∈ closedBall 0 (2 / ‖a - b‖) := by
    simpa only [mem_closedBall, dist_zero_right] using happ
  simpa only [dist_eq_norm] using hdist _ htrue' _ happ' (hN z hz)

#print axioms reciprocalExpansion_error
#print axioms analyticAt_reciprocalExpansion
#print axioms reciprocalExpansion_exterior_geometry
#print axioms norm_reciprocalExpansion_error_le
#print axioms reciprocalExpansion_tendstoUniformlyOn
#print axioms reciprocalExpansion_uniform_bounds
#print axioms exists_polynomial_reciprocal_approximation

end RudinRCA.Chapter15

-- Source draft: MittagLefflerSeriesWork.lean

/-!
Direct Mittag-Leffler construction on a normalized plane domain. The omitted
closed set is nonempty, and the poles have chosen boundary points whose distance
tends to zero. These geometric hypotheses are supplied by domain normalization;
no Mittag-Leffler or approximation existence theorem is assumed here.

Draft: all declarations in this file still await the serialized Lean check.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

/-- Finite principal-part polynomials preserve meromorphicity. -/
theorem meromorphicAt_polynomial_eval {f : ℂ → ℂ} {z : ℂ}
    (hf : MeromorphicAt f z) (P : Polynomial ℂ) :
    MeromorphicAt (fun w ↦ P.eval (f w)) z := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n c =>
    simpa only [Polynomial.eval_monomial] using (MeromorphicAt.const c z).mul (hf.pow n)

/-- A uniformly convergent complex series remains uniformly convergent after
removing an arbitrary finite prefix. -/
theorem uniformOn_complex_series_tail {S : Type*} {K : Set S}
    (u : ℕ → S → ℂ) (A : S → ℂ)
    (hconv : TendstoUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop K)
    (N : ℕ) :
    TendstoUniformlyOn (fun n s ↦ ∑ i ∈ range n, u (i + N) s)
      (fun s ↦ A s - ∑ i ∈ range N, u i s) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  have hshift := (tendsto_add_atTop_nat N).eventually
    (Metric.tendstoUniformlyOn_iff.1 hconv ε hε)
  filter_upwards [hshift] with n hn s hs
  have hsum : (∑ i ∈ range (n + N), u i s) =
      (∑ i ∈ range N, u i s) + ∑ i ∈ range n, u (i + N) s := by
    simpa [Nat.add_comm] using sum_range_add (fun i ↦ u i s) N n
  have hdist : dist (A s - ∑ i ∈ range N, u i s)
      (∑ i ∈ range n, u (i + N) s) =
      dist (A s) (∑ i ∈ range (n + N), u i s) := by
    rw [dist_eq_norm, dist_eq_norm, hsum]
    congr 1
    ring
  rw [hdist]
  exact hn s hs

theorem locallyUniform_complex_series_tail {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (u : ℕ → ℂ → ℂ) (A : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    (N : ℕ) :
    TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u (i + N) s)
      (fun s ↦ A s - ∑ i ∈ range N, u i s) atTop Ω := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).2
  intro K hKΩ hK
  exact uniformOn_complex_series_tail u A
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).1 hconv K hKΩ hK) N

/-- Uniform convergence and analyticity of all sufficiently late summands on a
neighborhood make the remainder after a finite prefix analytic there. -/
theorem analyticOnNhd_series_remainder {Ω V : Set ℂ}
    (hΩ : IsOpen Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω)
    {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    (N : ℕ) (hu : ∀ n, AnalyticOnNhd ℂ (u (n + N)) V) :
    AnalyticOnNhd ℂ (fun s ↦ A s - ∑ i ∈ range N, u i s) V := by
  have hlim := (locallyUniform_complex_series_tail hΩ u A hconv N).mono hVΩ
  apply (hlim.differentiableOn _ hV).analyticOnNhd hV
  exact Eventually.of_forall fun M ↦ DifferentiableOn.fun_sum
    fun n _ ↦ (hu n).differentiableOn

/-- Every compact part of the domain eventually lies in the exterior region
on which the explicit principal-part approximation is small. -/
theorem boundary_exteriors_contain_compacts (a b : ℕ → ℂ) {C K : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (hK : IsCompact K) (hKC : K ⊆ Cᶜ) :
    ∀ᶠ n in atTop, ∀ z ∈ K, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ := by
  obtain ⟨δ, hδ, hδK⟩ := compact_infDist_lower_bound hC hCne hK hKC
  filter_upwards [(tendsto_order.mp hsmall).2 (δ / 2) (half_pos hδ)] with n hn z hz
  have hden : δ ≤ ‖z - b n‖ :=
    (hδK z hz).trans (by simpa only [dist_eq_norm] using infDist_le_dist_of_mem (hb n))
  linarith

def correctedPrincipalPart (P : Polynomial ℂ) (N : ℕ) (a b z : ℂ) : ℂ :=
  P.eval (1 / (z - a)) - P.eval (reciprocalExpansion N a b z)

theorem correctedPrincipalPart_analyticAt (P : Polynomial ℂ) (N : ℕ)
    {a b z : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    AnalyticAt ℂ (correctedPrincipalPart P N a b) z := by
  have htrue : AnalyticAt ℂ (fun w : ℂ ↦ 1 / (w - a)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hza)
  exact (htrue.aeval_polynomial P).sub
    ((analyticAt_reciprocalExpansion N a b hzb).aeval_polynomial P)

theorem correctedPrincipalPart_meromorphicAt (P : Polynomial ℂ) (N : ℕ)
    (a b z : ℂ) : MeromorphicAt (correctedPrincipalPart P N a b) z := by
  have htrue : MeromorphicAt (fun w : ℂ ↦ 1 / (w - a)) z :=
    (MeromorphicAt.const 1 z).div ((MeromorphicAt.id z).sub (.const a z))
  have happ : MeromorphicAt (reciprocalExpansion N a b) z := by
    apply MeromorphicAt.fun_sum
    intro k _
    exact (((MeromorphicAt.const (a - b) z).div
      ((MeromorphicAt.id z).sub (.const b z))).pow k).div
        ((MeromorphicAt.id z).sub (.const b z))
  exact (meromorphicAt_polynomial_eval htrue P).sub
    (meromorphicAt_polynomial_eval happ P)

/-- The truncation orders are chosen from the proved geometric approximation,
and the resulting series converges locally uniformly on the whole domain. -/
theorem exists_locally_uniform_principal_part_series
    (P : ℕ → Polynomial ℂ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ N : ℕ → ℕ,
      (∀ n z, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
        ‖correctedPrincipalPart (P n) (N n) (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n) ∧
      TendstoLocallyUniformlyOn
        (fun M z ↦ ∑ n ∈ range M, correctedPrincipalPart (P n) (N n) (a n) (b n) z)
        (fun z ↦ ∑' n, correctedPrincipalPart (P n) (N n) (a n) (b n) z)
        atTop Cᶜ := by
  have hab : ∀ n, a n ≠ b n := fun n h ↦ ha n (h.symm ▸ hb n)
  have happrox : ∀ n, ∃ k : ℕ, ∀ z : ℂ, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
      ‖correctedPrincipalPart (P n) k (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n := by
    intro n
    exact exists_polynomial_reciprocal_approximation (P n) (hab n) (by positivity)
  choose N hN using happrox
  refine ⟨N, hN, (tendstoLocallyUniformlyOn_iff_forall_isCompact hC.isOpen_compl).2 ?_⟩
  intro K hKC hK
  apply tendstoUniformlyOn_tsum_nat_eventually
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [boundary_exteriors_contain_compacts a b hC hCne hb hsmall hK hKC]
    with n hn z hz
  exact (hN n z (hn z hz)).le

/-- Near any domain point all sufficiently late summands are analytic. The
finite prefix is allowed to contain actual poles. -/
theorem correctedPrincipalPart_eventually_analytic_near
    (P : ℕ → Polynomial ℂ) (N : ℕ → ℕ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    {z : ℂ} (hz : z ∉ C) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Cᶜ ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ
        (correctedPrincipalPart (P n) (N n) (a n) (b n)) V := by
  obtain ⟨K, ⟨hKz, hK⟩, hKC⟩ :=
    (compact_basis_nhds z).mem_iff.mp (hC.isOpen_compl.mem_nhds hz)
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKz,
    interior_subset.trans hKC, ?_⟩
  filter_upwards [boundary_exteriors_contain_compacts a b hC hCne hb hsmall hK hKC]
    with n hn w hw
  have hab : a n ≠ b n := fun h ↦ ha n (h.symm ▸ hb n)
  obtain ⟨hwa, hwb, _⟩ := reciprocalExpansion_exterior_geometry hab (hn w (interior_subset hw))
  exact correctedPrincipalPart_analyticAt (P n) (N n) hwa hwb

/-- A locally uniform series with an analytic tail and meromorphic summands
has a meromorphic sum. This retains the finite principal parts. -/
theorem meromorphicAt_of_locally_uniform_series
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (hu : ∀ n, MeromorphicAt (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) : MeromorphicAt A z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv N
    (fun n ↦ hN (n + N) (Nat.le_add_left N n)) z hzV
  have hprefix : MeromorphicAt (fun w ↦ ∑ n ∈ range N, u n w) z :=
    MeromorphicAt.fun_sum fun n _ ↦ hu n
  convert hrem.meromorphicAt.add hprefix using 1
  ext w
  exact (sub_add_cancel _ _).symm

/-- If all other summands are analytic at z, removing the selected summand
removes the whole principal part of the series there. -/
theorem analyticAt_of_locally_uniform_series
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (hu : ∀ n, AnalyticAt ℂ (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) : AnalyticAt ℂ A z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv N
    (fun n ↦ hN (n + N) (Nat.le_add_left N n)) z hzV
  have hprefix : AnalyticAt ℂ (fun w ↦ ∑ n ∈ range N, u n w) z :=
    Finset.analyticAt_fun_sum _ fun n _ ↦ hu n
  convert hrem.add hprefix using 1
  ext w
  exact (sub_add_cancel _ _).symm

/-- Removing one term from the sum preserves every other analytic germ. -/
theorem analyticAt_series_sub_term
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℕ → ℂ → ℂ} {A : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn (fun n s ↦ ∑ i ∈ range n, u i s) A atTop Ω)
    {z : ℂ} (j : ℕ) (hu : ∀ n, n ≠ j → AnalyticAt ℂ (u n) z)
    (htail : ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
      ∀ᶠ n in atTop, AnalyticOnNhd ℂ (u n) V) :
    AnalyticAt ℂ (fun w ↦ A w - u j w) z := by
  obtain ⟨V, hV, hzV, hVΩ, htail⟩ := htail
  obtain ⟨N, hN⟩ := eventually_atTop.1 htail
  let M := max N (j + 1)
  have hjM : j ∈ range M := mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _))
  have hrem := analyticOnNhd_series_remainder hΩ hV hVΩ hconv M
    (fun n ↦ hN (n + M) ((le_max_left _ _).trans (Nat.le_add_left M n))) z hzV
  have hprefix : AnalyticAt ℂ (fun w ↦ ∑ n ∈ (range M).erase j, u n w) z :=
    Finset.analyticAt_fun_sum _ fun n hn ↦ hu n (mem_erase.mp hn).1
  convert hrem.add hprefix using 1
  ext w
  have hsum := sum_erase_add (range M) (fun n ↦ u n w) hjM
  dsimp only
  rw [← hsum]
  ring

/-- The normalized Mittag-Leffler conclusion, including each prescribed
principal part. Injectivity says each distinct pole is listed once; arbitrary
finite pole order is stored in its polynomial. -/
theorem exists_normalized_mittag_leffler
    (P : ℕ → Polynomial ℂ) (a b : ℕ → ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCne : C.Nonempty) (ha : ∀ n, a n ∉ C)
    (hb : ∀ n, b n ∈ C) (hainj : Function.Injective a)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0)) :
    ∃ F : ℂ → ℂ, MeromorphicOn F Cᶜ ∧
      ∀ j, AnalyticAt ℂ (fun z ↦ F z - (P j).eval (1 / (z - a j))) (a j) := by
  obtain ⟨N, _, hconv⟩ :=
    exists_locally_uniform_principal_part_series P a b hC hCne ha hb hsmall
  let u := fun n z ↦ correctedPrincipalPart (P n) (N n) (a n) (b n) z
  let F := fun z ↦ ∑' n, u n z
  have htail := fun z hz ↦
    correctedPrincipalPart_eventually_analytic_near P N a b hC hCne ha hb hsmall (z := z) hz
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    exact meromorphicAt_of_locally_uniform_series hC.isOpen_compl hconv
      (fun n ↦ correctedPrincipalPart_meromorphicAt (P n) (N n) (a n) (b n) z)
      (htail z hz)
  · intro j
    have hother : ∀ n, n ≠ j → AnalyticAt ℂ (u n) (a j) := by
      intro n hnj
      exact correctedPrincipalPart_analyticAt (P n) (N n)
        (fun h ↦ hnj (hainj h.symm)) (fun h ↦ ha j (h.symm ▸ hb n))
    have hsub := analyticAt_series_sub_term hC.isOpen_compl hconv j hother (htail (a j) (ha j))
    have happ : AnalyticAt ℂ (fun z ↦ (P j).eval (reciprocalExpansion (N j) (a j) (b j) z))
        (a j) :=
      (analyticAt_reciprocalExpansion (N j) (a j) (b j)
        (fun h ↦ ha j (h.symm ▸ hb j))).aeval_polynomial (P j)
    convert hsub.sub happ using 1
    ext z
    dsimp [u, correctedPrincipalPart]
    ring

#print axioms meromorphicAt_polynomial_eval
#print axioms uniformOn_complex_series_tail
#print axioms locallyUniform_complex_series_tail
#print axioms analyticOnNhd_series_remainder
#print axioms boundary_exteriors_contain_compacts
#print axioms correctedPrincipalPart_analyticAt
#print axioms correctedPrincipalPart_meromorphicAt
#print axioms exists_locally_uniform_principal_part_series
#print axioms correctedPrincipalPart_eventually_analytic_near
#print axioms meromorphicAt_of_locally_uniform_series
#print axioms analyticAt_of_locally_uniform_series
#print axioms analyticAt_series_sub_term
#print axioms exists_normalized_mittag_leffler

end RudinRCA.Chapter15

-- Source draft: MittagLefflerInfinityWork.lean

/-!
The infinity chart of the explicit Mittag-Leffler series. This is required when
a point of the original domain is moved to infinity by normalization. Every
corrected summand has value zero in this chart at zero, and the same geometric
majorant proves normal convergence on a fixed chart disc.

Draft: awaiting the serialized Lean check.
-/

noncomputable section
open Filter Finset Set Metric
open scoped Topology

namespace RudinRCA.Chapter15

def reciprocalExpansionAtInfinity (N : ℕ) (a b w : ℂ) : ℂ :=
  ∑ k ∈ range N, ((a - b) * w / (1 - b * w)) ^ k * (w / (1 - b * w))

def correctedPrincipalPartAtInfinity (P : Polynomial ℂ) (N : ℕ) (a b w : ℂ) : ℂ :=
  P.eval (w / (1 - a * w)) - P.eval (reciprocalExpansionAtInfinity N a b w)

theorem reciprocal_at_infinity_eq {a w : ℂ} (hw : w ≠ 0) :
    w / (1 - a * w) = 1 / (1 / w - a) := by
  by_cases hd : 1 - a * w = 0
  · have hd' : 1 / w - a = 0 := by
      apply (mul_right_cancel₀ hw)
      field_simp [hw]
      linear_combination hd
    simp [hd, hd']
  · have hd' : 1 / w - a ≠ 0 := by
      intro h
      apply hd
      field_simp [hw] at h
      linear_combination h
    field_simp [hw, hd, hd']

theorem reciprocalExpansionAtInfinity_eq (N : ℕ) (a b : ℂ)
    {w : ℂ} (hw : w ≠ 0) :
    reciprocalExpansionAtInfinity N a b w = reciprocalExpansion N a b (1 / w) := by
  apply Finset.sum_congr rfl
  intro k _
  have hr : (a - b) * w / (1 - b * w) = (a - b) / (1 / w - b) := by
    calc
      (a - b) * w / (1 - b * w) = (a - b) * (w / (1 - b * w)) := by ring
      _ = (a - b) * (1 / (1 / w - b)) := by rw [reciprocal_at_infinity_eq hw]
      _ = (a - b) / (1 / w - b) := by ring
  rw [hr, reciprocal_at_infinity_eq hw]
  ring

theorem correctedPrincipalPartAtInfinity_eq (P : Polynomial ℂ) (N : ℕ)
    (a b : ℂ) {w : ℂ} (hw : w ≠ 0) :
    correctedPrincipalPartAtInfinity P N a b w =
      correctedPrincipalPart P N a b (1 / w) := by
  simp only [correctedPrincipalPartAtInfinity, correctedPrincipalPart,
    reciprocal_at_infinity_eq hw, reciprocalExpansionAtInfinity_eq N a b hw]

@[simp] theorem correctedPrincipalPartAtInfinity_zero
    (P : Polynomial ℂ) (N : ℕ) (a b : ℂ) :
    correctedPrincipalPartAtInfinity P N a b 0 = 0 := by
  simp [correctedPrincipalPartAtInfinity, reciprocalExpansionAtInfinity]

theorem correctedPrincipalPartAtInfinity_analyticAt (P : Polynomial ℂ) (N : ℕ)
    {a b w : ℂ} (ha : 1 - a * w ≠ 0) (hb : 1 - b * w ≠ 0) :
    AnalyticAt ℂ (correctedPrincipalPartAtInfinity P N a b) w := by
  have had : AnalyticAt ℂ (fun v : ℂ ↦ 1 - a * v) w :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hbd : AnalyticAt ℂ (fun v : ℂ ↦ 1 - b * v) w :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have htrue : AnalyticAt ℂ (fun v : ℂ ↦ v / (1 - a * v)) w := analyticAt_id.div had ha
  have happ : AnalyticAt ℂ (reciprocalExpansionAtInfinity N a b) w :=
    Finset.analyticAt_fun_sum _ fun k _ ↦
      (((analyticAt_const.mul analyticAt_id).div hbd hb).pow k).mul
        (analyticAt_id.div hbd hb)
  exact (htrue.aeval_polynomial P).sub (happ.aeval_polynomial P)

theorem infinity_exterior_of_small_difference {a b w : ℂ}
    (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1)
    (hden : (1 / 2 : ℝ) ≤ ‖1 - b * w‖) (hab : ‖a - b‖ ≤ 1 / 4) :
    2 * ‖a - b‖ ≤ ‖1 / w - b‖ := by
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have heq : 1 / w - b = (1 - b * w) / w := by field_simp [hw]
  rw [heq, norm_div, le_div_iff₀ hwp]
  have hprod : 2 * ‖a - b‖ * ‖w‖ ≤ 2 * (1 / 4 : ℝ) * 1 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hab (by norm_num)) hw1
      (norm_nonneg _) (by norm_num)
  linarith

/-- The corrected series is analytic in a full neighborhood of infinity. Its
chart value at zero is zero, which makes the normalization point removable. -/
theorem principal_part_series_analytic_at_infinity
    (P : ℕ → Polynomial ℂ) (N : ℕ → ℕ) (a b : ℕ → ℂ)
    (B : ℝ) (hB : 0 < B) (haB : ∀ n, ‖a n‖ ≤ B) (hbB : ∀ n, ‖b n‖ ≤ B)
    (hsmall : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0))
    (happrox : ∀ n z, 2 * ‖a n - b n‖ ≤ ‖z - b n‖ →
      ‖correctedPrincipalPart (P n) (N n) (a n) (b n) z‖ < (1 / 2 : ℝ) ^ n) :
    let G := fun w ↦ ∑' n, correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n) w
    AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ w, w ≠ 0 → G w = ∑' n, correctedPrincipalPart (P n) (N n) (a n) (b n) (1 / w) := by
  obtain ⟨ρa, hρa, hρa1, ha⟩ := exists_infinity_disc_denominator_lower_bound a B hB haB
  obtain ⟨ρb, hρb, hρb1, hb⟩ := exists_infinity_disc_denominator_lower_bound b B hB hbB
  let ρ := min ρa ρb
  have hρ : 0 < ρ := lt_min hρa hρb
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans hρa1
  have hbound : ∀ᶠ n in atTop, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ‖correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n) w‖ ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [(tendsto_order.mp hsmall).2 (1 / 4) (by norm_num)] with n hn w hw
    have hwρ : ‖w‖ ≤ ρ := by simpa only [mem_closedBall, dist_zero_right] using hw
    by_cases hw0 : w = 0
    · simp [hw0, pow_nonneg]
    · rw [correctedPrincipalPartAtInfinity_eq (P n) (N n) (a n) (b n) hw0]
      exact (happrox n (1 / w) (infinity_exterior_of_small_difference hw0 (hwρ.trans hρ1)
        (hb n w (hwρ.trans (min_le_right _ _))) hn.le)).le
  have hconv := tendstoUniformlyOn_tsum_nat_eventually
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) hbound
  have han : ∀ n, AnalyticOnNhd ℂ
      (correctedPrincipalPartAtInfinity (P n) (N n) (a n) (b n)) (ball 0 ρ) := by
    intro n w hw
    have hwρ : ‖w‖ ≤ ρ := (by simpa only [mem_ball, dist_zero_right] using hw : ‖w‖ < ρ).le
    apply correctedPrincipalPartAtInfinity_analyticAt
    · exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
        (ha n w (hwρ.trans (min_le_left _ _))))
    · exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
        (hb n w (hwρ.trans (min_le_right _ _))))
  have hhol := (hconv.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
    (Eventually.of_forall fun M ↦ DifferentiableOn.fun_sum
      fun n _ ↦ (han n).differentiableOn) isOpen_ball
  refine ⟨(hhol.analyticOnNhd isOpen_ball) 0 (mem_ball_self hρ), ?_, ?_⟩
  · simp
  · intro w hw
    exact tsum_congr fun n ↦ correctedPrincipalPartAtInfinity_eq (P n) (N n) (a n) (b n) hw

#print axioms reciprocal_at_infinity_eq
#print axioms reciprocalExpansionAtInfinity_eq
#print axioms correctedPrincipalPartAtInfinity_eq
#print axioms correctedPrincipalPartAtInfinity_zero
#print axioms correctedPrincipalPartAtInfinity_analyticAt
#print axioms infinity_exterior_of_small_difference
#print axioms principal_part_series_analytic_at_infinity

end RudinRCA.Chapter15

-- Source draft: MittagLefflerSetWork.lean

/-! Set-indexed normalized Mittag-Leffler construction, including finite and
empty sets and regularity at infinity. Draft awaiting a serialized Lean check. -/

noncomputable section
open Filter Set Finset Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def principalPartOnSphere (P : Polynomial ℂ) (a : ℂ) (p : ComplexSphere) : ℂ :=
  p.elim (P.eval 0) (fun z ↦ P.eval (1 / (z - a)))

theorem principalPartOnSphere_infinity_chart (P : Polynomial ℂ) (a : ℂ) :
    principalPartOnSphere P a ∘ sphereInfinityChart =
      fun w ↦ P.eval (w / (1 - a * w)) := by
  funext w
  by_cases hw : w = 0
  · subst w; simp [principalPartOnSphere]
  · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw, principalPartOnSphere,
      OnePoint.elim_some, ← one_div, ← reciprocal_at_infinity_eq hw]

theorem principalPartOnSphere_analytic_infinity (P : Polynomial ℂ) (a : ℂ) :
    SphereAnalyticAt (principalPartOnSphere P a) ∞ := by
  rw [sphereAnalyticAt_infty, principalPartOnSphere_infinity_chart]
  exact (analyticAt_id.div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)).aeval_polynomial P

/-- The normalized Mittag-Leffler theorem for a bounded discrete set. The
function is analytic at infinity and away from the specified finite poles. -/
theorem normalized_mittag_leffler_on_set {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S)) (P : S → Polynomial ℂ) :
    ∃ F : ComplexSphere → ℂ,
      MeromorphicOn (fun z ↦ F (↑z)) Cᶜ ∧
      SphereAnalyticAt F ∞ ∧
      (∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ F (↑w)) z) ∧
      ∀ a : S, AnalyticAt ℂ
        (fun z ↦ F (↑z) - (P a).eval (1 / (z - a))) a := by
  classical
  cases finite_or_infinite S with
  | inl hfinite =>
    letI := hfinite
    letI : Fintype S := Fintype.ofFinite S
    let F : ComplexSphere → ℂ := fun p ↦ ∑ a : S, principalPartOnSphere (P a) a p
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact MeromorphicAt.fun_sum fun a _ ↦ meromorphicAt_polynomial_eval
        ((MeromorphicAt.const 1 z).div ((MeromorphicAt.id z).sub (.const a z))) (P a)
    · change AnalyticAt ℂ (fun w ↦ ∑ a : S, principalPartOnSphere (P a) a (sphereInfinityChart w)) 0
      exact Finset.analyticAt_fun_sum _ fun a _ ↦ principalPartOnSphere_analytic_infinity (P a) a
    · intro z hz hzS
      apply Finset.analyticAt_fun_sum
      intro a _
      have hza : z ≠ a := fun h ↦ hzS (h.symm ▸ a.property)
      exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hza)).aeval_polynomial (P a)
    · intro a
      have hsum : AnalyticAt ℂ
          (fun z ↦ ∑ b ∈ (univ : Finset S).erase a, (P b).eval (1 / (z - b))) a := by
        apply Finset.analyticAt_fun_sum
        intro b hb
        have hab : (a : ℂ) ≠ b := fun h ↦ (mem_erase.mp hb).1 (Subtype.ext h).symm
        exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
          (sub_ne_zero.mpr hab)).aeval_polynomial (P b)
      convert hsum using 1
      ext z
      dsimp [F, principalPartOnSphere]
      exact (sub_eq_iff_eq_add).2 (sum_erase_add univ
        (fun b : S ↦ (P b).eval (1 / (z - b))) (mem_univ a)).symm
  | inr hinfinite =>
    letI := hinfinite
    haveI : Countable S := hScount.to_subtype
    let e : ℕ ≃ S := Classical.choice inferInstance
    let a : ℕ → ℂ := fun n ↦ e n
    have haS (n : ℕ) : a n ∈ S := (e n).property
    have ha (n : ℕ) : a n ∉ C := hS (haS n)
    have hainj : Function.Injective a := Subtype.val_injective.comp e.injective
    have hescape : ∀ K : Set ℂ, IsCompact K → K ⊆ Cᶜ →
        ∀ᶠ n in atTop, a n ∉ K := by
      intro K hK hKC
      have hSK := finite_inter_compact_of_no_accumulation hno hK hKC
      have hpre : (a ⁻¹' (S ∩ K)).Finite := hSK.preimage hainj.injOn
      have hpre' : {n : ℕ | a n ∈ K}.Finite := hpre.subset fun n hn ↦ ⟨haS n, hn⟩
      simpa only [Nat.cofinite_eq_atTop] using hpre'.eventually_cofinite_notMem
    choose b hb hnearest using (fun n ↦ hC.exists_infDist_eq_dist hCne (a n))
    obtain ⟨Ra, hRa, hbounda⟩ := hSbound.exists_pos_norm_le
    obtain ⟨Rb, hRb, hboundb⟩ := hC.isBounded.exists_pos_norm_le
    have hd := infDist_tendsto_zero_of_bounded_escape a C Ra
      (fun n ↦ hbounda (a n) (haS n)) hescape
    have hsmall := nearest_boundary_difference_tendsto_zero a b C hnearest hd
    let Q : ℕ → Polynomial ℂ := fun n ↦ P (e n)
    obtain ⟨N, happrox, hconv⟩ :=
      exists_locally_uniform_principal_part_series Q a b hC.isClosed hCne ha hb hsmall
    let u := fun n z ↦ correctedPrincipalPart (Q n) (N n) (a n) (b n) z
    let F : ComplexSphere → ℂ := fun p ↦ p.elim 0 (fun z ↦ ∑' n, u n z)
    have htail := fun z hz ↦ correctedPrincipalPart_eventually_analytic_near Q N a b
      hC.isClosed hCne ha hb hsmall (z := z) hz
    have hinfty := principal_part_series_analytic_at_infinity Q N a b (max Ra Rb)
      (hRa.trans_le (le_max_left _ _))
      (fun n ↦ (hbounda (a n) (haS n)).trans (le_max_left _ _))
      (fun n ↦ (hboundb (b n) (hb n)).trans (le_max_right _ _)) hsmall happrox
    refine ⟨F, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact meromorphicAt_of_locally_uniform_series hC.isClosed.isOpen_compl hconv
        (fun n ↦ correctedPrincipalPart_meromorphicAt (Q n) (N n) (a n) (b n) z)
        (htail z hz)
    · change AnalyticAt ℂ (F ∘ sphereInfinityChart) 0
      have heq : F ∘ sphereInfinityChart = fun w ↦
          ∑' n, correctedPrincipalPartAtInfinity (Q n) (N n) (a n) (b n) w := by
        funext w
        by_cases hw : w = 0
        · subst w; simp [F]
        · simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw, F, OnePoint.elim_some]
          simpa only [one_div] using (hinfty.2.2 w hw).symm
      rw [heq]
      exact hinfty.1
    · intro z hz hzS
      apply analyticAt_of_locally_uniform_series hC.isClosed.isOpen_compl hconv _ (htail z hz)
      intro n
      exact correctedPrincipalPart_analyticAt (Q n) (N n)
        (fun h ↦ hzS (h.symm ▸ haS n)) (fun h ↦ hz (h.symm ▸ hb n))
    · intro aj
      obtain ⟨j, rfl⟩ := e.surjective aj
      have hother : ∀ n, n ≠ j → AnalyticAt ℂ (u n) (a j) := by
        intro n hnj
        exact correctedPrincipalPart_analyticAt (Q n) (N n)
          (fun h ↦ hnj (hainj h.symm)) (fun h ↦ ha j (h.symm ▸ hb n))
      have hsub := analyticAt_series_sub_term hC.isClosed.isOpen_compl hconv j hother
        (htail (a j) (ha j))
      have happ : AnalyticAt ℂ (fun z ↦ (Q j).eval (reciprocalExpansion (N j) (a j) (b j) z))
          (a j) :=
        (analyticAt_reciprocalExpansion (N j) (a j) (b j)
          (fun h ↦ ha j (h.symm ▸ hb j))).aeval_polynomial (Q j)
      convert hsub.sub happ using 1
      ext z
      dsimp [F, u, Q, a, correctedPrincipalPart]
      ring

#print axioms principalPartOnSphere_infinity_chart
#print axioms principalPartOnSphere_analytic_infinity
#print axioms normalized_mittag_leffler_on_set

end RudinRCA.Chapter15

-- Source draft: InterpolationLocalWork.lean

/-!
Local algebra for 15.13. Taylor's theorem extracts the finite principal part of
an analytic germ divided by a finite-order analytic denominator. Realizing these
principal parts by the constructed Mittag-Leffler series then gives interpolation
after holomorphic regularization. No global interpolation premise is used here.

Draft: awaiting the serialized Lean check.
-/

noncomputable section
open Filter Finset Set
open scoped Topology

namespace RudinRCA.Chapter15

/-- The polynomial obtained by reversing the first k Taylor coefficients. -/
def reciprocalTaylorPolynomial (v : ℂ → ℂ) (k : ℕ) : Polynomial ℂ :=
  ∑ i ∈ range k, Polynomial.monomial (k - i) (iteratedDeriv i v 0 / i.factorial)

theorem reciprocalTaylorPolynomial_mul_pow (v : ℂ → ℂ) (k : ℕ)
    {x : ℂ} (hx : x ≠ 0) :
    x ^ k * (reciprocalTaylorPolynomial v k).eval (1 / x) =
      ∑ i ∈ range k, (x ^ i / i.factorial) * iteratedDeriv i v 0 := by
  simp only [reciprocalTaylorPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := (mem_range.mp hi).le
  have hp : x ^ k * (1 / x) ^ (k - i) = x ^ i := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero _ hx)]
    rw [← pow_add, Nat.add_sub_of_le hik]
  calc
    x ^ k * (iteratedDeriv i v 0 / i.factorial * (1 / x) ^ (k - i)) =
        (x ^ k * (1 / x) ^ (k - i)) * (iteratedDeriv i v 0 / i.factorial) := by ring
    _ = (x ^ i / i.factorial) * iteratedDeriv i v 0 := by rw [hp]; ring

/-- Every quotient of analytic germs by a finite-order denominator has a finite
polynomial principal part and an analytic remainder. Equality is on a punctured
neighborhood, so no arbitrary scalar value at the pole is misinterpreted. -/
theorem analytic_quotient_has_polynomial_principal_part
    {G h : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (hG : AnalyticAt ℂ G a) (hh : AnalyticAt ℂ h a)
    (horder : analyticOrderAt h a = (k : ℕ∞)) :
    ∃ P : Polynomial ℂ, ∃ R : ℂ → ℂ, AnalyticAt ℂ R a ∧
      (fun z ↦ G z / h z) =ᶠ[𝓝[≠] a]
        (fun z ↦ P.eval (1 / (z - a)) + R z) := by
  obtain ⟨u, hua, hua0, hhu⟩ := hh.analyticOrderAt_eq_natCast.mp horder
  let v : ℂ → ℂ := fun w ↦ G (w + a) / u (w + a)
  have hva : AnalyticAt ℂ v 0 := by
    exact (hG.div hua hua0).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
  obtain ⟨r, hra, hTaylor⟩ := hva.exists_eventuallyEq_sum_add_pow_mul k
  let R : ℂ → ℂ := fun z ↦ r (z - a)
  have hRa : AnalyticAt ℂ R a :=
    hra.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
  refine ⟨reciprocalTaylorPolynomial v k, R, hRa, ?_⟩
  have hTaylor' : ∀ᶠ z in 𝓝 a,
      G z / u z =
        (∑ i ∈ range k, ((z - a) ^ i / i.factorial) * iteratedDeriv i v 0) +
          (z - a) ^ k * R z := by
    have htrans : Tendsto (fun z : ℂ ↦ z - a) (𝓝 a) (𝓝 0) := by
      simpa using (continuousAt_id.sub_const a : ContinuousAt (fun z : ℂ ↦ z - a) a).tendsto
    simpa only [v, R, sub_add_cancel, smul_eq_mul] using htrans.eventually hTaylor
  filter_upwards [self_mem_nhdsWithin,
    hhu.filter_mono nhdsWithin_le_nhds,
    hTaylor'.filter_mono nhdsWithin_le_nhds,
    (hua.continuousAt.eventually_ne hua0).filter_mono nhdsWithin_le_nhds]
      with z hza hhz ht huz
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  change h z = (z - a) ^ k * u z at hhz
  have hhz0 : h z ≠ 0 := by rw [hhz]; exact mul_ne_zero (pow_ne_zero _ hza') huz
  have hv : G z / u z = (z - a) ^ k *
      ((reciprocalTaylorPolynomial v k).eval (1 / (z - a)) + R z) := by
    rw [mul_add, reciprocalTaylorPolynomial_mul_pow v k hza']
    exact ht
  apply (div_eq_iff hhz0).2
  rw [hhz, (div_eq_iff huz).1 hv]
  ring

/-- Normal-form regularization agrees in an ordinary neighborhood with any
analytic germ representing the same meromorphic function there. -/
theorem regularization_eq_analytic_germ {Ω : Set ℂ} {f V : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicOn f Ω) (ha : a ∈ Ω) (hV : AnalyticAt ℂ V a)
    (heq : f =ᶠ[𝓝[≠] a] V) :
    toMeromorphicNFOn f Ω =ᶠ[𝓝 a] V := by
  have h := (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf ha).trans
    (toMeromorphicNFAt_eventuallyEq_nhds_congr heq)
  rwa [toMeromorphicNFAt_eq_self.mpr hV.meromorphicNFAt] at h

/-- If M has the principal part of G/h, then regularizing h*M produces an
analytic germ whose error from G is divisible by h. This is the local step that
turns the actual Mittag-Leffler construction into arbitrary finite jets. -/
theorem interpolation_from_matching_principal_part
    {Ω : Set ℂ} {G h M : ℂ → ℂ} {a : ℂ} {k : ℕ}
    (ha : a ∈ Ω) (hG : AnalyticAt ℂ G a) (hh : AnalyticAt ℂ h a)
    (hprod : MeromorphicOn (fun z ↦ h z * M z) Ω)
    (horder : analyticOrderAt h a = (k : ℕ∞))
    (P : Polynomial ℂ) (R : ℂ → ℂ) (hR : AnalyticAt ℂ R a)
    (hprincipal : (fun z ↦ G z / h z) =ᶠ[𝓝[≠] a]
      (fun z ↦ P.eval (1 / (z - a)) + R z))
    (hM : AnalyticAt ℂ (fun z ↦ M z - P.eval (1 / (z - a))) a) :
    let H := toMeromorphicNFOn (fun z ↦ h z * M z) Ω
    AnalyticAt ℂ H a ∧
      (k : ℕ∞) ≤ analyticOrderAt (fun z ↦ H z - G z) a := by
  let D : ℂ → ℂ := fun z ↦ M z - P.eval (1 / (z - a)) - R z
  have hD : AnalyticAt ℂ D a := hM.sub hR
  let V : ℂ → ℂ := fun z ↦ G z + h z * D z
  have hV : AnalyticAt ℂ V a := hG.add (hh.mul hD)
  obtain ⟨u, hua, hua0, hhu⟩ := hh.analyticOrderAt_eq_natCast.mp horder
  have hnonzero : ∀ᶠ z in 𝓝[≠] a, h z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hhu.filter_mono nhdsWithin_le_nhds,
      (hua.continuousAt.eventually_ne hua0).filter_mono nhdsWithin_le_nhds]
      with z hza hhz huz
    simpa only [hhz, smul_eq_mul] using mul_ne_zero (pow_ne_zero k (sub_ne_zero.mpr hza)) huz
  have heq : (fun z ↦ h z * M z) =ᶠ[𝓝[≠] a] V := by
    filter_upwards [hprincipal, hnonzero] with z hz hhz
    have hGz := (div_eq_iff hhz).1 hz
    dsimp [V, D]
    rw [hGz]
    ring
  have hHV := regularization_eq_analytic_germ hprod ha hV heq
  have hH := hV.congr hHV.symm
  refine ⟨hH, (natCast_le_analyticOrderAt (hH.sub hG)).2 ?_⟩
  refine ⟨fun z ↦ u z * D z, hua.mul hD, ?_⟩
  filter_upwards [hHV, hhu] with z hz hhz
  rw [hz]
  dsimp only [V]
  rw [hhz]
  simp only [smul_eq_mul]
  ring

#print axioms reciprocalTaylorPolynomial_mul_pow
#print axioms analytic_quotient_has_polynomial_principal_part
#print axioms regularization_eq_analytic_germ
#print axioms interpolation_from_matching_principal_part

end RudinRCA.Chapter15

-- Source draft: NormalizedInterpolationWork.lean

/-!
Normalized interpolation on the complement of a compact plane set. All global
existence inputs are constructed: the prescribed zero function from 15.11 and
the explicit Mittag-Leffler series. Finite, empty, and infinite interpolation
sets use the same statement. Draft awaiting a serialized Lean check.
-/

noncomputable section
open Filter Set Metric Bornology
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

def sphereRegularization (f : ComplexSphere → ℂ) (C : Set ℂ)
    (p : ComplexSphere) : ℂ :=
  p.elim (f ∞) (toMeromorphicNFOn (fun z ↦ f (↑z)) Cᶜ)

@[simp] theorem sphereRegularization_coe (f : ComplexSphere → ℂ) (C : Set ℂ) (z : ℂ) :
    sphereRegularization f C (↑z) = toMeromorphicNFOn (fun w ↦ f (↑w)) Cᶜ z := rfl

@[simp] theorem sphereRegularization_infty (f : ComplexSphere → ℂ) (C : Set ℂ) :
    sphereRegularization f C ∞ = f ∞ := rfl

/-- Altering only a bounded set of finite-plane points leaves the analytic
germ at infinity unchanged. Here regularization changes only actual singular
points from the bounded set S. -/
theorem sphereRegularization_analytic_infinity {C S : Set ℂ}
    (hCbound : IsBounded C) (hSbound : IsBounded S) {f : ComplexSphere → ℂ}
    (hf : MeromorphicOn (fun z ↦ f (↑z)) Cᶜ)
    (hfin : ∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ f (↑w)) z)
    (hinfty : SphereAnalyticAt f ∞) : SphereAnalyticAt (sphereRegularization f C) ∞ := by
  obtain ⟨R, hR⟩ := (hCbound.union hSbound).exists_norm_le
  have hlim : Tendsto (fun w : ℂ ↦ ‖w⁻¹‖) (𝓝[≠] 0) atTop :=
    tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero
  have hlarge : ∀ᶠ w in 𝓝 0, w ≠ 0 → R < ‖w⁻¹‖ :=
    eventually_nhdsWithin_iff.mp (hlim.eventually (eventually_gt_atTop R))
  change AnalyticAt ℂ (f ∘ sphereInfinityChart) 0 at hinfty
  change AnalyticAt ℂ (sphereRegularization f C ∘ sphereInfinityChart) 0
  apply hinfty.congr
  filter_upwards [hlarge] with w hw
  by_cases hw0 : w = 0
  · subst w
    simp [Function.comp_def]
  · have hnot : w⁻¹ ∉ C ∪ S := fun h ↦ (not_le_of_gt (hw hw0)) (hR _ h)
    have hwC : w⁻¹ ∈ Cᶜ := fun h ↦ hnot (Or.inl h)
    have hwS : w⁻¹ ∉ S := fun h ↦ hnot (Or.inr h)
    simp only [Function.comp_def, sphereInfinityChart_of_ne_zero hw0, sphereRegularization_coe]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf hwC,
      toMeromorphicNFAt_eq_self.mpr (hfin _ hwC hwS).meromorphicNFAt]

/-- Exact finite-jet interpolation in the normalized domain, including its
infinity point. The order m counts the requested jets, so m=0 imposes no jet
condition. The construction uses a denominator of order m+1, which also covers
this edge case without deleting points from the data. -/
theorem normalized_interpolate_analytic_germs {C S : Set ℂ}
    (hC : IsCompact C) (hCne : C.Nonempty) (hS : S ⊆ Cᶜ)
    (hScount : S.Countable) (hSbound : IsBounded S)
    (hno : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S))
    (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ) (hG : ∀ a ∈ S, AnalyticAt ℂ (G a) a) :
    ∃ H : ComplexSphere → ℂ,
      SphereHolomorphicOn H (((↑) : ℂ → ComplexSphere) '' C)ᶜ ∧
      ∀ a ∈ S, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ H (↑z) - G a z) a := by
  classical
  obtain ⟨h, hh, _, hzeros, horder⟩ := normalized_prescribed_zeros
    hC hCne hS hScount hSbound hno (fun a ↦ m a + 1) (fun _ _ ↦ Nat.succ_pos _)
  have hhplane : AnalyticOnNhd ℂ (fun z ↦ h (↑z)) Cᶜ := by
    intro z hz
    exact hh (↑z) (by simpa only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe,
      exists_eq_right] using hz)
  have hparts : ∀ a : S, ∃ P : Polynomial ℂ, ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R a ∧
      (fun z ↦ G a z / h (↑z)) =ᶠ[𝓝[≠] (a : ℂ)]
        (fun z ↦ P.eval (1 / (z - a)) + R z) := by
    intro a
    exact analytic_quotient_has_polynomial_principal_part (hG a a.property)
      (hhplane a (hS a.property)) (horder a a.property)
  choose P R hR hprincipal using hparts
  obtain ⟨M, hM, hMinfty, hMoff, hMpart⟩ :=
    normalized_mittag_leffler_on_set hC hCne hS hScount hSbound hno P
  let f : ComplexSphere → ℂ := fun p ↦ h p * M p
  have hf : MeromorphicOn (fun z ↦ f (↑z)) Cᶜ := hhplane.meromorphicOn.mul hM
  have hfoff : ∀ z ∈ Cᶜ, z ∉ S → AnalyticAt ℂ (fun w ↦ f (↑w)) z :=
    fun z hz hzS ↦ (hhplane z hz).mul (hMoff z hz hzS)
  have hfinfty : SphereAnalyticAt f ∞ :=
    (hh ∞ (by simp)).mul hMinfty
  have hinterp : ∀ a : S,
      AnalyticAt ℂ (fun z ↦ sphereRegularization f C (↑z)) a ∧
      ((m a + 1 : ℕ) : ℕ∞) ≤
        analyticOrderAt (fun z ↦ sphereRegularization f C (↑z) - G a z) a := by
    intro a
    exact interpolation_from_matching_principal_part (hS a.property) (hG a a.property)
      (hhplane a (hS a.property)) hf (horder a a.property)
      (P a) (R a) (hR a) (hprincipal a) (hMpart a)
  refine ⟨sphereRegularization f C, ?_, ?_⟩
  · intro p hp
    induction p using OnePoint.rec with
    | infty =>
      exact sphereRegularization_analytic_infinity hC.isBounded hSbound hf hfoff hfinfty
    | coe z =>
      have hz : z ∈ Cᶜ := by
        simpa only [mem_compl_iff, mem_image, OnePoint.coe_eq_coe, exists_eq_right] using hp
      by_cases hzS : z ∈ S
      · exact (hinterp ⟨z, hzS⟩).1
      · have hgerm := regularization_eq_analytic_germ hf hz (hfoff z hz hzS) (EventuallyEq.rfl)
        exact (hfoff z hz hzS).congr hgerm.symm
  · intro a ha
    exact (show (m a : ℕ∞) ≤ ((m a + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.le_succ _).trans
      (hinterp ⟨a, ha⟩).2

#print axioms sphereRegularization_analytic_infinity
#print axioms sphereRegularization_coe
#print axioms sphereRegularization_infty
#print axioms normalized_interpolate_analytic_germs

end RudinRCA.Chapter15

-- Source draft: InterpolationWork.lean

/-!
Rudin 15.13: unrestricted finite jets on a discrete subset of an open plane
domain. The proof normalizes the domain, invokes the explicitly constructed
normalized interpolation theorem, and transports analytic order through the
sphere chart. No interpolation or Mittag-Leffler existence premise occurs in
the final statements. All source dependencies remain drafts awaiting checks.
-/

noncomputable section
open Filter Set Finset
open scoped Topology OnePoint

namespace RudinRCA.Chapter15

/-- A chart-invariant interpolation statement. It is useful for transport; the
printed plane-domain derivative formulation is given below. -/
theorem sphere_interpolate_analytic_germs {Ω A : Set ComplexSphere}
    (hΩ : IsOpen Ω) (hproper : Ω ≠ univ) (hA : A ⊆ Ω)
    (hno : NoAccumulationIn A Ω)
    (m : ComplexSphere → ℕ) (G : ComplexSphere → ComplexSphere → ℂ)
    (hG : ∀ a ∈ A, SphereAnalyticAt (G a) a) :
    ∃ H : ComplexSphere → ℂ, SphereHolomorphicOn H Ω ∧
      ∀ a ∈ A, (m a : ℕ∞) ≤ sphereAnalyticOrderAt (fun z ↦ H z - G a z) a := by
  classical
  rcases Ω.eq_empty_or_nonempty with hΩempty | hΩne
  · refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · intro a ha; exfalso; simpa only [hΩempty, mem_empty_iff_false] using ha
    · intro a ha; exfalso; simpa only [hΩempty, mem_empty_iff_false] using hA ha
  obtain ⟨pole, hpole, hpoleA⟩ := exists_domain_point_outside_zeros hΩ hΩne hno
  let C : Set ℂ := (spherePlaneParam pole ⁻¹' Ω)ᶜ
  let S : Set ℂ := spherePlaneParam pole ⁻¹' A
  let m' : ℂ → ℕ := fun z ↦ m (spherePlaneParam pole z)
  let G' : ℂ → ℂ → ℂ := fun a z ↦ G (spherePlaneParam pole a) (spherePlaneParam pole z)
  have hC : IsCompact C := normalized_complement_isCompact hΩ hpole
  have hCne : C.Nonempty := normalized_complement_nonempty hproper hpole
  have hS : S ⊆ Cᶜ := fun z hz ↦ not_not.mpr (hA hz)
  have hScount : S.Countable := normalized_zeros_countable hA hno pole
  have hSbound := normalized_zeros_isBounded hno hpole hpoleA
  have hno' : ∀ z ∈ Cᶜ, ¬ AccPt z (𝓟 S) :=
    fun z hz ↦ normalized_zeros_no_accumulation hno pole z (not_not.mp hz)
  have hG' : ∀ a ∈ S, AnalyticAt ℂ (G' a) a := by
    intro a ha
    exact (sphereAnalyticAt_iff_planeParam (G (spherePlaneParam pole a)) pole a).1
      (hG (spherePlaneParam pole a) ha)
  obtain ⟨H', hH', hjet⟩ :=
    normalized_interpolate_analytic_germs hC hCne hS hScount hSbound hno' m' G' hG'
  let H : ComplexSphere → ℂ := H' ∘ spherePoleChart pole
  have hdom : (((↑) : ℂ → ComplexSphere) '' C)ᶜ =
      (spherePoleChart pole).symm ⁻¹' Ω := normalized_domain_eq hpole
  refine ⟨H, ?_, ?_⟩
  · intro p hp
    apply (sphereAnalyticAt_comp_poleChart_iff H' pole p).2
    apply hH'
    rw [hdom]
    simpa using hp
  · intro p hp
    have hpp : p ≠ pole := fun h ↦ hpoleA (h ▸ hp)
    have hr : p ∈ range (spherePlaneParam pole) := by
      rw [range_spherePlaneParam]
      exact hpp
    obtain ⟨z, rfl⟩ := hr
    rw [sphereAnalyticOrderAt_planeParam]
    simpa only [H, G', m', Function.comp_def, spherePlaneParam,
      Homeomorph.apply_symm_apply] using hjet z hp

/-- Exact interpolation of analytic germs to arbitrary finite order on an
arbitrary open plane domain, including disconnected domains and empty data. -/
theorem interpolate_analytic_germs {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ a ∈ Ω, ¬ AccPt a (𝓟 A))
    (m : ℂ → ℕ) (G : ℂ → ℂ → ℂ) (hG : ∀ a ∈ A, AnalyticAt ℂ (G a) a) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F Ω ∧
      ∀ a ∈ A, (m a : ℕ∞) ≤ analyticOrderAt (fun z ↦ F z - G a z) a := by
  let Ωs : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' Ω
  let As : Set ComplexSphere := ((↑) : ℂ → ComplexSphere) '' A
  let ms : ComplexSphere → ℕ := fun p ↦ p.elim 0 m
  let Gs : ComplexSphere → ComplexSphere → ℂ := fun p ↦
    p.elim (fun _ ↦ 0) (fun a q ↦ q.elim 0 (G a))
  have hΩs : IsOpen Ωs := OnePoint.isOpen_image_coe.2 hΩ
  have hproper : Ωs ≠ univ := by
    intro h
    have hin : (∞ : ComplexSphere) ∈ Ωs := by rw [h]; trivial
    exact OnePoint.infty_notMem_image_coe hin
  have hAs : As ⊆ Ωs := image_mono hA
  have hnos : NoAccumulationIn As Ωs := by
    rintro p ⟨z, hz, rfl⟩ hacc
    have hacc' := OnePoint.isOpenEmbedding_coe.accPt_comap_iff.mpr hacc
    apply hno z hz
    simpa only [comap_principal, As, preimage_image_eq _ OnePoint.coe_injective] using hacc'
  have hGs : ∀ a ∈ As, SphereAnalyticAt (Gs a) a := by
    rintro p ⟨a, ha, rfl⟩
    exact hG a ha
  obtain ⟨F, hF, hjet⟩ := sphere_interpolate_analytic_germs hΩs hproper hAs hnos ms Gs hGs
  exact ⟨fun z ↦ F (↑z), fun z hz ↦ hF (↑z) ⟨z, hz, rfl⟩,
    fun a ha ↦ hjet (↑a) ⟨a, ha, rfl⟩⟩

def prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ) (a z : ℂ) : ℂ :=
  ∑ i ∈ range (m + 1), (z - a) ^ i * w i

theorem analyticAt_prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ) (a z : ℂ) :
    AnalyticAt ℂ (prescribedJetPolynomial m w a) z := by
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((analyticAt_id.sub analyticAt_const).pow i).mul analyticAt_const

theorem iteratedDeriv_prescribedJetPolynomial (m : ℕ) (w : ℕ → ℂ)
    (a : ℂ) {k : ℕ} (hk : k ≤ m) :
    iteratedDeriv k (prescribedJetPolynomial m w a) a = (k.factorial : ℂ) * w k := by
  change iteratedDeriv k
    (fun z ↦ (fun v : ℂ ↦ ∑ i ∈ range (m + 1), v ^ i * w i) (z - a)) a = _
  rw [iteratedDeriv_comp_sub_const, sub_self]
  rw [iteratedDeriv_fun_sum (fun i _ ↦ by fun_prop)]
  simp only [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero, ite_mul, zero_mul]
  exact sum_ite_eq_of_mem _ _ _ (mem_range.mpr (Nat.lt_succ_of_le hk))

/-- Rudin 15.13 in the printed derivative convention: the data w_(n,a) are
Taylor coefficients, so the prescribed nth derivative is n! * w_(n,a), for all
0 ≤ n ≤ m(a). No boundedness or growth restriction is imposed on those data. -/
theorem interpolate_prescribed_derivative_jets {Ω A : Set ℂ}
    (hΩ : IsOpen Ω) (hA : A ⊆ Ω)
    (hno : ∀ a ∈ Ω, ¬ AccPt a (𝓟 A))
    (m : ℂ → ℕ) (w : ℂ → ℕ → ℂ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      ∀ a ∈ A, ∀ n ≤ m a, iteratedDeriv n F a = (n.factorial : ℂ) * w a n := by
  let G : ℂ → ℂ → ℂ := fun a ↦ prescribedJetPolynomial (m a) (w a) a
  have hG : ∀ a ∈ A, AnalyticAt ℂ (G a) a :=
    fun a _ ↦ analyticAt_prescribedJetPolynomial (m a) (w a) a a
  obtain ⟨F, hF, hjet⟩ := interpolate_analytic_germs hΩ hA hno (fun a ↦ m a + 1) G hG
  refine ⟨F, hF.differentiableOn, ?_⟩
  intro a ha n hn
  have hFa : AnalyticAt ℂ F a := hF a (hA ha)
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFa.sub (hG a ha))).1
    (hjet a ha) n (Nat.lt_succ_of_le hn)
  rw [iteratedDeriv_fun_sub hFa.contDiffAt (hG a ha).contDiffAt] at hz
  exact (sub_eq_zero.mp hz).trans (iteratedDeriv_prescribedJetPolynomial (m a) (w a) a hn)

#print axioms sphere_interpolate_analytic_germs
#print axioms interpolate_analytic_germs
#print axioms analyticAt_prescribedJetPolynomial
#print axioms iteratedDeriv_prescribedJetPolynomial
#print axioms interpolate_prescribed_derivative_jets

end RudinRCA.Chapter15
