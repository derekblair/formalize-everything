import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.LocallyFinsupp

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
