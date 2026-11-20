import RudinRCA.Chapter13

open Set

namespace RudinRCA.Chapter13

private theorem strip_component_avoids_half {z w : ℂ}
    (hw : w ∈ connectedComponentIn horizontalStripᶜ z) : w.im ≠ 1 / 2 := by
  have hn := connectedComponentIn_subset horizontalStripᶜ z hw
  change ¬ (0 < w.im ∧ w.im < 1) at hn
  intro heq
  apply hn
  constructor <;> linarith

theorem strip_component_lower {z : ℂ} (hz : z.im ≤ 0) :
    connectedComponentIn horizontalStripᶜ z = {w : ℂ | w.im ≤ 0} := by
  have hzout : z ∈ horizontalStripᶜ := fun h => (not_lt_of_ge hz) h.1
  apply Subset.antisymm
  · intro w hw
    have hside := isPreconnected_connectedComponentIn.gt_of_ne
      Complex.continuous_im.continuousOn
      (fun w hw => strip_component_avoids_half hw)
      ⟨z, mem_connectedComponentIn hzout, by linarith⟩ hw
    have hn := connectedComponentIn_subset horizontalStripᶜ z hw
    change ¬ (0 < w.im ∧ w.im < 1) at hn
    by_contra hpos
    apply hn
    exact ⟨lt_of_not_ge hpos, by linarith⟩
  · exact (convex_halfSpace_le (.mk Complex.add_im Complex.smul_im) 0).isPreconnected
      |>.subset_connectedComponentIn hz (fun w hw h => (not_lt_of_ge hw) h.1)

theorem strip_component_upper {z : ℂ} (hz : 1 ≤ z.im) :
    connectedComponentIn horizontalStripᶜ z = {w : ℂ | 1 ≤ w.im} := by
  have hzout : z ∈ horizontalStripᶜ := fun h => (not_lt_of_ge hz) h.2
  apply Subset.antisymm
  · intro w hw
    have hside := isPreconnected_connectedComponentIn.lt_of_ne
      Complex.continuous_im.continuousOn
      (fun w hw => strip_component_avoids_half hw)
      ⟨z, mem_connectedComponentIn hzout, by linarith⟩ hw
    have hn := connectedComponentIn_subset horizontalStripᶜ z hw
    change ¬ (0 < w.im ∧ w.im < 1) at hn
    by_contra hlt
    apply hn
    exact ⟨by linarith, lt_of_not_ge hlt⟩
  · exact (convex_halfSpace_ge (.mk Complex.add_im Complex.smul_im) 1).isPreconnected
      |>.subset_connectedComponentIn hz (fun w hw h => (not_lt_of_ge hw) h.2)

/-- The planar complement has exactly the two closed half-plane components. -/
theorem horizontalStrip_components :
    {s : Set ℂ | ∃ z ∈ horizontalStripᶜ, s = connectedComponentIn horizontalStripᶜ z} =
      {{w : ℂ | w.im ≤ 0}, {w : ℂ | 1 ≤ w.im}} := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ¬ (0 < z.im ∧ z.im < 1) at hz
    by_cases hlow : z.im ≤ 0
    · simp [strip_component_lower hlow]
    · have hhigh : 1 ≤ z.im := le_of_not_gt (fun h => hz ⟨lt_of_not_ge hlow, h⟩)
      simp [strip_component_upper hhigh]
  · intro hs
    rcases (show s = {w : ℂ | w.im ≤ 0} ∨ s = {w : ℂ | 1 ≤ w.im} from by simpa using hs)
      with rfl | rfl
    · exact ⟨0, by simp [horizontalStrip], (strip_component_lower (by simp)).symm⟩
    · exact ⟨Complex.I, by simp [horizontalStrip], (strip_component_upper (by simp)).symm⟩

#print axioms strip_component_avoids_half
#print axioms strip_component_lower
#print axioms strip_component_upper
#print axioms horizontalStrip_components

end RudinRCA.Chapter13
