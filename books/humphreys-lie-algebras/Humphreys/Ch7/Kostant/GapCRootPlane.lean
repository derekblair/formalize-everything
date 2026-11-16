import Mathlib.LinearAlgebra.RootSystem.Finite.G2
import Mathlib.LinearAlgebra.Dimension.Finrank

open Function Set Submodule RootPairing

namespace Humphreys26_4.GapCRootPlane

section G2Arithmetic

private def g2Coeffs : List (ℤ × ℤ) :=
  [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (-1, -1),
   (2, 1), (-2, -1), (3, 1), (-3, -1), (3, 2), (-3, -2)]

private def pAdd (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 + v.1, u.2 + v.2)
private def pSub (u v : ℤ × ℤ) : ℤ × ℤ := (u.1 - v.1, u.2 - v.2)
private def pNeg (u : ℤ × ℤ) : ℤ × ℤ := (-u.1, -u.2)
private def pSmul (k : ℤ) (u : ℤ × ℤ) : ℤ × ℤ := (k * u.1, k * u.2)
private def pComb (m n : ℕ) (a b : ℤ × ℤ) : ℤ × ℤ := pAdd (pSmul (m : ℤ) a) (pSmul (n : ℤ) b)

private def isG2ShortPair (a b : ℤ × ℤ) : Bool :=
  decide (pAdd a b ∈ g2Coeffs) &&
  decide (pComb 2 1 a b ∈ g2Coeffs) &&
  decide (pComb 1 2 a b ∈ g2Coeffs) &&
  decide (pSub b a ∈ g2Coeffs) &&
  decide (pSub b (pSmul 2 a) ∉ g2Coeffs) &&
  decide (pSub (pAdd a b) (pSmul 2 a) ∈ g2Coeffs) &&
  decide (pSub (pAdd a b) (pSmul 3 a) ∉ g2Coeffs) &&
  decide (pSub b (pSmul 2 (pAdd a b)) ∈ g2Coeffs) &&
  decide (pSub b (pSmul 3 (pAdd a b)) ∉ g2Coeffs) &&
  decide (pComb 3 1 a b ∉ g2Coeffs) &&
  decide (pComb 2 2 a b ∉ g2Coeffs) &&
  decide (pComb 1 3 a b ∉ g2Coeffs) &&
  decide (pComb 3 2 a b ∉ g2Coeffs) &&
  decide (pComb 2 3 a b ∉ g2Coeffs) &&
  decide (pComb 3 3 a b ∉ g2Coeffs)

private def isG2Simple31 (a b : ℤ × ℤ) : Bool :=
  decide (pAdd a b ∈ g2Coeffs) &&
  decide (pComb 2 1 a b ∈ g2Coeffs) &&
  decide (pComb 3 1 a b ∈ g2Coeffs) &&
  decide (pComb 3 2 a b ∈ g2Coeffs) &&
  decide (pSub b a ∉ g2Coeffs) &&
  decide (pSub (pAdd a b) a ∈ g2Coeffs) &&
  decide (pSub (pAdd a b) (pSmul 2 a) ∉ g2Coeffs) &&
  decide (pSub (pComb 2 1 a b) (pSmul 2 a) ∈ g2Coeffs) &&
  decide (pSub (pComb 2 1 a b) (pSmul 3 a) ∉ g2Coeffs) &&
  decide (pSub (pAdd a b) (pSmul 2 (pComb 2 1 a b)) ∈ g2Coeffs) &&
  decide (pSub (pAdd a b) (pSmul 3 (pComb 2 1 a b)) ∉ g2Coeffs) &&
  decide (pComb 4 1 a b ∉ g2Coeffs) &&
  decide (pComb 4 2 a b ∉ g2Coeffs) &&
  decide (pComb 1 2 a b ∉ g2Coeffs) &&
  decide (pComb 5 2 a b ∉ g2Coeffs) &&
  decide (pComb 4 3 a b ∉ g2Coeffs) &&
  decide (pComb 5 3 a b ∉ g2Coeffs) &&
  decide (pComb 6 3 a b ∉ g2Coeffs)

private def g2PairValid (a b : ℤ × ℤ) : Bool :=
  decide (a = b) ||
  decide (a = pNeg b) ||
  decide (pAdd a b ∉ g2Coeffs) ||
  (decide (pAdd a b ∈ g2Coeffs) &&
    decide (pComb 2 1 a b ∉ g2Coeffs) &&
    decide (pComb 1 2 a b ∉ g2Coeffs)) ||
  isG2ShortPair a b ||
  isG2Simple31 a b ||
  isG2Simple31 b a

private theorem g2PairValid_all :
    (g2Coeffs.all fun a => g2Coeffs.all fun b => g2PairValid a b) = true := by
  decide

private theorem mem_g2Coeffs_iff_mem_allCoeffs (u : ℤ × ℤ) :
    u ∈ g2Coeffs ↔ (![u.1, u.2] : Fin 2 → ℤ) ∈ EmbeddedG2.allCoeffs := by
  rcases u with ⟨x, y⟩
  simp [g2Coeffs, EmbeddedG2.allCoeffs, funext_iff, Fin.forall_fin_two]

end G2Arithmetic

section RootPlane

variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  (P : RootPairing ι K M N) [Finite ι] [P.IsCrystallographic] [P.IsReduced]

/-- Oriented positive-cone cases for an ordered linearly independent root pair `(α, β)` (up to
`(α, β) ↔ (β, α)` swap). -/
inductive OrientedCone (α β : ι) : Prop
  | empty :
      P.root α + P.root β ∉ range P.root →
      OrientedCone α β
  | classTwo (γ : ι) :
      P.root γ = P.root α + P.root β →
      (2 : ℕ) • P.root α + P.root β ∉ range P.root →
      P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      OrientedCone α β
  | chain21 (γ δ : ι) :
      P.root γ = P.root α + P.root β →
      P.root δ = (2 : ℕ) • P.root α + P.root β →
      (3 : ℕ) • P.root α + P.root β ∉ range P.root →
      (2 : ℕ) • P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      OrientedCone α β
  | g2Short (γ δ ε : ι) :
      P.root γ = P.root α + P.root β →
      P.root δ = (2 : ℕ) • P.root α + P.root β →
      P.root ε = P.root α + (2 : ℕ) • P.root β →
      P.chainBotCoeff α β = 1 →
      P.chainBotCoeff α γ = 2 →
      P.chainBotCoeff γ β = 2 →
      (3 : ℕ) • P.root α + P.root β ∉ range P.root →
      (2 : ℕ) • P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      (3 : ℕ) • P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      (2 : ℕ) • P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      (3 : ℕ) • P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      OrientedCone α β
  | g2Simple31 (γ δ ε ζ : ι) :
      P.root γ = P.root α + P.root β →
      P.root δ = (2 : ℕ) • P.root α + P.root β →
      P.root ε = (3 : ℕ) • P.root α + P.root β →
      P.root ζ = (3 : ℕ) • P.root α + (2 : ℕ) • P.root β →
      P.chainBotCoeff α β = 0 →
      P.chainBotCoeff α γ = 1 →
      P.chainBotCoeff α δ = 2 →
      P.chainBotCoeff δ γ = 2 →
      (4 : ℕ) • P.root α + P.root β ∉ range P.root →
      (4 : ℕ) • P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      (5 : ℕ) • P.root α + (2 : ℕ) • P.root β ∉ range P.root →
      (4 : ℕ) • P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      (5 : ℕ) • P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      (6 : ℕ) • P.root α + (3 : ℕ) • P.root β ∉ range P.root →
      OrientedCone α β

private theorem chainBotCoeff_eq_of_sub_mem_not_mem {ξ η : ι}
    (hsum : P.root ξ + P.root η ∈ range P.root) {p : ℕ}
    (hmem : P.root η - p • P.root ξ ∈ range P.root)
    (hnot : P.root η - (p + 1) • P.root ξ ∉ range P.root) :
    P.chainBotCoeff ξ η = p := by
  have hlin : LinearIndependent K ![P.root ξ, P.root η] :=
    P.linearIndependent_of_add_mem_range_root' hsum
  have hle : p ≤ P.chainBotCoeff ξ η :=
    (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).mp hmem
  have hlt : ¬ p + 1 ≤ P.chainBotCoeff ξ η := fun h =>
    hnot ((P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlin).mpr h)
  omega

/-! ### Non-`G₂` plane classification (`NB-3`: local plane bounds, no `[P.IsIrreducible]`) -/

omit [P.IsReduced] in
private theorem local_chainBot_add_chainTop_le_two
    {W : Submodule K M}
    (hno3 : ∀ γ δ : ι, P.root γ ∈ W → P.root δ ∈ W →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ))
    {i j : ι} (hi : P.root i ∈ W) (hj : P.root j ∈ W) :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 2 := by
  by_cases h : LinearIndependent K ![P.root i, P.root j]
  swap
  · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have htopW : P.root (P.chainTopIdx i j) ∈ W := by
    rw [P.root_chainTopIdx]
    exact W.add_mem hj (nsmul_mem hi (P.chainTopCoeff i j))
  have hb := hno3 (P.chainTopIdx i j) i htopW hi
  simp only [mem_insert_iff, mem_singleton_iff] at hb
  omega

private theorem local_pairingIn_le_zero_of_root_add_mem
    {W : Submodule K M}
    (hno3 : ∀ γ δ : ι, P.root γ ∈ W → P.root δ ∈ W →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ))
    {i j : ι} (hi : P.root i ∈ W) (hj : P.root j ∈ W)
    (h : P.root i + P.root j ∈ range P.root) :
    P.pairingIn ℤ i j ≤ 0 := by
  have aux₁ := P.linearIndependent_of_add_mem_range_root' (add_comm (P.root i) (P.root j) ▸ h)
  have aux₂ := local_chainBot_add_chainTop_le_two P hno3 hj hi
  have aux₃ : 1 ≤ P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  omega

private theorem local_zero_le_pairingIn_of_root_sub_mem
    {W : Submodule K M}
    (hno3 : ∀ γ δ : ι, P.root γ ∈ W → P.root δ ∈ W →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ))
    {i j : ι} (hi : P.root i ∈ W) (hj : P.root j ∈ W)
    (h : P.root i - P.root j ∈ range P.root) :
    0 ≤ P.pairingIn ℤ i j := by
  have hj' : P.root (P.reflectionPerm j j) ∈ W := by
    rw [root_reflectionPerm, reflection_apply_self]
    exact W.neg_mem hj
  have h' : P.root i + P.root (P.reflectionPerm j j) ∈ range P.root := by
    simpa [root_reflectionPerm, reflection_apply_self, ← sub_eq_add_neg] using h
  simpa using local_pairingIn_le_zero_of_root_add_mem P hno3 hi hj' h'

private theorem local_root_add_mem_of_pos_nsmul_add_pos_nsmul_mem
    {α β : ι} (hlin : LinearIndependent K ![P.root α, P.root β])
    (hno3 : ∀ γ δ : ι,
      P.root γ ∈ span K {P.root α, P.root β} →
      P.root δ ∈ span K {P.root α, P.root β} →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root α + n • P.root β ∈ range P.root) :
    P.root α + P.root β ∈ range P.root := by
  let W := span K {P.root α, P.root β}
  have hαW : P.root α ∈ W := subset_span (by simp)
  have hβW : P.root β ∈ W := subset_span (by simp)
  by_contra hsum
  have hne := ((IsReduced.linearIndependent_iff P).mp hlin).2
  have hab : 0 ≤ P.pairingIn ℤ α β := by
    by_contra! hneg
    exact hsum (P.root_add_root_mem_of_pairingIn_neg hneg hne)
  have hba : 0 ≤ P.pairingIn ℤ β α := by
    by_contra! hneg
    have hne' : P.root β ≠ -P.root α := fun heq =>
      hne (by simpa only [neg_neg] using (congrArg Neg.neg heq).symm)
    exact hsum (by simpa [add_comm] using P.root_add_root_mem_of_pairingIn_neg hneg hne')
  obtain ⟨γ, hγ⟩ := h
  have hγW : P.root γ ∈ W := by
    rw [hγ]
    exact W.add_mem (nsmul_mem hαW m) (nsmul_mem hβW n)
  have hγ' : P.root γ = (m : ℤ) • P.root α + (n : ℤ) • P.root β := by
    simpa only [natCast_zsmul] using hγ
  have ha := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := α) hγ'
  have hb := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := β) hγ'
  simp only [pairingIn_same, smul_eq_mul] at ha hb
  have hbounda := hno3 γ α hγW hαW
  have hboundb := hno3 γ β hγW hβW
  have hma : (m : ℤ) ≤ 1 := by
    have := mul_nonneg (Int.natCast_nonneg n) hba
    simp only [mem_insert_iff, mem_singleton_iff] at hbounda
    omega
  have hnb : (n : ℤ) ≤ 1 := by
    have := mul_nonneg (Int.natCast_nonneg m) hab
    simp only [mem_insert_iff, mem_singleton_iff] at hboundb
    omega
  have hm1 : m = 1 := by omega
  have hn1 : n = 1 := by omega
  exact hsum (by simpa [hm1, hn1] using mem_range.mpr ⟨γ, hγ⟩)

private theorem local_coefficients_of_pos_nsmul_add_pos_nsmul_mem
    {α β : ι} (hlin : LinearIndependent K ![P.root α, P.root β])
    (hno3 : ∀ γ δ : ι,
      P.root γ ∈ span K {P.root α, P.root β} →
      P.root δ ∈ span K {P.root α, P.root β} →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m • P.root α + n • P.root β ∈ range P.root) :
    (m = 1 ∧ n = 1) ∨ (m = 2 ∧ n = 1) ∨ (m = 1 ∧ n = 2) := by
  let W := span K {P.root α, P.root β}
  have hαW : P.root α ∈ W := subset_span (by simp)
  have hβW : P.root β ∈ W := subset_span (by simp)
  obtain ⟨γ, hγ⟩ := local_root_add_mem_of_pos_nsmul_add_pos_nsmul_mem P hlin hno3 hm hn h
  have hγW : P.root γ ∈ W := by rw [hγ]; exact W.add_mem hαW hβW
  have hag : 0 ≤ P.pairingIn ℤ α γ := by
    apply local_zero_le_pairingIn_of_root_sub_mem P hno3 hαW hγW
    convert P.neg_root_mem β using 1; rw [hγ]; abel
  have hbg : 0 ≤ P.pairingIn ℤ β γ := by
    apply local_zero_le_pairingIn_of_root_sub_mem P hno3 hβW hγW
    convert P.neg_root_mem α using 1; rw [hγ]; abel
  have hsum : P.pairingIn ℤ α γ + P.pairingIn ℤ β γ = 2 := by
    simpa only [pairingIn_same] using
      (pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := γ) hγ).symm
  obtain ⟨δ, hδ⟩ := h
  have hδW : P.root δ ∈ W := by
    rw [hδ]; exact W.add_mem (nsmul_mem hαW m) (nsmul_mem hβW n)
  have hδ' : P.root δ = (m : ℤ) • P.root α + (n : ℤ) • P.root β := by
    simpa only [natCast_zsmul] using hδ
  have hd := pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := γ) hδ'
  simp only [smul_eq_mul] at hd
  have hbound := hno3 δ γ hδW hγW
  simp only [mem_insert_iff, mem_singleton_iff] at hbound
  have hle : P.pairingIn ℤ δ γ ≤ 2 := by omega
  have hor : m = 1 ∨ n = 1 := by
    by_contra! hne
    have hma : (2 : ℤ) ≤ m := by omega
    have hnb : (2 : ℤ) ≤ n := by omega
    nlinarith [mul_le_mul_of_nonneg_right hma hag, mul_le_mul_of_nonneg_right hnb hbg]
  have hchaina := local_chainBot_add_chainTop_le_two P hno3 hαW hβW
  have hchainb := local_chainBot_add_chainTop_le_two P hno3 hβW hαW
  rcases hor with rfl | rfl
  · have htop : n ≤ P.chainTopCoeff β α := by
      apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff
        (LinearIndependent.pair_symm_iff.mpr hlin)).mp
      simpa only [one_smul] using mem_range.mpr ⟨δ, hδ⟩
    omega
  · have htop : m ≤ P.chainTopCoeff α β := by
      apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlin).mp
      simpa only [one_smul, add_comm] using mem_range.mpr ⟨δ, hδ⟩
    omega

private theorem local_not_double_both
    {α β : ι} (hlin : LinearIndependent K ![P.root α, P.root β])
    (hno3 : ∀ γ δ : ι,
      P.root γ ∈ span K {P.root α, P.root β} →
      P.root δ ∈ span K {P.root α, P.root β} →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ)) :
    ¬ ((2 : ℕ) • P.root α + P.root β ∈ range P.root ∧
      P.root α + (2 : ℕ) • P.root β ∈ range P.root) := by
  let W := span K {P.root α, P.root β}
  have hαW : P.root α ∈ W := subset_span (by simp)
  have hβW : P.root β ∈ W := subset_span (by simp)
  rintro ⟨⟨δ, hδ⟩, ⟨ε, hε⟩⟩
  obtain ⟨γ, hγ⟩ := local_root_add_mem_of_pos_nsmul_add_pos_nsmul_mem P hlin hno3
    (by decide : 0 < 2) (by decide : 0 < 1) (by simpa only [one_smul] using mem_range.mpr ⟨δ, hδ⟩)
  have hγW : P.root γ ∈ W := by rw [hγ]; exact W.add_mem hαW hβW
  have hda : P.root δ = P.root α + P.root γ := by rw [hδ, hγ]; abel
  have heb : P.root ε = P.root β + P.root γ := by rw [hε, hγ]; abel
  have ha := local_pairingIn_le_zero_of_root_add_mem P hno3 hαW hγW (mem_range.mpr ⟨δ, hda⟩)
  have hb := local_pairingIn_le_zero_of_root_add_mem P hno3 hβW hγW (mem_range.mpr ⟨ε, heb⟩)
  have hgg := pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := γ) hγ
  rw [pairingIn_same] at hgg
  omega

private theorem classify_nonG2_plane
    {α β : ι} (hlin : LinearIndependent K ![P.root α, P.root β])
    (hno3 : ∀ γ δ : ι,
      P.root γ ∈ span K {P.root α, P.root β} →
      P.root δ ∈ span K {P.root α, P.root β} →
      P.pairingIn ℤ γ δ ∈ ({-2, -1, 0, 1, 2} : Set ℤ)) :
    OrientedCone P α β ∨ OrientedCone P β α := by
  by_cases h11 : P.root α + P.root β ∈ range P.root
  · obtain ⟨γ, hγ⟩ := h11
    by_cases h21 : (2 : ℕ) • P.root α + P.root β ∈ range P.root
    · obtain ⟨δ, hδ⟩ := h21
      refine Or.inl (OrientedCone.chain21 γ δ hγ hδ ?_ ?_ ?_)
      · intro h31
        have hc := local_coefficients_of_pos_nsmul_add_pos_nsmul_mem P hlin hno3
          (by decide : 0 < 3) (by decide : 0 < 1) (by simpa only [one_smul] using h31)
        omega
      · intro h22
        have hc := local_coefficients_of_pos_nsmul_add_pos_nsmul_mem P hlin hno3
          (by decide : 0 < 2) (by decide : 0 < 2) h22
        omega
      · intro h12
        exact local_not_double_both P hlin hno3 ⟨⟨δ, hδ⟩, h12⟩
    · by_cases h12 : P.root α + (2 : ℕ) • P.root β ∈ range P.root
      · obtain ⟨δ, hδ⟩ := h12
        have hlin' : LinearIndependent K ![P.root β, P.root α] :=
          LinearIndependent.pair_symm_iff.mpr hlin
        have hspan_eq : span K {P.root β, P.root α} = span K {P.root α, P.root β} := by
          rw [Set.pair_comm]
        have hno3' : ∀ ξ η : ι,
            P.root ξ ∈ span K {P.root β, P.root α} →
            P.root η ∈ span K {P.root β, P.root α} →
            P.pairingIn ℤ ξ η ∈ ({-2, -1, 0, 1, 2} : Set ℤ) := by
          simpa only [hspan_eq] using hno3
        refine Or.inr (OrientedCone.chain21 γ δ (by rw [hγ, add_comm])
          (by rw [hδ, add_comm]) ?_ ?_ ?_)
        · intro h31
          have hc := local_coefficients_of_pos_nsmul_add_pos_nsmul_mem P hlin' hno3'
            (by decide : 0 < 3) (by decide : 0 < 1) (by simpa only [one_smul] using h31)
          omega
        · intro h22
          have hc := local_coefficients_of_pos_nsmul_add_pos_nsmul_mem P hlin' hno3'
            (by decide : 0 < 2) (by decide : 0 < 2) h22
          omega
        · simpa only [add_comm] using h21
      · exact Or.inl (OrientedCone.classTwo γ hγ h21 h12)
  · exact Or.inl (OrientedCone.empty h11)

/-! ### Embedded `G₂` plane classification (when `∃ l s` in plane with `pairingIn ℤ l s = -3`) -/

omit [P.IsCrystallographic] [P.IsReduced] in
private theorem mem_allRoots_of_mem_embeddedG2_plane
    [P.EmbeddedG2] {α β : ι}
    (hlW : EmbeddedG2.longRoot P ∈ span K {P.root α, P.root β})
    (hsW : EmbeddedG2.shortRoot P ∈ span K {P.root α, P.root β})
    {γ : ι} (hγW : P.root γ ∈ span K {P.root α, P.root β}) :
    P.root γ ∈ EmbeddedG2.allRoots P := by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := EmbeddedG2.isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  have : Module.IsReflexive K M := .of_isPerfPair P.toLinearMap
  rw [isOrthogonal_iff_pairing_eq_zero, ← B.apply_root_root_zero_iff] at h₁ h₂
  let W := span K {P.root α, P.root β}
  let v : Fin 2 → W := ![(⟨EmbeddedG2.shortRoot P, hsW⟩ : W), ⟨EmbeddedG2.longRoot P, hlW⟩]
  have hv_li : LinearIndependent K v := by
    apply LinearIndependent.of_comp W.subtype
    have hcomp : (W.subtype ∘ v) = ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P] := by
      ext j; fin_cases j <;> rfl
    rw [hcomp]
    exact EmbeddedG2.linearIndependent_short_long P
  have hfinW : Module.finrank K W ≤ 2 := by
    classical
    have heq : ({P.root α, P.root β} : Set M) = ↑({P.root α, P.root β} : Finset M) := by simp
    change Module.finrank K (span K {P.root α, P.root β}) ≤ 2
    rw [heq]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_le_two
  have : FiniteDimensional K W := by
    classical
    have heq : ({P.root α, P.root β} : Set M) = ↑({P.root α, P.root β} : Finset M) := by simp
    rw [show W = span K ({P.root α, P.root β} : Set M) from rfl, heq]
    exact FiniteDimensional.span_of_finite K (Finset.finite_toSet _)
  have hspanW : span K (range v) = ⊤ := by
    have h2 : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
    have hge : 2 ≤ Module.finrank K W := by
      simpa only [h2] using hv_li.fintype_card_le_finrank
    have heq_dim : Fintype.card (Fin 2) = Module.finrank K W := by omega
    exact hv_li.span_eq_top_of_card_eq_finrank heq_dim
  have hγ_mem : (⟨P.root γ, hγW⟩ : W) ∈ span K (range v) := by
    rw [hspanW]; trivial
  have hform0 : ∀ w ∈ span K (range v), B.form (P.root γ) (w : M) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨j, rfl⟩ := hu
      fin_cases j
      · exact h₁
      · exact h₂
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  exact B.ne_zero γ (hform0 ⟨P.root γ, hγW⟩ hγ_mem)

set_option linter.overlappingInstances false in
private theorem classify_embeddedG2_plane
    [P.EmbeddedG2] {α β : ι}
    (hlin : LinearIndependent K ![P.root α, P.root β])
    (hlW : EmbeddedG2.longRoot P ∈ span K {P.root α, P.root β})
    (hsW : EmbeddedG2.shortRoot P ∈ span K {P.root α, P.root β}) :
    OrientedCone P α β ∨ OrientedCone P β α := by
  classical
  let W := span K {P.root α, P.root β}
  let f : (ℤ × ℤ) → M := fun u =>
    u.1 • EmbeddedG2.shortRoot P + u.2 • EmbeddedG2.longRoot P
  let fFin := Fintype.linearCombination ℤ ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P]
  have hf_eq (u : ℤ × ℤ) : f u = fFin ![u.1, u.2] := by
    simp [f, fFin, Fintype.linearCombination_apply]
  have hfFin_inj : Injective fFin :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp
      ((EmbeddedG2.linearIndependent_short_long P).restrict_scalars' ℤ)
  have hf_add (u v : ℤ × ℤ) : f (pAdd u v) = f u + f v := by
    simp [f, pAdd, add_smul]; abel
  have hf_sub (u v : ℤ × ℤ) : f (pSub u v) = f u - f v := by
    simp [f, pSub, sub_smul]; abel
  have hf_smul (k : ℕ) (u : ℤ × ℤ) : f (pSmul (k : ℤ) u) = k • f u := by
    simp [f, pSmul, mul_smul, natCast_zsmul]
  have hf_comb (m n : ℕ) (u v : ℤ × ℤ) :
      f (pComb m n u v) = m • f u + n • f v := by
    rw [pComb, hf_add, hf_smul, hf_smul]
  have hfW (u : ℤ × ℤ) : f u ∈ W :=
    W.add_mem (zsmul_mem hsW u.1) (zsmul_mem hlW u.2)
  have mem_range_iff (u : ℤ × ℤ) : f u ∈ range P.root ↔ u ∈ g2Coeffs := by
    constructor
    · rintro ⟨γ, hγ⟩
      have hγW : P.root γ ∈ W := hγ ▸ hfW u
      have hall := mem_allRoots_of_mem_embeddedG2_plane P hlW hsW hγW
      rw [EmbeddedG2.allRoots_eq_map_allCoeffs] at hall
      obtain ⟨c, hc, hfc⟩ := List.mem_map.mp hall
      have hcu : c = ![u.1, u.2] := hfFin_inj (by rw [hfc, hγ, hf_eq])
      exact (mem_g2Coeffs_iff_mem_allCoeffs u).mpr (hcu ▸ hc)
    · intro hu
      have hc := (mem_g2Coeffs_iff_mem_allCoeffs u).mp hu
      have hall : fFin ![u.1, u.2] ∈ EmbeddedG2.allRoots P := by
        rw [EmbeddedG2.allRoots_eq_map_allCoeffs]
        exact List.mem_map.mpr ⟨![u.1, u.2], hc, rfl⟩
      rw [hf_eq]
      exact EmbeddedG2.allRoots_subset_range_root P (List.mem_toFinset.mpr hall)
  have coords_of_mem {γ : ι} (hγW : P.root γ ∈ W) :
      ∃ u ∈ g2Coeffs, f u = P.root γ := by
    have hall := mem_allRoots_of_mem_embeddedG2_plane P hlW hsW hγW
    rw [EmbeddedG2.allRoots_eq_map_allCoeffs] at hall
    obtain ⟨c, hc, hfc⟩ := List.mem_map.mp hall
    have hpair : (c 0, c 1) ∈ g2Coeffs := by
      rw [mem_g2Coeffs_iff_mem_allCoeffs]
      convert hc using 1
      ext j; fin_cases j <;> rfl
    refine ⟨(c 0, c 1), hpair, ?_⟩
    rw [hf_eq]
    convert hfc using 2
    ext j; fin_cases j <;> rfl
  obtain ⟨a, ha, hai⟩ := coords_of_mem (subset_span (by simp) : P.root α ∈ W)
  obtain ⟨b, hb, hbj⟩ := coords_of_mem (subset_span (by simp) : P.root β ∈ W)
  obtain ⟨hne_root, hneg_root⟩ := (IsReduced.linearIndependent_iff P).mp hlin
  have hab_ne : a ≠ b := fun h => hne_root (P.root.injective (by rw [← hai, h, hbj]))
  have hab_neg : a ≠ pNeg b := by
    intro h
    apply hneg_root
    rw [← hai, ← hbj, h]
    simp [f, pNeg, neg_smul, neg_add_rev, add_comm]
  have hvalid : g2PairValid a b = true :=
    (List.all_eq_true.mp (List.all_eq_true.mp g2PairValid_all a ha) b hb)
  have comb_mem (m n : ℕ) (u v : ℤ × ℤ) :
      m • f u + n • f v ∈ range P.root ↔ pComb m n u v ∈ g2Coeffs := by
    rw [← hf_comb, mem_range_iff]
  have sub_mem (u v : ℤ × ℤ) (p : ℕ) :
      f v - p • f u ∈ range P.root ↔ pSub v (pSmul (p : ℤ) u) ∈ g2Coeffs := by
    rw [← hf_smul, ← hf_sub, mem_range_iff]
  have build_simple31 {ξ η : ι} {u v : ℤ × ℤ}
      (hu : f u = P.root ξ) (hv : f v = P.root η)
      (hs31 : isG2Simple31 u v = true) : OrientedCone P ξ η := by
    simp only [isG2Simple31, Bool.and_eq_true, decide_eq_true_eq] at hs31
    rcases hs31 with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩,
      h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩
    obtain ⟨γ, hγ⟩ := (mem_range_iff (pAdd u v)).mpr h1
    obtain ⟨δ, hδ⟩ := (mem_range_iff (pComb 2 1 u v)).mpr h2
    obtain ⟨ε, hε⟩ := (mem_range_iff (pComb 3 1 u v)).mpr h3
    obtain ⟨ζ, hζ⟩ := (mem_range_iff (pComb 3 2 u v)).mpr h4
    have hγ_eq : P.root γ = P.root ξ + P.root η := by rw [hγ, hf_add, hu, hv]
    have hδ_eq : P.root δ = (2 : ℕ) • P.root ξ + P.root η := by
      rw [hδ, hf_comb 2 1 u v, hu, hv, one_smul]
    have hε_eq : P.root ε = (3 : ℕ) • P.root ξ + P.root η := by
      rw [hε, hf_comb 3 1 u v, hu, hv, one_smul]
    have hζ_eq : P.root ζ = (3 : ℕ) • P.root ξ + (2 : ℕ) • P.root η := by
      rw [hζ, hf_comb 3 2 u v, hu, hv]
    have hp1 : P.chainBotCoeff ξ η = 0 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨γ, hγ_eq⟩
      · simp
      · rw [← hu, ← hv, sub_mem]; simpa [pSmul] using h5
    have hp2 : P.chainBotCoeff ξ γ = 1 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨δ, by rw [hδ_eq, hγ_eq]; abel⟩
      · rw [← hu, hγ, sub_mem]; simpa [pSmul] using h6
      · rw [← hu, hγ, sub_mem]; exact h7
    have hp3 : P.chainBotCoeff ξ δ = 2 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨ε, by rw [hε_eq, hδ_eq]; abel⟩
      · rw [← hu, hδ, sub_mem]; exact h8
      · rw [← hu, hδ, sub_mem]; exact h9
    have hp4 : P.chainBotCoeff δ γ = 2 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨ζ, by rw [hζ_eq, hδ_eq, hγ_eq]; abel⟩
      · rw [hδ, hγ, sub_mem]; exact h10
      · rw [hδ, hγ, sub_mem]; exact h11
    refine OrientedCone.g2Simple31 γ δ ε ζ hγ_eq hδ_eq hε_eq hζ_eq hp1 hp2 hp3 hp4
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← hu, ← hv]; simpa only [one_smul] using mt (comb_mem 4 1 u v).mp h12
    · rw [← hu, ← hv]; exact mt (comb_mem 4 2 u v).mp h13
    · rw [← hu, ← hv]; simpa only [one_smul] using mt (comb_mem 1 2 u v).mp h14
    · rw [← hu, ← hv]; exact mt (comb_mem 5 2 u v).mp h15
    · rw [← hu, ← hv]; exact mt (comb_mem 4 3 u v).mp h16
    · rw [← hu, ← hv]; exact mt (comb_mem 5 3 u v).mp h17
    · rw [← hu, ← hv]; exact mt (comb_mem 6 3 u v).mp h18
  simp only [g2PairValid, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  rcases hvalid with ((((((rfl | hab_neg') | hempty) | ⟨⟨h11, h21⟩, h12⟩) | hshort) | hs31) | hs13)
  · exact absurd rfl hab_ne
  · exact absurd hab_neg' hab_neg
  · refine Or.inl (OrientedCone.empty ?_)
    rw [← hai, ← hbj, ← hf_add, mem_range_iff]
    exact hempty
  · obtain ⟨γ, hγ⟩ := (mem_range_iff (pAdd a b)).mpr h11
    refine Or.inl (OrientedCone.classTwo γ (by rw [hγ, hf_add, hai, hbj]) ?_ ?_)
    · rw [← hai, ← hbj]; simpa only [one_smul] using mt (comb_mem 2 1 a b).mp h21
    · rw [← hai, ← hbj]; simpa only [one_smul] using mt (comb_mem 1 2 a b).mp h12
  · simp only [isG2ShortPair, Bool.and_eq_true, decide_eq_true_eq] at hshort
    rcases hshort with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩,
      h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩
    obtain ⟨γ, hγ⟩ := (mem_range_iff (pAdd a b)).mpr h1
    obtain ⟨δ, hδ⟩ := (mem_range_iff (pComb 2 1 a b)).mpr h2
    obtain ⟨ε, hε⟩ := (mem_range_iff (pComb 1 2 a b)).mpr h3
    have hγ_eq : P.root γ = P.root α + P.root β := by rw [hγ, hf_add, hai, hbj]
    have hδ_eq : P.root δ = (2 : ℕ) • P.root α + P.root β := by
      rw [hδ, hf_comb 2 1 a b, hai, hbj, one_smul]
    have hε_eq : P.root ε = P.root α + (2 : ℕ) • P.root β := by
      rw [hε, hf_comb 1 2 a b, hai, hbj, one_smul]
    have hp1 : P.chainBotCoeff α β = 1 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨γ, hγ_eq⟩
      · rw [← hai, ← hbj, sub_mem]; simpa [pSmul] using h4
      · rw [← hai, ← hbj, sub_mem]; exact h5
    have hp2 : P.chainBotCoeff α γ = 2 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨δ, by rw [hδ_eq, hγ_eq]; abel⟩
      · rw [← hai, hγ, sub_mem]; exact h6
      · rw [← hai, hγ, sub_mem]; exact h7
    have hp3 : P.chainBotCoeff γ β = 2 := by
      apply chainBotCoeff_eq_of_sub_mem_not_mem P ⟨ε, by rw [hε_eq, hγ_eq]; abel⟩
      · rw [hγ, ← hbj, sub_mem]; exact h8
      · rw [hγ, ← hbj, sub_mem]; exact h9
    refine Or.inl (OrientedCone.g2Short γ δ ε hγ_eq hδ_eq hε_eq hp1 hp2 hp3 ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [← hai, ← hbj]; simpa only [one_smul] using mt (comb_mem 3 1 a b).mp h10
    · rw [← hai, ← hbj]; exact mt (comb_mem 2 2 a b).mp h11
    · rw [← hai, ← hbj]; simpa only [one_smul] using mt (comb_mem 1 3 a b).mp h12
    · rw [← hai, ← hbj]; exact mt (comb_mem 3 2 a b).mp h13
    · rw [← hai, ← hbj]; exact mt (comb_mem 2 3 a b).mp h14
    · rw [← hai, ← hbj]; exact mt (comb_mem 3 3 a b).mp h15
  · exact Or.inl (build_simple31 hai hbj hs31)
  · exact Or.inr (build_simple31 hbj hai hs13)

/-- **Local Rank-2 Positive-Cone Classification (Route C2.1):**
For any linearly independent roots `α, β` in any finite crystallographic reduced root pairing
(without `[P.IsIrreducible]`), either `(α, β)` or `(β, α)` falls into one of the five oriented
positive-cone cases. -/
theorem orientedCone_or_symm {α β : ι} (hlin : LinearIndependent K ![P.root α, P.root β]) :
    OrientedCone P α β ∨ OrientedCone P β α := by
  let W := span K {P.root α, P.root β}
  by_cases hex3 : ∃ l s : ι, P.root l ∈ W ∧ P.root s ∈ W ∧ P.pairingIn ℤ l s = -3
  · obtain ⟨l, s, hlW, hsW, hls⟩ := hex3
    let _ : P.EmbeddedG2 :=
      { long := l
        short := s
        pairingIn_long_short := hls }
    exact classify_embeddedG2_plane P hlin hlW hsW
  · refine classify_nonG2_plane P hlin fun γ δ hγW hδW => ?_
    have hpair := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed γ δ
    have hnot_neg3 : P.pairingIn ℤ γ δ ≠ -3 := fun h => hex3 ⟨γ, δ, hγW, hδW, h⟩
    have hnot_pos3 : P.pairingIn ℤ γ δ ≠ 3 := by
      intro h3
      have hγ'W : P.root (P.reflectionPerm γ γ) ∈ W := by
        rw [root_reflectionPerm, reflection_apply_self]
        exact W.neg_mem hγW
      have hneg3 : P.pairingIn ℤ (P.reflectionPerm γ γ) δ = -3 := by
        simp [h3]
      exact hex3 ⟨P.reflectionPerm γ γ, δ, hγ'W, hδW, hneg3⟩
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hpair ⊢
    omega

end RootPlane

end Humphreys26_4.GapCRootPlane
