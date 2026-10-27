import Merkle.Binding
import Merkle.ConsistencyStructure

namespace Merkle

/-- An arbitrary successful consistency walk binds two honest trees to a prefix,
or exhibits an explicit hash collision. Both trees are independently quantified;
the unused proof suffix and all supplied sibling bytes are unrestricted. -/
theorem consistencyRoots_extract (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (n m : Nat) (b : Bool) (known : ByteArray) (proof : List ByteArray)
    (old current : ByteArray) (rest : List ByteArray)
    (hmn : 0 < m ∧ m ≤ n) (ds₀ ds : List ByteArray)
    (hm₀ : ds₀.length = m) (hn : ds.length = n)
    (hold : old = MTH H ds₀) (hcur : current = MTH H ds)
    (hknown : b = true → known = MTH H ds₀)
    (hwalk : consistencyRoots H m n b known proof = some (old, current, rest)) :
    ds₀ = ds.take m ∨ Collides H := by
  by_cases heq : m = n
  · have hsame := consistencyRoots_equal H m n b known proof old current rest heq hwalk
    have ht : ds.take m = ds := List.take_of_length_le (by omega)
    rw [ht]
    exact mth_binding H ℓ hw ds₀ ds (hold.symm.trans (hsame.trans hcur))
  · have hn2 : 1 < n := by omega
    have hk := split_lt hn2
    have hp := split_pos hn2
    have htree : MTH H ds =
        nodeHash H (MTH H (ds.take (split n))) (MTH H (ds.drop (split n))) := by
      simpa only [hn] using MTH_eq H ds (by omega)
    by_cases hmleft : m ≤ split n
    · obtain ⟨child, sibling, hsub, hnode⟩ :=
        consistencyRoots_left_inv H m n b known proof old current rest
          heq hn2 hmleft hwalk
      -- The equal-size subcall may return an unhashed seed. In that case its
      -- equal components and the honest old root supply the missing width.
      have hwidth : child.size = ℓ := by
        by_cases hlt : m < split n
        · exact consistencyRoots_current_size H ℓ hw m (split n) b known proof
            old child (sibling :: rest) hlt hsub
        · have hequal := consistencyRoots_equal H m (split n) b known proof
            old child (sibling :: rest) (by omega) hsub
          rw [← hequal, hold]
          exact MTH_size H ℓ hw ds₀
      have hhash := hnode.symm.trans (hcur.trans htree)
      rcases nodeHash_eq_left H
          (hwidth.trans (MTH_size H ℓ hw (ds.take (split n))).symm) hhash
          with hchildren | hcollision
      · have hlen : (ds.take (split n)).length = split n := by
          simp only [List.length_take, hn, Nat.min_eq_left (Nat.le_of_lt hk)]
        have hextract := consistencyRoots_extract H ℓ hw (split n) m b known proof
          old child (sibling :: rest) ⟨hmn.1, hmleft⟩ ds₀ (ds.take (split n))
          hm₀ hlen hold hchildren.1 hknown hsub
        simpa only [List.take_take, Nat.min_eq_left hmleft] using hextract
      · exact Or.inr hcollision
    · obtain ⟨oldChild, currentChild, sibling, hsub, hnodeOld, hnodeCurrent⟩ :=
        consistencyRoots_right_inv H m n b known proof old current rest
          heq hn2 hmleft hwalk
      -- Recover the current chain FIRST, from the right: the old child may
      -- still be a raw seed and the sibling has no width guarantee yet.
      have hwidth := consistencyRoots_current_size H ℓ hw (m - split n)
        (n - split n) false known proof oldChild currentChild (sibling :: rest)
        (by omega) hsub
      have hhash := hnodeCurrent.symm.trans (hcur.trans htree)
      rcases nodeHash_eq_right H
          (hwidth.trans (MTH_size H ℓ hw (ds.drop (split n))).symm) hhash
          with hcurrent | hcollision
      · have halign : split m = split n := split_prefix hn2 (by omega) hmn.2
        have htreeOld : MTH H ds₀ = nodeHash H (MTH H (ds₀.take (split n)))
            (MTH H (ds₀.drop (split n))) := by
          simpa only [hm₀, halign] using MTH_eq H ds₀ (by omega)
        -- The current equation has now identified the sibling as an honest
        -- digest, so splitting the old equation from the left is justified.
        have hsibling : sibling.size = (MTH H (ds₀.take (split n))).size := by
          rw [hcurrent.1, MTH_size H ℓ hw, MTH_size H ℓ hw]
        have hhashOld := hnodeOld.symm.trans (hold.trans htreeOld)
        rcases nodeHash_eq_left H hsibling hhashOld with hprevious | hcollision
        · -- This shared left subtree is never entered by the verifier. Its
          -- hash equality requires a SECOND binding call, independent of IH.
          rcases mth_binding H ℓ hw (ds₀.take (split n)) (ds.take (split n))
              (hprevious.1.symm.trans hcurrent.1) with hleft | hcollision
          · have hmright : (ds₀.drop (split n)).length = m - split n := by
              simp only [List.length_drop, hm₀]
            have hnright : (ds.drop (split n)).length = n - split n := by
              simp only [List.length_drop, hn]
            have hextract := consistencyRoots_extract H ℓ hw (n - split n)
              (m - split n) false known proof oldChild currentChild (sibling :: rest)
              ⟨by omega, by omega⟩ (ds₀.drop (split n)) (ds.drop (split n))
              hmright hnright hprevious.2 hcurrent.2 (by simp) hsub
            rcases hextract with hright | hcollision
            · left
              calc
                ds₀ = ds₀.take (split n) ++ ds₀.drop (split n) :=
                  (List.take_append_drop _ _).symm
                _ = ds.take (split n) ++ (ds.drop (split n)).take (m - split n) := by
                  rw [hleft, hright]
                _ = ds.take m := by
                  rw [List.take_drop, show split n + (m - split n) = m by omega]
                  have ht : (ds.take m).take (split n) = ds.take (split n) := by
                    rw [List.take_take, Nat.min_eq_left (by omega : split n ≤ m)]
                  rw [← ht, List.take_append_drop]
            · exact Or.inr hcollision
          · exact Or.inr hcollision
        · exact Or.inr hcollision
      · exact Or.inr hcollision
termination_by n
decreasing_by
  · exact hk
  · omega

/-- Consistency acceptance against two honest commitments implies the first
leaf list is the claimed prefix, or supplies an explicit hash collision. -/
theorem consistency_sound (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds₀ ds : List ByteArray) (hm : 0 < ds₀.length) (hle : ds₀.length ≤ ds.length)
    (proof : List ByteArray)
    (hacc : verifyConsistency H ds₀.length ds.length (MTH H ds₀) (MTH H ds)
        proof = true) :
    ds₀ = ds.take ds₀.length ∨ Collides H := by
  unfold verifyConsistency at hacc
  rw [ite_eq_left ⟨hm, hle⟩] at hacc
  cases hwalk : consistencyRoots H ds₀.length ds.length true (MTH H ds₀) proof with
  | none => simp [hwalk] at hacc
  | some result =>
    rcases result with ⟨old, current, rest⟩
    cases rest with
    | nil =>
      have hroots : old = MTH H ds₀ ∧ current = MTH H ds := by
        simpa only [hwalk, decide_eq_true_eq] using hacc
      exact consistencyRoots_extract H ℓ hw ds.length ds₀.length true (MTH H ds₀)
        proof old current [] ⟨hm, hle⟩ ds₀ ds rfl rfl hroots.1 hroots.2
        (by intros; rfl) hwalk
    | cons sibling rest => simp [hwalk] at hacc

/-- The idealized injectivity corollary; this is not a cryptographic security
claim about a fixed-width hash on arbitrary byte strings. -/
theorem consistency_sound_of_injective (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (hinj : ∀ x y : ByteArray, H x = H y → x = y)
    (ds₀ ds : List ByteArray) (hm : 0 < ds₀.length) (hle : ds₀.length ≤ ds.length)
    (proof : List ByteArray)
    (hacc : verifyConsistency H ds₀.length ds.length (MTH H ds₀) (MTH H ds)
        proof = true) :
    ds₀ = ds.take ds₀.length := by
  rcases consistency_sound H ℓ hw ds₀ ds hm hle proof hacc with heq | ⟨x, y, hne, heq⟩
  · exact heq
  · exact False.elim (hne (hinj x y heq))

end Merkle
