import Merkle.AuditStructure

namespace Merkle

/-- An arbitrary successful walk against an honest tree either reaches the same
leaf hash or exposes two distinct inputs with the same hash. The unused proof
suffix is unrestricted; sibling nodes need not themselves be hash outputs. -/
theorem auditWalk_extract (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (n m : Nat) (leaf : ByteArray) (proof : List ByteArray)
    (r : ByteArray) (rest : List ByteArray) (hmn : m < n)
    (hwalk : auditWalk H m n leaf proof = some (r, rest))
    (ds : List ByteArray) (hn : ds.length = n) (hr : r = MTH H ds) :
    leafHash H leaf = leafHash H (ds[m]'(by omega)) ∨ Collides H := by
  induction n using Nat.strongRecOn generalizing m proof r rest ds with
  | ind n ih =>
    by_cases hn2 : 1 < n
    · have hk := split_lt hn2
      have hp := split_pos hn2
      have hlen : (ds.take (split n)).length = split n := by
        simp only [List.length_take, hn, Nat.min_eq_left (Nat.le_of_lt hk)]
      have htree : MTH H ds =
          nodeHash H (MTH H (ds.take (split n))) (MTH H (ds.drop (split n))) := by
        simpa only [hn] using MTH_eq H ds (by omega)
      by_cases hmleft : m < split n
      · obtain ⟨child, sibling, hsub, hnode⟩ :=
          auditWalk_left_inv H m n leaf proof r rest hn2 hmleft hwalk
        have hhash := hnode.symm.trans (hr.trans htree)
        have hsize : child.size = (MTH H (ds.take (split n))).size :=
          (auditWalk_size H ℓ hw m (split n) leaf proof child (sibling :: rest) hsub).trans
            (MTH_size H ℓ hw (ds.take (split n))).symm
        rcases nodeHash_eq_left H hsize hhash with hchildren | hcollision
        · have hextract := ih (split n) hk m proof child (sibling :: rest)
            hmleft hsub (ds.take (split n)) hlen hchildren.1
          simpa only [List.getElem_take] using hextract
        · exact Or.inr hcollision
      · obtain ⟨child, sibling, hsub, hnode⟩ :=
          auditWalk_right_inv H m n leaf proof r rest hn2 hmleft hwalk
        have hhash := hnode.symm.trans (hr.trans htree)
        have hsize : child.size = (MTH H (ds.drop (split n))).size :=
          (auditWalk_size H ℓ hw (m - split n) (n - split n) leaf proof child
            (sibling :: rest) hsub).trans (MTH_size H ℓ hw (ds.drop (split n))).symm
        rcases nodeHash_eq_right H hsize hhash with hchildren | hcollision
        · have hmr : m - split n < n - split n := by omega
          have hdrop : (ds.drop (split n)).length = n - split n := by
            simp only [List.length_drop, hn]
          have hidx : split n + (m - split n) = m := by omega
          have hextract := ih (n - split n) (by omega) (m - split n) proof child
            (sibling :: rest) hmr hsub (ds.drop (split n)) hdrop hchildren.2
          simpa only [List.getElem_drop, hidx] using hextract
        · exact Or.inr hcollision
    · have hn1 : n = 1 := by omega
      have hm0 : m = 0 := by omega
      subst m
      have hroot := (auditWalk_one_inv H 0 leaf proof r rest
        (by simpa only [hn1] using hwalk)).1
      have htree : MTH H ds = leafHash H (ds[0]'(by omega)) := by
        rw [MTH]
        simp only [hn, hn1, Nat.one_ne_zero, ↓reduceDIte]
      exact Or.inl (hroot.symm.trans (hr.trans htree))

/-- Inclusion soundness with an explicit collision alternative. The verifier's
tree size is the honest leaf-list length; the proof is completely arbitrary. -/
theorem audit_sound (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds : List ByteArray) (m : Nat) (hm : m < ds.length)
    (leaf : ByteArray) (proof : List ByteArray)
    (hacc : verifyAudit H m ds.length leaf proof (MTH H ds) = true) :
    leaf = ds[m] ∨ Collides H := by
  unfold verifyAudit at hacc
  rw [ite_eq_left hm] at hacc
  cases hwalk : auditWalk H m ds.length leaf proof with
  | none => simp [hwalk] at hacc
  | some result =>
    rcases result with ⟨r, rest⟩
    cases rest with
    | nil =>
      have hr : r = MTH H ds := by simpa only [hwalk, decide_eq_true_eq] using hacc
      rcases auditWalk_extract H ℓ hw ds.length m leaf proof r [] hm hwalk ds rfl hr
          with hleaf | hcollision
      · exact leafHash_eq H hleaf
      · exact Or.inr hcollision
    | cons sibling rest => simp [hwalk] at hacc

/-- The requested injectivity corollary. Global injectivity is an idealized
hypothesis, not a cryptographic claim about a fixed-width digest function. -/
theorem audit_sound_of_injective (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (hinj : ∀ x y : ByteArray, H x = H y → x = y)
    (ds : List ByteArray) (m : Nat) (hm : m < ds.length)
    (leaf : ByteArray) (proof : List ByteArray)
    (hacc : verifyAudit H m ds.length leaf proof (MTH H ds) = true) :
    leaf = ds[m] := by
  rcases audit_sound H ℓ hw ds m hm leaf proof hacc with heq | ⟨x, y, hne, heq⟩
  · exact heq
  · exact False.elim (hne (hinj x y heq))

end Merkle
