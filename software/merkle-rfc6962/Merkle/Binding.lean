import Merkle.ByteAlgebra

namespace Merkle

/-- Equal roots bind the complete leaf lists, or expose a hash collision.
The lists may have different lengths: tag separation distinguishes empty trees,
leaves, and internal nodes, and fixed width recovers the two node children. -/
theorem mth_binding (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds ds' : List ByteArray) (h : MTH H ds = MTH H ds') :
    ds = ds' ∨ Collides H := by
  cases hds : ds with
  | nil =>
    cases hds' : ds' with
    | nil => exact Or.inl rfl
    | cons d tail =>
      cases htail : tail with
      | nil =>
        exact Or.inr ⟨_, _, empty_ne_leaf d,
          by simpa only [hds, hds', htail, MTH_nil, MTH_singleton, leafHash] using h⟩
      | cons e tail =>
        rw [hds, hds', htail, MTH_nil, MTH_eq H (d :: e :: tail) (by simp)] at h
        exact Or.inr ⟨_, _, empty_ne_node _ _, h⟩
  | cons d tail =>
    cases htail : tail with
    | nil =>
      cases hds' : ds' with
      | nil =>
        exact Or.inr ⟨_, _, empty_ne_leaf d,
          by simpa only [hds, hds', htail, MTH_nil, MTH_singleton, leafHash] using h.symm⟩
      | cons d' tail' =>
        cases htail' : tail' with
        | nil =>
          rcases leafHash_eq H
              (by simpa only [hds, hds', htail, htail', MTH_singleton] using h) with hd | hc
          · exact Or.inl (by rw [hd])
          · exact Or.inr hc
        | cons e' tail' =>
          rw [hds, hds', htail, htail', MTH_singleton, MTH_eq H (d' :: e' :: tail') (by simp)] at h
          exact Or.inr ⟨_, _, leaf_ne_node _ _ _, h⟩
    | cons e tail =>
      cases hds' : ds' with
      | nil =>
        rw [hds, hds', htail, MTH_nil, MTH_eq H (d :: e :: tail) (by simp)] at h
        exact Or.inr ⟨_, _, empty_ne_node _ _, h.symm⟩
      | cons d' tail' =>
        cases htail' : tail' with
        | nil =>
          rw [hds, hds', htail, htail', MTH_singleton, MTH_eq H (d :: e :: tail) (by simp)] at h
          exact Or.inr ⟨_, _, leaf_ne_node _ _ _, h.symm⟩
        | cons e' tail' =>
          have hn : 1 < (d :: e :: tail).length := by simp
          have hn' : 1 < (d' :: e' :: tail').length := by simp
          rw [hds, hds', htail, htail', MTH_eq H _ hn, MTH_eq H _ hn'] at h
          have hsize :
              (MTH H ((d :: e :: tail).take (split (d :: e :: tail).length))).size =
              (MTH H ((d' :: e' :: tail').take (split (d' :: e' :: tail').length))).size :=
            (MTH_size H ℓ hw _).trans (MTH_size H ℓ hw _).symm
          rcases nodeHash_eq_left H hsize h with hchildren | hc
          · rcases mth_binding H ℓ hw _ _ hchildren.1 with hleft | hc
            · rcases mth_binding H ℓ hw _ _ hchildren.2 with hright | hc
              · exact Or.inl (by
                  calc
                    d :: e :: tail =
                        (d :: e :: tail).take (split (d :: e :: tail).length) ++
                        (d :: e :: tail).drop (split (d :: e :: tail).length) :=
                      (List.take_append_drop _ _).symm
                    _ = (d' :: e' :: tail').take (split (d' :: e' :: tail').length) ++
                        (d' :: e' :: tail').drop (split (d' :: e' :: tail').length) := by
                      rw [hleft, hright]
                    _ = d' :: e' :: tail' := List.take_append_drop _ _)
              · exact Or.inr hc
            · exact Or.inr hc
          · exact Or.inr hc
termination_by ds.length + ds'.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop]
    have hk := split_lt (n := (d :: e :: tail).length) (by simp)
    have hk' := split_lt (n := (d' :: e' :: tail').length) (by simp)
    have hp := split_pos (n := (d :: e :: tail).length) (by simp)
    have hp' := split_pos (n := (d' :: e' :: tail').length) (by simp)
    simp_all only [List.length_cons]
    omega

/-- Binding with collisions ruled out by the requested idealized injectivity
hypothesis. No injectivity or collision-resistance property is assumed globally. -/
theorem mth_binding_of_injective (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (hinj : ∀ x y : ByteArray, H x = H y → x = y)
    (ds ds' : List ByteArray) (h : MTH H ds = MTH H ds') : ds = ds' := by
  rcases mth_binding H ℓ hw ds ds' h with heq | ⟨x, y, hne, heq⟩
  · exact heq
  · exact False.elim (hne (hinj x y heq))

end Merkle
