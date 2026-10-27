import Merkle.Spec

namespace Merkle

/-- An explicit collision for the abstract hash. This is a proposition, not an axiom. -/
def Collides (H : Hash) : Prop := ∃ x y : ByteArray, x ≠ y ∧ H x = H y

/-- Every hash output has the given byte width (32 for RFC 6962's SHA-256).
Soundness takes this as a hypothesis; the verifier does not assume it. -/
def FixedWidth (H : Hash) (ℓ : Nat) : Prop := ∀ x : ByteArray, (H x).size = ℓ

/-- The empty-tree input cannot be a tagged leaf input. -/
theorem empty_ne_leaf (d : ByteArray) :
    ByteArray.mk #[] ≠ ByteArray.mk #[0] ++ d := by
  intro h
  have hs := congrArg ByteArray.size h
  simp only [ByteArray.size_append] at hs
  change 0 = 1 + d.size at hs
  omega

/-- The empty-tree input cannot be a tagged internal-node input. -/
theorem empty_ne_node (a b : ByteArray) :
    ByteArray.mk #[] ≠ ByteArray.mk #[1] ++ a ++ b := by
  intro h
  have hs := congrArg ByteArray.size h
  simp only [ByteArray.size_append] at hs
  change 0 = 1 + a.size + b.size at hs
  omega

/-- Leaf and internal-node inputs have different first bytes. -/
theorem leaf_ne_node (d a b : ByteArray) :
    ByteArray.mk #[0] ++ d ≠ ByteArray.mk #[1] ++ a ++ b := by
  intro h
  have ht := congrArg (fun x : ByteArray => x.data.toList) h
  simp at ht

/-- A fixed leaf tag can be cancelled without any width hypothesis. -/
theorem leaf_inj {d d' : ByteArray}
    (h : ByteArray.mk #[0] ++ d = ByteArray.mk #[0] ++ d') : d = d' := by
  exact (ByteArray.append_right_inj _).mp h

/-- Node children are recovered when only the left pair has equal widths.
The right child may be an arbitrary adversarial proof node. -/
theorem node_inj_left {a b a' b' : ByteArray} (hw : a.size = a'.size)
    (h : ByteArray.mk #[1] ++ a ++ b = ByteArray.mk #[1] ++ a' ++ b') :
    a = a' ∧ b = b' := by
  rw [ByteArray.append_assoc, ByteArray.append_assoc] at h
  exact (ByteArray.append_eq_append_iff_of_size_eq_left hw).mp
    ((ByteArray.append_right_inj _).mp h)

/-- Node children are recovered when only the right pair has equal widths.
The left child may be an arbitrary adversarial proof node. -/
theorem node_inj_right {a b a' b' : ByteArray} (hw : b.size = b'.size)
    (h : ByteArray.mk #[1] ++ a ++ b = ByteArray.mk #[1] ++ a' ++ b') :
    a = a' ∧ b = b' := by
  rw [ByteArray.append_assoc, ByteArray.append_assoc] at h
  exact (ByteArray.append_eq_append_iff_of_size_eq_right hw).mp
    ((ByteArray.append_right_inj _).mp h)

/-- Equal leaf hashes recover their data or exhibit the two colliding inputs. -/
theorem leafHash_eq (H : Hash) {d d' : ByteArray}
    (h : leafHash H d = leafHash H d') : d = d' ∨ Collides H := by
  by_cases hi : ByteArray.mk #[0] ++ d = ByteArray.mk #[0] ++ d'
  · exact Or.inl (leaf_inj hi)
  · exact Or.inr ⟨_, _, hi, h⟩

/-- Equal node hashes recover their children or exhibit a collision, using
only the left pair's width equality. -/
theorem nodeHash_eq_left (H : Hash) {a b a' b' : ByteArray}
    (hw : a.size = a'.size) (h : nodeHash H a b = nodeHash H a' b') :
    (a = a' ∧ b = b') ∨ Collides H := by
  by_cases hi : ByteArray.mk #[1] ++ a ++ b = ByteArray.mk #[1] ++ a' ++ b'
  · exact Or.inl (node_inj_left hw hi)
  · exact Or.inr ⟨_, _, hi, h⟩

/-- Equal node hashes recover their children or exhibit a collision, using
only the right pair's width equality. -/
theorem nodeHash_eq_right (H : Hash) {a b a' b' : ByteArray}
    (hw : b.size = b'.size) (h : nodeHash H a b = nodeHash H a' b') :
    (a = a' ∧ b = b') ∨ Collides H := by
  by_cases hi : ByteArray.mk #[1] ++ a ++ b = ByteArray.mk #[1] ++ a' ++ b'
  · exact Or.inl (node_inj_right hw hi)
  · exact Or.inr ⟨_, _, hi, h⟩

theorem leafHash_size (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ) (d : ByteArray) :
    (leafHash H d).size = ℓ := hw _

theorem nodeHash_size (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ) (a b : ByteArray) :
    (nodeHash H a b).size = ℓ := hw _

/-- Every branch of MTH returns a hash output, including the empty tree. -/
theorem MTH_size (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ) (ds : List ByteArray) :
    (MTH H ds).size = ℓ := by
  rw [MTH]
  split
  · exact hw _
  · split
    · exact leafHash_size H ℓ hw _
    · exact nodeHash_size H ℓ hw _ _

end Merkle
