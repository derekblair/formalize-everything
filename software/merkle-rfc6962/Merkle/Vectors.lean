import Merkle.Spec

/-!
Symbolic RFC 6962 vectors. The input leaves and hash function are arbitrary;
only tree sizes and indices are concrete. Expected expressions spell out
prefix bytes independently of the implementation's hashing helpers.
The proof-producing `cbv` evaluator unfolds the well-founded defining equations
in the left-hand side;
`conv` then closes each definitional equality by kernel reflexivity.
-/
namespace Merkle.Vectors

private abbrev L (H : Hash) (d : ByteArray) := H (ByteArray.mk #[0] ++ d)
private abbrev N (H : Hash) (l r : ByteArray) := H (ByteArray.mk #[1] ++ l ++ r)

variable (H : Hash) (d0 d1 d2 d3 d4 d5 d6 : ByteArray)

/-- §2.1: a leaf has a one-byte 0x00 prefix. -/
theorem leaf_prefix : leafHash H d0 = H (ByteArray.mk #[0] ++ d0) := rfl

/-- §2.1: an internal node has a one-byte 0x01 prefix, left then right. -/
theorem node_prefix : nodeHash H d0 d1 = H (ByteArray.mk #[1] ++ d0 ++ d1) := rfl

/-- §2.1: the empty tree hashes the empty byte string, with no prefix. -/
theorem mth_empty : MTH H [] = H (ByteArray.mk #[]) := by
  conv => lhs; cbv

/-- §2.1: a singleton is a leaf hash. -/
theorem mth_singleton : MTH H [d0] = L H d0 := by
  conv => lhs; cbv

/-- §2.1/§2.1.3: the two-leaf shape of g, h, and i. -/
theorem mth_pair : MTH H [d0, d1] = N H (L H d0) (L H d1) := by
  conv => lhs; cbv

/-- §2.1.3: hash0; also the same shape as the right subtree l. -/
theorem mth_three : MTH H [d0, d1, d2] =
    N H (N H (L H d0) (L H d1)) (L H d2) := by
  conv => lhs; cbv

/-- §2.1.3: hash1 = k; a power-of-two length splits strictly below itself. -/
theorem mth_four : MTH H [d0, d1, d2, d3] =
    N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3)) := by
  conv => lhs; cbv

/-- §2.1.3: hash2. -/
theorem mth_six : MTH H [d0, d1, d2, d3, d4, d5] =
    N H (N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3)))
      (N H (L H d4) (L H d5)) := by
  conv => lhs; cbv

/-- §2.1.3: the complete worked seven-leaf tree. -/
theorem mth_seven : MTH H [d0, d1, d2, d3, d4, d5, d6] =
    N H (N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3)))
      (N H (N H (L H d4) (L H d5)) (L H d6)) := by
  conv => lhs; cbv

/-- §2.1's half-open interval notation, applied to §2.1.3's g. -/
theorem subtree_g : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 0 2 =
    N H (L H d0) (L H d1) := by
  conv => lhs; cbv

/-- §2.1.3: h = MTH(D[2:4]). -/
theorem subtree_h : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 2 4 =
    N H (L H d2) (L H d3) := by
  conv => lhs; cbv

/-- §2.1.3: i = MTH(D[4:6]). -/
theorem subtree_i : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 4 6 =
    N H (L H d4) (L H d5) := by
  conv => lhs; cbv

/-- §2.1.3: j = MTH(D[6:7]) is a leaf, not a unary internal node. -/
theorem subtree_j : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 6 7 =
    L H d6 := by
  conv => lhs; cbv

/-- §2.1.3: k = MTH(D[0:4]). -/
theorem subtree_k : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 0 4 =
    N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3)) := by
  conv => lhs; cbv

/-- §2.1.3: l = MTH(D[4:7]). -/
theorem subtree_l : subtreeMTH H [d0, d1, d2, d3, d4, d5, d6] 4 7 =
    N H (N H (L H d4) (L H d5)) (L H d6) := by
  conv => lhs; cbv

/-- §2.1.1: singleton audit paths are empty. -/
theorem path_singleton : PATH H 0 [d0] = [] := by
  conv => lhs; cbv

/-- §2.1.1: the left leaf's sibling is on its right. -/
theorem path_pair_left : PATH H 0 [d0, d1] = [L H d1] := by
  conv => lhs; cbv

/-- §2.1.1: the right leaf's sibling is on its left. -/
theorem path_pair_right : PATH H 1 [d0, d1] = [L H d0] := by
  conv => lhs; cbv

/-- §2.1.3: PATH(0,D[7]) = [b,h,l], in leaf-to-root order. -/
theorem path_d0 : PATH H 0 [d0, d1, d2, d3, d4, d5, d6] =
    [L H d1, N H (L H d2) (L H d3),
      N H (N H (L H d4) (L H d5)) (L H d6)] := by
  conv => lhs; cbv

/-- §2.1.3: PATH(3,D[7]) = [c,g,l]. -/
theorem path_d3 : PATH H 3 [d0, d1, d2, d3, d4, d5, d6] =
    [L H d2, N H (L H d0) (L H d1),
      N H (N H (L H d4) (L H d5)) (L H d6)] := by
  conv => lhs; cbv

/-- §2.1.3: PATH(4,D[7]) = [f,j,k]. -/
theorem path_d4 : PATH H 4 [d0, d1, d2, d3, d4, d5, d6] =
    [L H d5, L H d6,
      N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3))] := by
  conv => lhs; cbv

/-- §2.1.3: PATH(6,D[7]) = [i,k]. -/
theorem path_d6 : PATH H 6 [d0, d1, d2, d3, d4, d5, d6] =
    [N H (L H d4) (L H d5),
      N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3))] := by
  conv => lhs; cbv

/-- §2.1.3: PROOF(3,D[7]) = [c,d,g,l]. -/
theorem consistency_3_7 : consistencyProof H 3 [d0, d1, d2, d3, d4, d5, d6] =
    [L H d2, L H d3, N H (L H d0) (L H d1),
      N H (N H (L H d4) (L H d5)) (L H d6)] := by
  conv => lhs; cbv

/-- §2.1.3: PROOF(4,D[7]) = [l]; k is already known and omitted. -/
theorem consistency_4_7 : consistencyProof H 4 [d0, d1, d2, d3, d4, d5, d6] =
    [N H (N H (L H d4) (L H d5)) (L H d6)] := by
  conv => lhs; cbv

/-- §2.1.3: PROOF(6,D[7]) = [i,j,k]. -/
theorem consistency_6_7 : consistencyProof H 6 [d0, d1, d2, d3, d4, d5, d6] =
    [N H (L H d4) (L H d5), L H d6,
      N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3))] := by
  conv => lhs; cbv

/-- §2.1.2: the known complete subtree contributes no proof node. -/
theorem subproof_known : SUBPROOF H 4 [d0, d1, d2, d3] true = [] := by
  conv => lhs; cbv

/-- §2.1.2: the unknown complete subtree contributes exactly its root. -/
theorem subproof_unknown : SUBPROOF H 4 [d0, d1, d2, d3] false =
    [N H (N H (L H d0) (L H d1)) (N H (L H d2) (L H d3))] := by
  conv => lhs; cbv

/-- §2.1.2's SUBPROOF base case extends PROOF to equal sizes. -/
theorem consistency_same : consistencyProof H 7 [d0, d1, d2, d3, d4, d5, d6] =
    [] := by
  conv => lhs; cbv

end Merkle.Vectors
