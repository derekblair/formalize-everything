# RFC 6962 vector inventory

The default `lake build` checks **28 symbolic shape equalities** in
[`Merkle/Vectors.lean`](Merkle/Vectors.lean), plus **16 concrete verifier
regressions** in [`Merkle/VerifierCases.lean`](Merkle/VerifierCases.lean), and
**one shifted-parse inclusion attack with seven checked facts** in
[`Merkle/InclusionAttack.lean`](Merkle/InclusionAttack.lean).
The symbolic vectors quantify over every `H : ByteArray → ByteArray` and
arbitrary input bytes `d0` through `d6`; only list lengths and indices are
fixed. They check exact expressions, not sampled digest values.

The source is the [published RFC 6962 text](https://www.rfc-editor.org/rfc/rfc6962.txt).
Its actual sections are §2.1 (MTH), §2.1.1 (audit paths), §2.1.2
(consistency proofs), and §2.1.3 (worked example). The numbering correction
relative to ticket #11 is explained in the README.

## Symbolic notation

Every expected leaf and internal hash in the Lean file is independently
expanded using these byte expressions:

```text
L(x)   = H(0x00 || x)
N(x,y) = H(0x01 || x || y)
```

For the seven-leaf worked example, the printed RFC names stand for:

```text
a=L(d0)  b=L(d1)  c=L(d2)  d=L(d3)  e=L(d4)  f=L(d5)  j=L(d6)
g=N(a,b)  h=N(c,d)  i=N(e,f)
k=N(g,h)  l=N(i,j)
hash0=N(g,c)  hash1=k  hash2=N(k,i)  hash=N(k,l)
```

`j` is a leaf hash. There is no additional hash at a unary node. `D7` below
means `[d0,d1,d2,d3,d4,d5,d6]`; ranges are half-open.

## The 28 symbolic vectors

All theorem names in this table have namespace prefix `Merkle.Vectors.`.

| # | Theorem | Expected expression or shape | RFC section |
|---|---|---|---|
| 1 | `leaf_prefix` | `leafHash H d0 = H(0x00 \|\| d0)` | §2.1 |
| 2 | `node_prefix` | `nodeHash H d0 d1 = H(0x01 \|\| d0 \|\| d1)` | §2.1 |
| 3 | `mth_empty` | `MTH([]) = H(empty bytes)`; no domain prefix | §2.1 |
| 4 | `mth_singleton` | `MTH([d0]) = a` | §2.1 |
| 5 | `mth_pair` | `MTH([d0,d1]) = g`; also pins the shape of `h` and `i` | §§2.1, 2.1.3 |
| 6 | `mth_three` | `MTH([d0,d1,d2]) = hash0 = N(g,c)` | §2.1.3 |
| 7 | `mth_four` | `MTH([d0,d1,d2,d3]) = hash1 = k` | §2.1.3 |
| 8 | `mth_six` | `MTH([d0,d1,d2,d3,d4,d5]) = hash2 = N(k,i)` | §2.1.3 |
| 9 | `mth_seven` | `MTH(D7) = N(k,l)` with every nested leaf/node hash expanded | §2.1.3 |
| 10 | `subtree_g` | `MTH(D7[0:2]) = g` | §§2.1, 2.1.3 |
| 11 | `subtree_h` | `MTH(D7[2:4]) = h` | §§2.1, 2.1.3 |
| 12 | `subtree_i` | `MTH(D7[4:6]) = i` | §§2.1, 2.1.3 |
| 13 | `subtree_j` | `MTH(D7[6:7]) = j` | §§2.1, 2.1.3 |
| 14 | `subtree_k` | `MTH(D7[0:4]) = k` | §§2.1, 2.1.3 |
| 15 | `subtree_l` | `MTH(D7[4:7]) = l` | §§2.1, 2.1.3 |
| 16 | `path_singleton` | `PATH(0,[d0]) = []` | §2.1.1 |
| 17 | `path_pair_left` | `PATH(0,[d0,d1]) = [b]` | §2.1.1 |
| 18 | `path_pair_right` | `PATH(1,[d0,d1]) = [a]` | §2.1.1 |
| 19 | `path_d0` | `PATH(0,D7) = [b,h,l]` | §2.1.3 |
| 20 | `path_d3` | `PATH(3,D7) = [c,g,l]` | §2.1.3 |
| 21 | `path_d4` | `PATH(4,D7) = [f,j,k]` | §2.1.3 |
| 22 | `path_d6` | `PATH(6,D7) = [i,k]` | §2.1.3 |
| 23 | `consistency_3_7` | `PROOF(3,D7) = [c,d,g,l]` | §2.1.3 |
| 24 | `consistency_4_7` | `PROOF(4,D7) = [l]`; known complete subtree `k` omitted | §2.1.3 |
| 25 | `consistency_6_7` | `PROOF(6,D7) = [i,j,k]` | §2.1.3 |
| 26 | `subproof_known` | `SUBPROOF(4,[d0,d1,d2,d3],true) = []` | §2.1.2 |
| 27 | `subproof_unknown` | `SUBPROOF(4,[d0,d1,d2,d3],false) = [k]` | §2.1.2 |
| 28 | `consistency_same` | `PROOF(7,D7) = []`, using the equal-size SUBPROOF base | §2.1.2; ticket's `m ≤ n` extension |

The first two use `rfl` directly. For the other 26, `conv => lhs; cbv`
uses the proof-producing `cbv` evaluator to unfold the well-founded defining equations on the left-hand side and
normalizes the concrete arithmetic and list operations. The conversion
closes the resulting equality by kernel reflexivity. No expected shape is
inferred from a completeness theorem or a previously proved shape theorem.
Changing a prefix byte, split, child order, sibling order, or seed omission
breaks the corresponding equality.

The printed RFC's complete example inventory is present: four audit paths,
three consistency proofs, the seven-leaf tree, and all three earlier
incremental trees (sizes 3, 4, and 6). Empty/singleton and both SUBPROOF base
flags come from the defining equations rather than the worked figure.

## The 16 supplemental verifier regressions

These use `diagnosticHash bytes = bytes` with one-byte leaves `10` through
`16` and are proved by `decide +kernel`. The hash exposes orientation and
prefix mistakes; it is not a cryptographic model or SHA-256 substitute.
The table's sections identify the algorithm being exercised; these concrete
mutations are local regression cases, not additional RFC-published vectors.
All names have namespace prefix `Merkle.VerifierCases.`.

| # | Theorem | Expected result | RFC algorithm |
|---|---|---|---|
| 1 | `audit_honest_seven` | Accept index 6 in a seven-leaf tree | §2.1.1 |
| 2 | `audit_empty` | Reject an audit request for an empty tree | §2.1.1 |
| 3 | `audit_out_of_range` | Reject index 7 in a seven-leaf tree | §2.1.1 |
| 4 | `audit_missing_sibling` | Reject a shortened honest proof | §2.1.1 |
| 5 | `audit_extra_sibling` | Reject an honest proof with a trailing node | §2.1.1 |
| 6 | `audit_wrong_root` | Reject a root unequal to the recomputed root | §2.1.1 |
| 7 | `audit_swapped_orientation` | Reject the left leaf presented at the right index | §2.1.1 |
| 8 | `consistency_zero` | Reject an old size of zero | §2.1.2 |
| 9 | `consistency_oversized` | Reject old size 8 with new size 7 | §2.1.2 |
| 10 | `consistency_equal_empty` | Accept equal nonzero sizes and roots with no proof nodes | §2.1.2 base case |
| 11 | `consistency_equal_extra` | Reject equal sizes with a redundant proof node | §2.1.2 base case |
| 12 | `consistency_missing_node` | Reject a shortened 3-to-7 proof | §2.1.2 |
| 13 | `consistency_extra_node` | Reject a 3-to-7 proof with a trailing node | §2.1.2 |
| 14 | `consistency_wrong_old_root` | Reject an incorrect old root | §2.1.2 |
| 15 | `consistency_wrong_new_root` | Reject an incorrect new root | §2.1.2 |
| 16 | `consistency_four_seed_omitted` | Accept 4-to-7 with exactly the right subtree root | §§2.1.2, 2.1.3 |

These examples supplement the general completeness theorems. They do not
prove general rejection of forged proofs; M2a's separate soundness theorems
extract a collision under `FixedWidth`. Concrete SHA-256 numeric vectors are deferred until a verified
SHA-256 implementation is introduced, as required by the hash-abstract design.

## M2a inclusion attack: why width is a hypothesis

This local regression records the digest-width abstraction gap **D1** and the
insufficiency of injectivity alone (**D2**); it is not an RFC-published vector or
an attack on SHA-256. All theorem names below have prefix
`Merkle.InclusionAttack.`. `diagnosticHash` is the existing identity hash from
`Merkle.VerifierCases`.

The honest list is `[#[0x78], #[0x79]]`, with root `01 00 78 00 79`.
The supplied leaf is empty, its index is `0`, and the proof has one element,
`#[0x78, 0x00, 0x79]`. The verifier parses the same root bytes as
`01 | 00 | 78 00 79`, shifting the child boundary from the honest split
`01 | 00 78 | 00 79`.

| Theorem | Checked fact |
|---|---|
| `honest_root_bytes` | The honest root is exactly `01 00 78 00 79`. |
| `shifted_parse_accepts` | The unchanged verifier accepts the empty leaf and supplied proof against that honest root, at the honest tree size. |
| `shifted_parse_leaf_ne` | The accepted empty leaf differs from the committed leaf at index `0`. |
| `diagnosticHash_injective` | Equal outputs of the identity hash imply equal inputs. |
| `diagnosticHash_no_collision` | No witness of `Collides diagnosticHash` exists. |
| `diagnosticHash_not_fixedWidth` | No `ℓ` gives this hash fixed output width. |
| `shifted_parse_attack` | The acceptance, differing leaf, injectivity, absence of collisions, and absence of fixed width hold together. |

The three concrete byte/verifier assertions use `decide +kernel`; the remaining
facts use direct proofs and kernel-checked arithmetic. No compiled evaluator
is trusted as a proof oracle. The attack demonstrates that dropping the width
hypothesis from the inclusion theorem would make its statement false.
