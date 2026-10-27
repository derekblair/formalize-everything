# Merkle proofs (RFC 6962), milestones 1 and 2

A standalone Lean 4.34.1 project for the Merkle tree algorithms in
[RFC 6962](https://www.rfc-editor.org/rfc/rfc6962.txt), implementing
[programme ticket #11](https://github.com/derekblair/formalize-everything/issues/11),
[ticket #19](https://github.com/derekblair/formalize-everything/issues/19),
and [ticket #22](https://github.com/derekblair/formalize-everything/issues/22).
It defines tree hashes, audit paths, consistency proofs, and executable
verifiers, with general completeness proofs for arbitrary hashes and leaf lists.
Milestone 2 adds collision-explicit inclusion soundness, tree binding, and
consistency soundness under an explicit fixed-digest-width hypothesis.
Milestone 2a supplied inclusion; milestone 2b supplies binding and consistency.

The hash is an explicit parameter `H : ByteArray → ByteArray`. There is no
SHA-256 implementation. The milestone-1 definitions and completeness theorems
use no digest-width or collision-resistance assumption. Completeness concerns
the algorithms' structure and holds even for a poor hash function. The executable verifiers actually
reconstruct and compare roots; they receive sizes, supplied roots, and proof
nodes, not the original leaf list or a proof-generation oracle.

## Source coverage

| Printed RFC section | Coverage |
|---|---|
| §2.1, Merkle Hash Trees | Empty and singleton hashes; exact `0x00` leaf and `0x01` internal-node prefixes; largest-power-of-two split; half-open subtree ranges; collision-explicit tree binding under fixed digest width. |
| §2.1.1, Merkle Audit Paths | Literal `PATH` recursion and the prose root-recomputation procedure; completeness for every valid leaf index; collision-explicit soundness under fixed digest width. |
| §2.1.2, Merkle Consistency Proofs | Literal `SUBPROOF` recursion, including its Boolean known-root flag; two-root reconstruction and comparison; completeness for every `0 < m ≤ n`; collision-explicit consistency soundness for two arbitrary committed leaf lists under fixed digest width. |
| §2.1.3, Example | All four published audit paths, all three published consistency proofs, the seven-leaf tree and its subtrees, and the three earlier incremental trees. |
| §2.1.4, Signatures | Outside this algorithm milestone; the printed section concerns signature algorithms. |

The ticket and build brief associate audit and consistency algorithms with
§§2.1.3–2.1.4. In the downloaded RFC 6962 text those algorithms are actually
§§2.1.1–2.1.2; §2.1.3 supplies the worked shapes. The implementation follows
the requested algorithms and those printed definitions, not the mismatched
section labels. It does not import RFC 9162 algorithms.

## The three recursions

Let `D` be the ordered leaf list, `n = D.length`, `L(d) = H(0x00 || d)`,
and `N(l,r) = H(0x01 || l || r)`. For `n > 1`, the split is
`k = 2 ^ (n - 1).log2`. `split_spec` and `split_largest` prove that it is a
power of two, `k < n ≤ 2k`, and every power of two strictly below `n` is at
most `k`. No balancing, padding, or duplicate-last-leaf rule is used.

```text
MTH([])  = H(empty bytes)
MTH([d]) = L(d)
MTH(D)   = N(MTH(D.take k), MTH(D.drop k))                 (n > 1)

PATH(0, [d]) = []
PATH(m, D) = PATH(m, D.take k) ++ [MTH(D.drop k)]          (m < k)
PATH(m, D) = PATH(m-k, D.drop k) ++ [MTH(D.take k)]        (k ≤ m)

SUBPROOF(m, D, true)  = []                               (m = n)
SUBPROOF(m, D, false) = [MTH(D)]                         (m = n)
SUBPROOF(m, D, b) = SUBPROOF(m, D.take k, b)
                    ++ [MTH(D.drop k)]                  (m < n, m ≤ k)
SUBPROOF(m, D, b) = SUBPROOF(m-k, D.drop k, false)
                    ++ [MTH(D.take k)]                  (m < n, k < m)

consistencyProof(H, m, D) = SUBPROOF(H, m, D, true)
```

`subtreeMTH H D lo hi` is `MTH H ((D.drop lo).take (hi-lo))`, corresponding
to the RFC's half-open interval `D[lo:hi]` when `lo ≤ hi ≤ D.length`.
All three recursions terminate by decreasing list length. Their source is
[`Merkle/Spec.lean`](Merkle/Spec.lean).

## Verifiers and completeness

`verifyAudit H m n leaf proof root` checks `m < n`, follows the branch
determined by `m`, `n`, and the same split rule, hashes the supplied leaf, and
combines each sibling on the correct side while unwinding. It accepts only
if every proof node is consumed and the computed root equals `root`.

`verifyConsistency H m n oldRoot newRoot proof` checks `0 < m ≤ n` and
reconstructs both roots. A left branch preserves the old root and extends
the current root with a right sibling. A right branch prefixes the same
left sibling to both reconstructed roots. At an equal-size base, the known
root supplies both values if `b = true`; otherwise a proof node supplies
them. Acceptance requires complete consumption and equality with both
advertised roots. Missing or extra nodes are rejected. For equal nonzero
sizes, acceptance requires an empty proof and equal roots.

These are the completeness statements verbatim, in namespace `Merkle`:

```lean
theorem audit_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (hm : m < ds.length) :
    verifyAudit H m ds.length ds[m] (PATH H m ds) (MTH H ds) = true

theorem consistency_complete (H : Hash) (ds : List ByteArray) (m : Nat)
    (hm : 0 < m) (hmn : m ≤ ds.length) :
    verifyConsistency H m ds.length (MTH H (ds.take m)) (MTH H ds)
      (consistencyProof H m ds) = true
```

The proofs use stronger internal statements that reconstruct the expected
root or pair of roots and leave an arbitrary appended proof suffix untouched.
They therefore establish exact proof consumption as well as root equality.
The public statements have only the RFC's size/index hypotheses and quantify
over every `H` and every list of `ByteArray` leaves.

## Soundness, tree binding, and fidelity deviations D1/D2

Milestone 2a adds these definitions as ordinary propositions, not axioms:

```lean
def Collides (H : Hash) : Prop := ∃ x y : ByteArray, x ≠ y ∧ H x = H y
def FixedWidth (H : Hash) (ℓ : Nat) : Prop := ∀ x : ByteArray, (H x).size = ℓ
```

The primary theorem in [`Merkle/Soundness.lean`](Merkle/Soundness.lean) accepts an
arbitrary proof against the honest root of a universally quantified leaf list:

```lean
theorem audit_sound (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds : List ByteArray) (m : Nat) (hm : m < ds.length)
    (leaf : ByteArray) (proof : List ByteArray)
    (hacc : verifyAudit H m ds.length leaf proof (MTH H ds) = true) :
    leaf = ds[m] ∨ Collides H

theorem audit_sound_of_injective (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (hinj : ∀ x y : ByteArray, H x = H y → x = y)
    (ds : List ByteArray) (m : Nat) (hm : m < ds.length)
    (leaf : ByteArray) (proof : List ByteArray)
    (hacc : verifyAudit H m ds.length leaf proof (MTH H ds) = true) :
    leaf = ds[m]
```

The tree size is tied to `ds.length`; it is part of the honest commitment
assumption. No hypothesis says that the supplied proof came from `PATH` or that
its siblings have a prescribed width. The strengthened `auditWalk_extract` lemma
allows any unconsumed proof suffix. Exact consumption is enforced by the existing
verifier, but is not needed for the extraction argument.

[`Merkle/ByteAlgebra.lean`](Merkle/ByteAlgebra.lean) separates the empty, leaf, and
node input encodings, cancels the leaf tag, and recovers both children from equal
node inputs when either the left pair or the right pair has equal widths.
[`Merkle/AuditStructure.lean`](Merkle/AuditStructure.lean) inverts the walk branches
and proves every successful walk output has width `ℓ`. At each inclusion step,
equal hash outputs either expose distinct node inputs (an explicit collision) or
force the traversed child to equal its honest subtree root. At the leaf, differing
leaf inputs with equal hashes provide the remaining collision case.

Milestone 2b adds tree binding in [`Merkle/Binding.lean`](Merkle/Binding.lean)
and consistency soundness in
[`Merkle/ConsistencySoundness.lean`](Merkle/ConsistencySoundness.lean):

```lean
theorem mth_binding (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds ds' : List ByteArray) (h : MTH H ds = MTH H ds') :
    ds = ds' ∨ Collides H

theorem consistency_sound (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (ds₀ ds : List ByteArray) (hm : 0 < ds₀.length) (hle : ds₀.length ≤ ds.length)
    (proof : List ByteArray)
    (hacc : verifyConsistency H ds₀.length ds.length (MTH H ds₀) (MTH H ds)
        proof = true) :
    ds₀ = ds.take ds₀.length ∨ Collides H

theorem consistency_sound_of_injective (H : Hash) (ℓ : Nat) (hw : FixedWidth H ℓ)
    (hinj : ∀ x y : ByteArray, H x = H y → x = y)
    (ds₀ ds : List ByteArray) (hm : 0 < ds₀.length) (hle : ds₀.length ≤ ds.length)
    (proof : List ByteArray)
    (hacc : verifyConsistency H ds₀.length ds.length (MTH H ds₀) (MTH H ds)
        proof = true) :
    ds₀ = ds.take ds₀.length
```

Binding permits arbitrary list lengths, including empty lists and differently
shaped trees. It descends through equal node inputs using the fixed child widths;
different empty/leaf/node inputs with equal hash outputs produce the explicit
collision. `mth_binding_of_injective` removes that alternative under the same
global injectivity premise as the other corollaries.

Consistency uses two independent universally quantified leaf lists, with both
advertised sizes tied to their lengths. The proof list is arbitrary, without any
assumption that it came from `SUBPROOF` or `consistencyProof`. The strengthened
pair-form `consistencyRoots_extract` allows an arbitrary unconsumed suffix. Tree
binding is used both at the equal-size base and in a right branch to identify
the shared left subtree, which the verifier never traverses.

[`Merkle/ConsistencyStructure.lean`](Merkle/ConsistencyStructure.lean) inverts
the two recursive branches and establishes the conditional structural facts:
under `FixedWidth H ℓ`, when `m < n`, the returned current root has width `ℓ`;
when `m = n`, the returned
old and current roots are equal. There is no unconditional output-width claim:
the equal-size `b = false` base returns an arbitrary proof seed unhashed. In a
right branch, extraction first splits the current equation using its right
child's known width, then uses the recovered sibling width to split the old
equation from the left. In a left branch, the current child has width either
from the strict-size structural fact or, at equal sizes, from its equality to
the honestly committed old root.

**D1 — Digest-width abstraction gap.** RFC 6962 §2.1 fixes SHA-256's 32-byte output;
milestone 1 deliberately abstracted away that width. Leaf/node tag separation
alone does not make two concatenated variable-width children unambiguous.
[`Merkle/InclusionAttack.lean`](Merkle/InclusionAttack.lean) checks the obstruction
with the identity hash. The honest leaves `[78]`, `[79]` have root
`01 00 78 00 79`. At index zero, the empty forged leaf and the one-element proof
`[78 00 79]` reach the same bytes by splitting them as `01 | 00 | 78 00 79`.
The verifier accepts, the leaf differs from the committed leaf, and the identity
hash is injective and has no collisions. The file also proves that this hash has
no fixed width. `FixedWidth H ℓ` is therefore an explicit hypothesis of the
soundness and binding statements, rather than a change to any verifier
definition. The parameter permits `ℓ = 32`, but no SHA-256 instantiation is
supplied here.

[`Merkle/ConsistencyAttack.lean`](Merkle/ConsistencyAttack.lean) checks the
same D1 obstruction for consistency: `ds₀ = [#[]]` has root `00`, while
`ds = [#[0x78], #[0x79]]` has root `01 00 78 00 79`. The proof
`[#[0x78, 0x00, 0x79]]` is accepted at sizes 1 and 2 although `ds₀ ≠ ds.take 1`.
It also checks a binding witness: `[#[0x78], #[0x00, 0x79]]` and
`[#[0x78, 0x00], #[0x79]]` are distinct lists with the same root
`01 00 78 00 00 79`. Both use the injective, collision-free identity hash.
Thus fixed width cannot be dropped from either consistency soundness or tree
binding, even when injectivity is assumed.

**D2 — M1 had no collision-resistance hypothesis.** `Collides` now names a pair
of distinct inputs with equal outputs. The injectivity corollaries add the global
condition `∀ x y, H x = H y → x = y`; it is not a computational or probabilistic
collision-resistance definition. Injectivity alone is insufficient, as D1 shows.
Moreover, global injectivity on arbitrarily long byte strings cannot coexist
with a fixed finite output width. These corollaries are formal conditional
statements, not instantiable SHA-256 security assumptions. The primary deliverables are the
explicit-collision theorems, proved from the tree and verifier hash inputs.

No milestone-1 definition in `Spec.lean`, `Audit.lean`, or `Consistency.lean`
changes; the milestone-2a proof modules also remain unchanged by milestone 2b.
This milestone introduces no node-ambiguity predicate or trichotomy.

## Interpretation decisions

1. The source's colon notation appends a sibling to the end of the recursively
   produced list. Proof nodes are stored and consumed from leaf toward root.
   The four worked audit paths pin this order.
2. The equal-size `SUBPROOF` clauses are separate Boolean cases. A complete
   subtree is omitted only when its root is already known (`b = true`).
   Descending right sets `b = false`, even if the resulting subtree size is
   a power of two. The worked `PROOF(4,D[7]) = [l]` confirms the omitted
   `k` node; `PROOF(3,D[7])` and `PROOF(6,D[7])` confirm required seed nodes.
3. RFC 6962 gives recursive generators and describes verification in prose;
   it does not print separate bitwise verifier pseudocode in these sections.
   The verifiers implement that prose by recursively following tree sizes
   and recomputing roots. No equivalence to another implementation's iterative
   verifier is claimed.
4. The RFC introduces `PROOF` for `0 < m < n`; ticket #11 requires
   `0 < m ≤ n`. The existing equal-size `SUBPROOF(..., true)` base extends
   the generator to `m = n`, and verification compares the two roots with
   an empty proof. The equal-size slice of consistency soundness uses
   `mth_binding`; it covers this extension beyond the RFC's printed `PROOF` domain.
5. To make generators total, `PATH` returns `[]` on lists of length at most
   one; `SUBPROOF` checks its equal-size base first and otherwise returns
   `[]` on lists of length at most one. Values at invalid indices or sizes
   are not RFC proof claims. Public verifiers reject invalid sizes/indices.
   The subtree helper uses Lean's saturating `Nat` subtraction and truncating
   `take`/`drop` outside the valid half-open range.

## Build, vectors, and axiom audit

From this directory:

```sh
lake build
MERKLE_AUDIT_VERBOSE=1 lake env lean Merkle/Checks.lean
```

`lean-toolchain` pins `leanprover/lean4:v4.34.1`. The project uses Lean
core/Std and Lean's audit metaprogramming support; there are no external
packages and no Mathlib dependency. The default target imports the proofs,
vectors, verifier regression cases, and build-enforced audit.

[`VECTORS.md`](VECTORS.md) inventories 28 symbolic shape equalities, 16
milestone-1 concrete verifier regressions, the M2a shifted-parse inclusion
attack with seven checked facts, and the M2b consistency and binding attacks
with eight checked facts. Symbolic right-hand sides spell
out the exact nested `H` expressions, with prefix bytes independent of the
implementation's helpers. Two prefix assertions use literal `rfl`; the other 26 use proof-producing
`cbv` in a left-hand-side conversion to unfold the well-founded defining
equations, then close the resulting expressions by kernel reflexivity.
Concrete arithmetic is kernel checked. They do not instantiate `H`, assume any hash
identities, or derive shapes from the completeness theorems. The supplemental
regressions use an identity hash solely to make acceptance, rejection, and
orientation errors observable by kernel `decide +kernel`.

[`Merkle/Checks.lean`](Merkle/Checks.lean) selects declarations by their
originating project module, including private helpers and compiler-generated
equations and termination declarations. It checks their transitive axiom
dependencies and fails on any project axiom declaration or dependency outside
`propext`, `Classical.choice`, and `Quot.sound`. Thus a `sorryAx` dependency
also fails the build. It additionally prints axioms for the public completeness
theorems, their stronger internal statements, representative executable
definitions, and every new milestone-2 theorem. All new modules are imported by
`Checks.lean`. Set `MERKLE_AUDIT_VERBOSE=1` to print every declaration's result.
No proof uses `native_decide`.

## Prior art and deferred work

The programme's [ticket #8 assessment](https://github.com/derekblair/formalize-everything/issues/8),
dated 2026-10-26, records a self-published preprint, *Polymorphic Merkle Logs*,
claiming a Lean 4 formalization of RFC 9162's MTH construction, with no public
repository found. Its §4.6 assumes standard inclusion and consistency
soundness. The assessment also identifies ArkLib's generic Merkle commitment
scheme for ZK, but no RFC-shaped CT verifiers with proved soundness, and no
corresponding Mathlib/Batteries development. These are the programme's dated
research findings, not claims proved by this library.

Milestone 2 proves inclusion soundness, tree binding (`mth_binding`), and
consistency soundness with the fixed-width hypothesis above. The identity-hash
regressions establish why that hypothesis is necessary. No computational or
probabilistic cryptographic security property is claimed, and no unconditional
variable-width soundness theorem is supplied.

Exact SHA-256 numeric vectors are deferred until a verified SHA-256
implementation is available. An abstract `H` cannot yield concrete SHA-256
digests; this milestone instead checks the RFC's shapes symbolically. Signature
algorithms, RFC 9162, TLS presentation/wire encodings, proof-length and
complexity bounds, and performance optimization are outside this milestone.
The coordinator appoints the crossed reviewer; the implementation lane does
not arrange its own review.
