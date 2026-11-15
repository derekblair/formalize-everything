# CBOR (RFC 8949), Milestone 1 — Float-Free Wire Grammar, Indefinite Deflation, Bignums, Duplicate-Key Semantics, Ordering Profiles, and Conformance Vectors

A standalone, zero-dependency Lean 4 (`leanprover/lean4:v4.34.1`, no Mathlib)
formalization of the float-free fragment of **Concise Binary Object
Representation (CBOR)**, [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html),
implementing [programme ticket #34](https://github.com/derekblair/formalize-everything/issues/34)
as twice amended by coordinator comments `6460668308` (Amendment 1) and
`6487507282` (Amendment 2). IEEE 754 floating-point values (`0xf9`, `0xfa`,
`0xfb`) belong to **Milestone 2** and are deferred (see
[Deferred Milestone 2 scope](#deferred-milestone-2-scope)).

---

## Prior art and honest novelty accounting (`PARTIAL`)

Per programme ticket #33, ticket #34, and the crossed scoping review, the
prior-art gate for CBOR is **PARTIAL**. Scaffolding overlapping existing
formalizations is **credited to prior art and never claimed as novelty**:

* **EverCBOR** (F* / EverParse, ACM CCS 2025 / arXiv:2505.17335; `Valid.fsti`,
  `Nondet.fst`, and CBORNondet PR #245): formalizes definite-length CBOR
  including tags and simple values, definite-length basic §5.6.1 map-key
  equivalence, and §5.3.1 duplicate-key rejection.
* **`paulbutcher/lean-cbor`** (Lean 4): formalizes a definite canonical CBOR
  core and proves `decode_distinctKeys`.
* **`Proven-Commons/cbor` PR #2** (Lean 4): formalizes a definite canonical
  CBOR core with 37 theorems and checks 30/32 in-slice Appendix A rows
  bidirectionally plus 2 encode-only.
* **`b-erdem/cbor_ada`** (SPARK Level 2): proves head-only round-trip
  properties; does not overlap the recursive or novel Milestone 1 surface.

Accordingly, Milestone 1 partitions its deliverables cleanly between
**scaffolding** (Deliverable 1) and **novel Milestone 1 results**
(Deliverables 2–6):

| Deliverable | Classification | Modules | Summary |
|---|---|---|---|
| **1. Core syntax, parser, deterministic round-trip, basic definite duplicates** | **Scaffolding** (overlaps EverCBOR, `lean-cbor`, `Proven-Commons/cbor`) | [`Head.lean`](Cbor/Rfc8949/Head.lean), [`Item.lean`](Cbor/Rfc8949/Item.lean), [`Parse.lean`](Cbor/Rfc8949/Parse.lean), [`Grammar.lean`](Cbor/Rfc8949/Grammar.lean), [`Deterministic.lean`](Cbor/Rfc8949/Deterministic.lean) | Non-float `Item` & width-preserving `RawItem` ASTs; step-fueled `parseWellFormed` & `decodePrefix` (`bs.length + 1` initial fuel, no overloaded `decode`); exact wire-grammar characterization `parseWellFormed_eq_some_iff`; `encodeDeterministic` / `decodeDeterministic` round trips (with Unicode Table 3-7 UTF-8 check); basic definite-length §5.6.1 `Item.Equiv` and `decodeStrict .basic`. |
| **2. Indefinite lengths & size-hypothesised `deflateIndefinite` + boundary counterexamples** | **Novel** (Amendments 1 & 2 applied) | [`Indefinite.lean`](Cbor/Rfc8949/Indefinite.lean), [`Boundary.lean`](Cbor/Rfc8949/Boundary.lean), [`Boundary/ArrayCountFragment.lean`](Cbor/Rfc8949/Boundary/ArrayCountFragment.lean), [`Boundary/ChunkCountFragment.lean`](Cbor/Rfc8949/Boundary/ChunkCountFragment.lean) | Chunked byte/text strings, indefinite arrays/maps, `break` (`0xff`) completeness; wire-level `deflateIndefinite` proved unconditionally syntax-preserving (`deflateIndefinite_exists_equiv`), idempotent (`deflateIndefinite_idem`), commuting with `encodeDeterministic ∘ Item.normalise` (`deflateIndefinite_normalise`), byte-identical on definite wires (`deflateIndefinite_of_definite`), and definite-producing under recursive `Item.IndefBounded` (`deflateIndefinite_definite`, plus `< 2^64`-byte wire corollary `deflateIndefinite_definite_of_length_lt`); both `< 2^64` boundary counterexamples proved in-kernel. |
| **3. Tag 2/3 bignums (§3.4.3, §4.2.2)** | **Novel** (I3 boundary form) | [`Bignum.lean`](Cbor/Rfc8949/Bignum.lean) | Exact `Int` valuation (`n` for tag 2, `-1 - n` for tag 3) tolerating leading zeros and indefinite byte-string chunks; `encodeInt` preferred boundary (tag 2 iff `z ≥ 2^64`, tag 3 iff `z < -2^64`, minimal big-endian bytes with no leading `0x00` and `length ≥ 9`); uniqueness `eq_encodeInt_of_isPreferredInt`; kernel refutation of the withdrawn `\|z\| ≥ 2^64` form at `-2^64` (`dossier_form_misclassifies_row13`, Appendix A Row 13). |
| **4. Extended duplicate-key & collapse semantics (§5.3.1, §5.6.1)** | **Novel** (narrowed per I2) | [`Equiv.lean`](Cbor/Rfc8949/Equiv.lean), [`Duplicates.lean`](Cbor/Rfc8949/Duplicates.lean) | Maps-as-sets-of-pairs characterization (`Item.equiv_map_iff`, `Item.equiv_mapIndef_iff`); first-wins / collapse-to-one-instance decoder (`firstWins`, `decodeFirstWins`) alongside strict rejection (`decodeStrict`); duplicate equivalence across indefinite chunks/containers (`firstWins_indef_bytes_dup`, `firstWins_indef_array_dup`) and extended tag-2/3 bignum ↔ major 0/1 integer keys (`Item.equivExt_of_intValue?`, `firstWins_extended_int_dup`, `zero_vs_tag2_empty_map_split`). |
| **5. Map-key ordering profiles (§4.2.1, §4.2.3, CTAP2)** | **Novel** (I1 applied) | [`Lex.lean`](Cbor/Rfc8949/Lex.lean), [`Ordering.lean`](Cbor/Rfc8949/Ordering.lean) | Core bytewise-lex (`lexLt`), length-first (`lengthFirstLt`), and FIDO CTAP2 canonical order (`ctap2Lt`) proved strict total orders with stable `sortBy`; exact atomic-key agreement on major types `{0, 1, 2, 3, 7}` (`order_core_eq_ctap2_atomic`, `order_core_eq_ctap2_atomic_indefBounded`, `order_core_eq_ctap2_atomic_wire`, `sortBy_core_eq_ctap2_atomic`); compound-key counterexample `[100]` vs `[-1]` from §4.2.1 (`order_core_ne_ctap2_compound`, `not_order_core_eq_ctap2_all`) and cross-major divergence against §4.2.3 (`order_core_ne_lengthFirst_atomic`). |
| **6. Full float-free RFC 8949 conformance vector suite** | **Novel** (Amendment 1 counts) | [`Vectors.lean`](Cbor/Rfc8949/Vectors.lean), [`Vectors/AppendixA.lean`](Cbor/Rfc8949/Vectors/AppendixA.lean), [`Vectors/AppendixF1.lean`](Cbor/Rfc8949/Vectors/AppendixF1.lean), [`Vectors/Ordering.lean`](Cbor/Rfc8949/Vectors/Ordering.lean) | In-kernel verification of all **58** float-free Appendix A rows in both directions (plus 18 `Int`/bignum semantic round trips), refusal of all **94** Appendix F.1 malformed byte sequences across all 14 RFC categories, and the **8**-key §4.2.1 / §4.2.3 / CTAP2 ordering vector suite. |
| **7. Build-enforced foundation audit & docs** | Verification gate | [`Audit.lean`](Cbor/Rfc8949/Audit.lean) | Imported by root [`Cbor.lean`](Cbor.lean); three-way source-tree/module-inventory check + transitive `collectAxioms` scan across all 2,915 project declarations plus explicit `#print axioms` on every theorem family. |

---

## Key theorems and governing amendments

### 1. Twice-amended `< 2^64` size hypothesis for `deflateIndefinite` (Amendments 1 & 2)

Every CBOR definite head encodes its argument in at most 8 bytes (`< 2^64`).
Consequently, `deflateIndefinite` produces a definite output iff every
indefinite aggregate in the parsed tree fits a definite head (`Item.IndefBounded`
in [`Cbor/Rfc8949/Indefinite.lean`](Cbor/Rfc8949/Indefinite.lean)):

* **Indefinite byte/text strings (`.bytesIndef cs`, `.textIndef cs`):** total
  concatenated chunk payload length `cs.flatten.length < 2 ^ 64` (Amendment 2,
  comment `6487507282` — replacing the withdrawn chunk-count-only hypothesis).
* **Indefinite arrays (`.arrayIndef xs`):** element count `xs.length < 2 ^ 64`
  (Amendment 1, comment `6460668308`), plus `IndefBounded` recursively on `xs`.
* **Indefinite maps (`.mapIndef kvs`):** entry count `kvs.length < 2 ^ 64`,
  plus `IndefBounded` recursively on keys and values.

```lean
theorem deflateIndefinite_exists_equiv {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) :
    ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ Item.Equiv y x

theorem deflateIndefinite_definite {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) (hb : x.IndefBounded) :
    ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ y.Definite ∧ Item.Equiv y x

theorem deflateIndefinite_definite_of_length_lt {bs : List UInt8} {x : Item}
    (hlen : bs.length < 2 ^ 64) (h : parseWellFormed bs = some x) :
    ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ y.Definite ∧ Item.Equiv y x
```

[`Cbor/Rfc8949/Boundary.lean`](Cbor/Rfc8949/Boundary.lean) proves in-kernel
that neither bound can be dropped or weakened (without ever unfolding giant
`List.replicate` payloads in the kernel):

* **`Boundary.array_deflation_counterexample`:** `9f · 00^(2^64) · ff` parses
  to a well-formed indefinite array of `2^64` zeros, and **no** well-formed
  wire parses to a definite item equivalent to it.
* **`Boundary.chunk_count_bound_insufficient`:** two definite byte-string
  chunks of `2^63` zero bytes inside `5f … ff` have chunk count `2 < 2^64`
  (satisfying the withdrawn chunk-count bound), yet their `2^64` payload bytes
  have **no** well-formed definite encoding of an equivalent item.

### 2. Tag 2/3 bignums in I3 boundary form (`Bignum.lean`)

`encodeInt : Int → Item` implements RFC 8949 §3.4.3 / §4.2.2 preferred
integer serialization:

* Major type 0 (`.uint z.toNat`) iff `0 ≤ z ∧ z < 2^64` (`encodeInt_uint_iff`).
* Major type 1 (`.nint (-1 - z).toNat`) iff `-2^64 ≤ z ∧ z < 0`
  (`encodeInt_nint_iff`), including Row 13 `z = -2^64`
  (`encodeInt_neg_two_pow_64`, `dossier_form_misclassifies_row13`).
* Tag 2 (`encodeInt_tag2_iff`, `encodeInt_tag2_content`) iff `2^64 ≤ z`, and
  tag 3 (`encodeInt_tag3_iff`, `encodeInt_tag3_content`) iff `z < -2^64`,
  carrying minimal big-endian bytes with no leading `0x00` and length `≥ 9`.

### 3. Ordering profile agreement & counterexample (`Ordering.lean`)

```lean
theorem order_core_eq_ctap2_atomic {x y : Item}
    (hx : x.WF) (hy : y.WF) (hax : x.isAtomic = true) (hay : y.isAtomic = true) :
    lexLt (encodeDeterministic x) (encodeDeterministic y) =
      ctap2Lt (encodeDeterministic x) (encodeDeterministic y)

theorem order_core_ne_ctap2_compound :
    let w100 := encodeDeterministic compoundKeyArray100
    let wNeg1 := encodeDeterministic compoundKeyArrayNeg1
    w100 = [0x81, 0x18, 0x64] ∧
    wNeg1 = [0x81, 0x20] ∧
    decodeDeterministic w100 = some compoundKeyArray100 ∧
    decodeDeterministic wNeg1 = some compoundKeyArrayNeg1 ∧
    lexLt w100 wNeg1 = true ∧
    ctap2Lt w100 wNeg1 = false ∧
    ctap2Lt wNeg1 w100 = true ∧
    lengthFirstLt w100 wNeg1 = false ∧
    lexLt w100 wNeg1 ≠ ctap2Lt w100 wNeg1
```

---

## Conformance vector counts (verified against official RFC 8949 XML)

All vectors were cross-checked directly against the official RFC Editor XML
(`rfc8949.xml`, SHA-256
`49ee4cb6abd49d775cb7477bd66fc116dc97b970f040714010a01290a3270eb2`):

1. **Appendix A — 58 float-free / 23 float-containing rows (81 total):**
   * **58 float-free rows verified bidirectionally in [`Vectors/AppendixA.lean`](Cbor/Rfc8949/Vectors/AppendixA.lean):**
     rows `1..18` (integers and tag-2/3 bignums), `41..48` (simple values and
     tags `0`, `1(1363896240)`), and `50..81` (tags `23`, `24`, `32`, definite
     byte/text strings including 2/3/4-byte UTF-8, definite arrays/maps, and
     11 indefinite-length strings/arrays/maps `71..81`).
   * **23 float-containing rows deferred to Milestone 2 (Amendment 1):**
     rows `19..40` (22 bare half/single/double float rows) **plus row `49`**,
     `1(1363896240.5)` (`c1 fb 41 d4 52 d9 ec 20 00 00`), which wraps a
     `binary64` float inside tag `1`.
2. **Appendix F.1 — all 94 malformed byte sequences refused in [`Vectors/AppendixF1.lean`](Cbor/Rfc8949/Vectors/AppendixF1.lean):**
   * Exact group counts across the 14 RFC categories:
     `[18, 6, 7, 1, 2, 8, 24, 4, 8, 2, 1, 8, 2, 3]` (sum = `94`, all distinct).
   * Every sequence returns `none` under `parseWellFormed`, `parseRaw`,
     `decodeDeterministic`, `decodeStrict` (`.basic` / `.extended`), and
     `decodeFirstWins` (`.basic` / `.extended`).
   * *Scope note on Group 1's 3 truncated float heads (`f900`, `fa0000`, `fb000000`):*
     Milestone 1's `decodeHead` rejects `0xf9`/`0xfa`/`0xfb` unconditionally
     because floating-point heads are outside the float-free fragment;
     Milestone 2 will accept complete 2/4/8-byte float heads while continuing
     to reject these 3 truncated sequences.
3. **§4.2.1 / §4.2.3 / CTAP2 — 8-key ordering suite in [`Vectors/Ordering.lean`](Cbor/Rfc8949/Vectors/Ordering.lean):**
   * All **8** keys (`10`, `100`, `-1`, `"z"`, `"aa"`, `[100]`, `[-1]`, `false`)
     round-trip through `encodeDeterministic` / `decodeDeterministic` and sort
     into the exact §4.2.1 list under `coreKeyOrder`, the exact §4.2.3 list
     under `lengthFirstKeyOrder`, and `ctap2CanonicalKeys` under `ctap2KeyOrder`.

---

## Build and foundation audit

From `software/cbor-rfc8949/`:

```sh
rm -rf .lake && lake build
```

* Toolchain pinned to `leanprover/lean4:v4.34.1` (`lean-toolchain`), empty
  `lake-manifest.json` (zero external dependencies, no Mathlib, never run
  `lake exe cache get`).
* [`Cbor/Rfc8949/Audit.lean`](Cbor/Rfc8949/Audit.lean) is imported by the
  default target [`Cbor.lean`](Cbor.lean), so every `lake build` verifies
  module coverage across all 20 `.lean` source files and checks transitive
  foundations across all 2,915 project declarations (`⊆ {propext, Classical.choice, Quot.sound}`).
  Run `CBOR_AUDIT_VERBOSE=1 lake env lean Cbor/Rfc8949/Audit.lean` to log each
  declaration individually.

---

## Deferred Milestone 2 scope

Milestone 2 extends this package to IEEE 754 floating-point CBOR values:

* Binary16 (`0xf9`), binary32 (`0xfa`), and binary64 (`0xfb`) head/payload
  decoding and encoding (RFC 8949 §3.3, Appendix D half-precision layout);
* Preferred and core deterministic shortest-float width selection
  (`binary64 → binary32 → binary16` value-preserving narrowing, §4.1 / §4.2.1);
* Deterministic NaN canonicalization to quiet half-precision `0xf97e00`
  (§4.2.1) and signed-zero handling (`-0.0` = `0xf98000` vs `0.0` = `0xf90000`);
* Float data-model equivalence (§2, §5.6.1) and acceptance of complete float
  heads alongside rejection of Appendix F.1's 3 truncated float heads;
* In-kernel bidirectional verification of the remaining **23** Appendix A
  rows (`19..40` and row `49`, `1(1363896240.5)`).
