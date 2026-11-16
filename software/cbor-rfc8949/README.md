# CBOR (RFC 8949), Milestones 1 & 2 — Full Wire Grammar, IEEE 754 Floats, Indefinite Deflation, Bignums, Duplicate-Key Semantics, Ordering Profiles, and Conformance Vectors

A standalone, zero-dependency Lean 4 (`leanprover/lean4:v4.34.1`, no Mathlib)
formalization of **Concise Binary Object Representation (CBOR)**,
[RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html), implementing:

* **Milestone 1** ([programme ticket #34](https://github.com/derekblair/formalize-everything/issues/34),
  merged as PR #60 / `e629a63`, twice amended by coordinator comments
  `6460668308` and `6487507282`) — the complete float-free CBOR grammar,
  indefinite-length deflation and `< 2^64` boundary counterexamples, tag 2/3
  bignums, duplicate-key semantics, §4.2.1 / §4.2.3 / CTAP2 ordering profiles,
  and 58 float-free Appendix A / 94 Appendix F.1 / 8 ordering vectors; and
* **Milestone 2** ([programme ticket #126](https://github.com/derekblair/formalize-everything/issues/126)) —
  the complete IEEE 754 floating-point slice (`0xf9` `binary16`, `0xfa`
  `binary32`, `0xfb` `binary64`, §3.3 & Appendix D), value-preserving
  `binary64 → binary32 → binary16` shortest-float narrowing (§4.1 / §4.2.1)
  and deterministic `0xf97e00` NaN canonicalization (§4.2.1 / §4.2.2),
  proved boundary cases, §2 / §5.6.1 float data-model equivalence, full-grammar
  acceptance of complete float heads alongside refusal of all 94 Appendix F.1
  malformed sequences, and all **23** float Appendix A rows (`19..40` and `49`),
  completing **81/81** Appendix A vectors in-kernel.

---

## Prior art and honest novelty accounting (`PARTIAL`)

Per programme tickets #33, #34, and #126, the package-level prior-art gate for
CBOR is **PARTIAL**. Scaffolding overlapping existing formalizations is
**credited to prior art and never claimed as novelty**:

* **EverCBOR** (F* / EverParse, ACM CCS 2025 / arXiv:2505.17335; `Valid.fsti`,
  `Nondet.fst`, and CBORNondet PR #245): formalizes definite-length float-free
  CBOR including tags and simple values, definite-length basic §5.6.1 map-key
  equivalence, and §5.3.1 duplicate-key rejection; scopes out IEEE 754 floats.
* **`paulbutcher/lean-cbor`** (Lean 4): formalizes a definite canonical
  float-free CBOR core and proves `decode_distinctKeys`.
* **`Proven-Commons/cbor` PR #2** (Lean 4): formalizes a definite canonical
  float-free CBOR core with 37 theorems and checks 30/32 in-slice Appendix A
  rows bidirectionally plus 2 encode-only; scopes out IEEE 754 floats.
* **`b-erdem/cbor_ada`** (SPARK Level 2): proves head-only round-trip
  properties; does not overlap the recursive Milestone 1 or Milestone 2 surface.

Accordingly, the package partitions its deliverables cleanly between
**scaffolding** (Deliverable 1) and **novel Milestone 1 & Milestone 2 results**
(Deliverables 2–6 and 8):

| Deliverable | Classification | Modules | Summary |
|---|---|---|---|
| **1. Core syntax, parser, deterministic round-trip, basic definite duplicates** | **Scaffolding** (overlaps EverCBOR, `lean-cbor`, `Proven-Commons/cbor`) | [`Head.lean`](Cbor/Rfc8949/Head.lean), [`Item.lean`](Cbor/Rfc8949/Item.lean), [`Parse.lean`](Cbor/Rfc8949/Parse.lean), [`Grammar.lean`](Cbor/Rfc8949/Grammar.lean), [`Deterministic.lean`](Cbor/Rfc8949/Deterministic.lean) | Non-float `Item` & width-preserving `RawItem` ASTs; step-fueled `parseWellFormed` & `decodePrefix` (`bs.length + 1` initial fuel, no overloaded `decode`); exact wire-grammar characterization `parseWellFormed_eq_some_iff`; `encodeDeterministic` / `decodeDeterministic` round trips (with Unicode Table 3-7 UTF-8 check); basic definite-length §5.6.1 `Item.Equiv` and `decodeStrict .basic`. |
| **2. Indefinite lengths & size-hypothesised `deflateIndefinite` + boundary counterexamples** | **Novel** (Amendments 1 & 2 applied) | [`Indefinite.lean`](Cbor/Rfc8949/Indefinite.lean), [`Boundary.lean`](Cbor/Rfc8949/Boundary.lean), [`Boundary/ArrayCountFragment.lean`](Cbor/Rfc8949/Boundary/ArrayCountFragment.lean), [`Boundary/ChunkCountFragment.lean`](Cbor/Rfc8949/Boundary/ChunkCountFragment.lean) | Chunked byte/text strings, indefinite arrays/maps, `break` (`0xff`) completeness; wire-level `deflateIndefinite` proved unconditionally syntax-preserving under both `Item.Equiv` and `Item.EquivExt` (`deflateIndefinite_exists_equiv`), idempotent (`deflateIndefinite_idem`), commuting with `encodeDeterministic ∘ Item.normalise` (`deflateIndefinite_normalise`), byte-identical on definite wires (`deflateIndefinite_of_definite`), and `RawItem`-definite-producing (`r.Definite ∧ r.toItem = x.toDefinite`) under recursive `Item.IndefBounded` (`deflateIndefinite_definite`, plus `< 2^64`-byte wire corollary `deflateIndefinite_definite_of_length_lt`); both `< 2^64` boundary counterexamples proved in-kernel. |
| **3. Tag 2/3 bignums (§3.4.3, §4.2.2)** | **Novel** (I3 boundary form) | [`Bignum.lean`](Cbor/Rfc8949/Bignum.lean) | Exact `Int` valuation (`n` for tag 2, `-1 - n` for tag 3) tolerating leading zeros and indefinite byte-string chunks; `encodeInt` preferred boundary (tag 2 iff `z ≥ 2^64`, tag 3 iff `z < -2^64`, minimal big-endian bytes with no leading `0x00` and `length ≥ 9`); uniqueness `eq_encodeInt_of_isPreferredInt`; kernel refutation of the withdrawn `\|z\| ≥ 2^64` form at `-2^64` (`dossier_form_misclassifies_row13`, Appendix A Row 13). |
| **4. Extended duplicate-key & collapse semantics (§5.3.1, §5.6.1)** | **Novel** (narrowed per I2) | [`Equiv.lean`](Cbor/Rfc8949/Equiv.lean), [`Duplicates.lean`](Cbor/Rfc8949/Duplicates.lean) | Maps-as-sets-of-pairs characterization (`Item.equiv_map_iff`, `Item.equiv_mapIndef_iff`) under explicit canonical-entry well-formedness hypotheses `WFPairs (canonWithPairs false kvs₁)` and `WFPairs (canonWithPairs false kvs₂)` (automatic when canonicalized aggregate sizes are `< 2^64`); first-wins / collapse-to-one-instance decoder (`firstWins`, `decodeFirstWins`) alongside strict rejection (`decodeStrict`); duplicate equivalence across indefinite chunks/containers (`firstWins_indef_bytes_dup`, `firstWins_indef_array_dup`) and extended tag-2/3 bignum ↔ major 0/1 integer keys (`Item.equivExt_of_intValue?`, `firstWins_extended_int_dup`, `zero_vs_tag2_empty_map_split`). |
| **5. Map-key ordering profiles (§4.2.1, §4.2.3, CTAP2)** | **Novel** (I1 applied) | [`Lex.lean`](Cbor/Rfc8949/Lex.lean), [`Ordering.lean`](Cbor/Rfc8949/Ordering.lean) | Core bytewise-lex (`lexLt`), length-first (`lengthFirstLt`), and FIDO CTAP2 canonical order (`ctap2Lt`) proved strict total orders with stable `sortBy`; exact atomic-key agreement on major types `{0, 1, 2, 3, 7}` (`order_core_eq_ctap2_atomic`, `order_core_eq_ctap2_atomic_indefBounded`, `order_core_eq_ctap2_atomic_wire`, `sortBy_core_eq_ctap2_atomic`); compound-key counterexample `[100]` vs `[-1]` from §4.2.1 (`order_core_ne_ctap2_compound`, `not_order_core_eq_ctap2_all`) and cross-major divergence against §4.2.3 (`order_core_ne_lengthFirst_atomic`). |
| **6. Full float-free RFC 8949 conformance vector suite** | **Novel** (Amendment 1 counts) | [`Vectors.lean`](Cbor/Rfc8949/Vectors.lean), [`Vectors/AppendixA.lean`](Cbor/Rfc8949/Vectors/AppendixA.lean), [`Vectors/AppendixF1.lean`](Cbor/Rfc8949/Vectors/AppendixF1.lean), [`Vectors/Ordering.lean`](Cbor/Rfc8949/Vectors/Ordering.lean) | In-kernel verification of all **58** float-free Appendix A rows in both directions (plus 18 `Int`/bignum semantic round trips), refusal of all **94** Appendix F.1 malformed byte sequences across all 14 RFC categories, and the **8**-key §4.2.1 / §4.2.3 / CTAP2 ordering vector suite. |
| **7. Build-enforced foundation audit & docs** | Verification gate | [`Audit.lean`](Cbor/Rfc8949/Audit.lean) | Imported by root [`Cbor.lean`](Cbor.lean); three-way source-tree/module-inventory check + transitive `collectAxioms` scan across all **5,090** project declarations (`23` audited modules, `25` source modules total) plus explicit `#print axioms` on every M1 and M2 theorem family. |
| **8. Milestone 2: IEEE 754 float slice & 23 Appendix A float vectors (FE #126)** | **Novel** | [`Float.lean`](Cbor/Rfc8949/Float.lean), [`Float/IEEE754.lean`](Cbor/Rfc8949/Float/IEEE754.lean), [`Float/Narrowing.lean`](Cbor/Rfc8949/Float/Narrowing.lean), [`Float/DataModel.lean`](Cbor/Rfc8949/Float/DataModel.lean), [`Float/Vectors.lean`](Cbor/Rfc8949/Float/Vectors.lean) | Explicit bit-level `Float16`/`Float32`/`Float64`/`CborFloat` codecs (`0xf9`/`0xfa`/`0xfb`, §3.3 & Appendix D Figure 3); stepwise `binary64 → binary32 → binary16` value-preserving narrowing (§4.1 `preferredFloat`, `encodeFloatPreferred_shortest`) and deterministic `0xf97e00` NaN canonicalization (§4.2.1/§4.2.2 `canonicalFloatDet`); signed-zero, `±Infinity`, NaN-payload, subnormal, and IEEE 754 RNE lossy-narrowing boundary theorems; §2/§5.6.1 `FloatEquiv` & `FullItem.Equiv`; full-grammar `parseFullRaw_eq_some_iff` + 94-sequence Appendix F.1 refusal; and all **23** float Appendix A rows (`19..40` and `49`) + complete **81**-row partition (`58 + 23 = 81`). |

---

## Key theorems and governing amendments

### 1. Twice-amended `< 2^64` size hypothesis for `deflateIndefinite` (Amendments 1 & 2, N1 exact signatures)

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

The compiled theorems in [`Indefinite.lean`](Cbor/Rfc8949/Indefinite.lean) establish
both `Item.Equiv` and `Item.EquivExt` unconditionally and produce a `RawItem`-level
`r.Definite` witness with `r.toItem = x.toDefinite` under `IndefBounded`:

```lean
theorem deflateIndefinite_exists_equiv {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) :
    ∃ y, parseWellFormed (deflateIndefinite bs) = some y ∧ Item.Equiv x y ∧ Item.EquivExt x y

theorem deflateIndefinite_definite {bs : List UInt8} {x : Item}
    (h : parseWellFormed bs = some x) (hb : x.IndefBounded) :
    ∃ r, parseRaw (deflateIndefinite bs) = some r ∧ r.Definite ∧ r.toItem = x.toDefinite ∧
      Item.Equiv x r.toItem

theorem deflateIndefinite_definite_of_length_lt {bs : List UInt8} {x : Item}
    (hlen : bs.length < 2 ^ 64) (h : parseWellFormed bs = some x) :
    ∃ r, parseRaw (deflateIndefinite bs) = some r ∧ r.Definite ∧ r.toItem = x.toDefinite ∧
      Item.Equiv x r.toItem
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

### 2. Maps-as-sets-of-pairs equivalence (`Equiv.lean`, N2 explicit `WFPairs` hypothesis)

Because [`Equiv.lean`](Cbor/Rfc8949/Equiv.lean) canonicalizes map entries by
sorting canonicalized pairs with `entryLt` (bytewise `lexLt` on preferred
encodings), `Item.equiv_map_iff` and `Item.equiv_mapIndef_iff` carry the
explicit canonical-entry well-formedness hypotheses
`WFPairs (canonWithPairs false kvs₁)` and `WFPairs (canonWithPairs false kvs₂)`
(which hold automatically whenever canonicalized aggregate sizes are `< 2^64`,
e.g. for every `< 2^64`-byte wire):

```lean
theorem Item.equiv_map_iff {kvs₁ kvs₂ : List (Item × Item)}
    (h₁ : WFPairs (canonWithPairs false kvs₁))
    (h₂ : WFPairs (canonWithPairs false kvs₂)) :
    Equiv (.map kvs₁) (.map kvs₂) ↔
      ∀ k v, (∃ kv ∈ kvs₁, Equiv kv.1 k ∧ Equiv kv.2 v) ↔
             (∃ kv ∈ kvs₂, Equiv kv.1 k ∧ Equiv kv.2 v)

theorem Item.equiv_mapIndef_iff {kvs₁ kvs₂ : List (Item × Item)}
    (h₁ : WFPairs (canonWithPairs false kvs₁))
    (h₂ : WFPairs (canonWithPairs false kvs₂)) :
    Equiv (.mapIndef kvs₁) (.mapIndef kvs₂) ↔
      ∀ k v, (∃ kv ∈ kvs₁, Equiv kv.1 k ∧ Equiv kv.2 v) ↔
             (∃ kv ∈ kvs₂, Equiv kv.1 k ∧ Equiv kv.2 v)
```

### 3. Tag 2/3 bignums in I3 boundary form (`Bignum.lean`)

`encodeInt : Int → Item` implements RFC 8949 §3.4.3 / §4.2.2 preferred
integer serialization:

* Major type 0 (`.uint z.toNat`) iff `0 ≤ z ∧ z < 2^64` (`encodeInt_uint_iff`).
* Major type 1 (`.nint (-1 - z).toNat`) iff `-2^64 ≤ z ∧ z < 0`
  (`encodeInt_nint_iff`), including Row 13 `z = -2^64`
  (`encodeInt_neg_two_pow_64`, `dossier_form_misclassifies_row13`).
* Tag 2 (`encodeInt_tag2_iff`, `encodeInt_tag2_content`) iff `2^64 ≤ z`, and
  tag 3 (`encodeInt_tag3_iff`, `encodeInt_tag3_content`) iff `z < -2^64`,
  carrying minimal big-endian bytes with no leading `0x00` and length `≥ 9`.

### 4. Ordering profile agreement & counterexample (`Ordering.lean`)

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

### 5. Milestone 2: IEEE 754 floating-point slice (`Float/`, FE #126)

Lean 4 core exposes `Float` as an opaque runtime type with no bit-level proof
API. Milestone 2 therefore formalizes IEEE 754 `binary16` (`Float16`),
`binary32` (`Float32`), and `binary64` (`Float64`) directly from bounded
`(sign, exp, mant)` bit fields in [`Float/IEEE754.lean`](Cbor/Rfc8949/Float/IEEE754.lean)
with **zero** reliance on Lean's opaque `Float`:

1. **Bit-level wire codecs & Appendix D correspondence (`Float/IEEE754.lean`, §3.3 & Appendix D):**
   * Major type 7, additional information `25` (`0xf9`, 3 wire bytes), `26`
     (`0xfa`, 5 wire bytes), and `27` (`0xfb`, 9 wire bytes), with bit-packing
     bijections (`ofBits_toBits`, `toBits_ofBits_of_lt`), exact round-trip and
     iff characterizations (`decodeFloat16_eq_some_iff`, `decodeFloat32_eq_some_iff`,
     `decodeFloat64_eq_some_iff`, `decodeFloat_eq_some_iff`), prefix uniqueness
     (`encodeFloat_prefix_unique`), and Appendix D Figure 3 bit-mask equivalence
     (`decodeFloat16_eq_appendixD`).
   * Exact symbolic valuation `IEEEValue` (`zero sign`, `finiteNz sign scaledMag`
     scaled by `2^1074`, `inf sign`, `nan sign sig52`) proved injective at all
     three widths (`Float64.toIEEEValue_injective`, `Float32.toIEEEValue_injective`,
     `Float16.toIEEEValue_injective`).
2. **Preferred vs. core deterministic shortest-float rules (`Float/Narrowing.lean`, §4.1 vs. §4.2.1/§4.2.2):**
   * Exact stepwise narrowing `narrow64To32?` and `narrow32To16?` (`narrow64To16?`)
     proved sound and complete (`narrow64To32?_eq_some_iff`,
     `narrow32To16?_eq_some_iff`, `narrow64To16?_eq_some_iff`).
   * **Accepted vs. rejected float encodings:**
     - `parseFullRaw` / `parseFullWellFormed` (§3.3 variation-tolerant grammar)
       accepts every complete 3-, 5-, or 9-byte float encoding (including
       Appendix A's 6 non-preferred rows `35..40`) and rejects truncated heads.
     - `decodeFloatPreferred` (§4.1) accepts `bs` iff `bs = encodeFloat f` and
       no narrower width represents `f.toIEEEValue` (`decodeFloatPreferred_eq_some_iff`,
       `encodeFloatPreferred_shortest`), preserving `-0.0` (`0xf98000`) vs.
       `0.0` (`0xf90000`) and keeping wider NaNs only when non-zero low payload
       bits prevent exact narrowing (e.g. `0xfb7ff8000000000001`).
     - `decodeFloatDeterministic` / `decodeFullDeterministic` (§4.2.1 & §4.2.2)
       additionally canonicalizes **every** NaN to quiet half-precision
       `0xf97e00` (`canonicalFloatDet`, `encodeFloatDeterministic_nan`) and
       rejects both non-shortest widths (`Rows 35..40`) and non-canonical NaNs
       (`0xf97c01`, `0xf9fe00`, `0xfb7ff8000000000001`).
3. **Proved boundary cases (`Float/Narrowing.lean`, §2.4):**
   * **`signed_zero_boundary`:** `0.0` (`0xf90000`) vs. `-0.0` (`0xf98000`)
     distinct in bits, `IEEEValue`, preferred, and deterministic encodings;
     5-byte and 9-byte `-0.0` rejected by `decodeFloatPreferred` and narrowed to `0xf98000`.
   * **`infinity_boundary`:** `binary32`/`binary64` `±Infinity` (Rows 35, 37, 38, 40)
     narrow to `0xf97c00` / `0xf9fc00` (Rows 32, 34).
   * **`nan_payload_and_canonical_boundary`:** zero-low-bit NaNs (Rows 36, 39)
     narrow to `0xf97e00` under both §4.1 and §4.2.1; low-payload NaN
     `0xfb7ff8000000000001`, signaling NaN `0xf97c01`, and negative quiet NaN
     `0xf9fe00` separate §4.1 `preferredFloat` from §4.2.1 `canonicalFloatDet`.
   * **`subnormal_boundary`:** `Float16.minPosSubnormal` (`2^-24`, `0xf90001`,
     Row 28) widens to **normal** `Float32` (`0xfa33800000`) and **normal**
     `Float64` (`0xfb3e70000000000000`) and narrows back to subnormal `0xf90001`;
     `Float32.minPosSubnormal` (`2^-149`) and `Float64.minPosSubnormal` (`2^-1074`)
     cannot narrow further.
   * **`widen32To64_round64To32_eq_iff` & `lossy_narrowing_boundary`:** IEEE 754
     round-to-nearest-even `round64To32` round-trips via `widen32To64` iff
     `narrow64To32? d ≠ none`, with kernel witnesses of all three exact loss
     mechanisms (precision narrowing on `1.1` Row 22, `1363896240.5` Row 49, and
     `1.0 + 2^-11`; exponent overflow to `+Infinity` on `100000.0` Row 25 and
     `1.0e+300` Row 27; exponent underflow to `+0.0` on `2^-25` and `2^-1074`).
4. **Float data-model equivalence & full-grammar F.1 refusal (`Float/DataModel.lean`, §2 & §5.6.1):**
   * `FloatEquiv` and `FullItem.Equiv` erase float width, equate `-0.0` and
     `+0.0` as generic data-model values / map keys (`floatEquiv_posZero_negZero`,
     `{0.0: 1, -0.0: 1} ≈ {0.0: 1}`), equate NaNs iff their 52-bit
     right-zero-extended significands match (`floatEquiv_nan_iff`), keep floats
     distinct from integers/bignums/simple values (`1.0 ≢ 1`,
     `FullItem.not_equiv_float_uint`), and conservatively extend M1
     (`FullItem.equiv_ofItem_iff`).
   * `fullHead_complete_vs_truncated` and `appendixF1_all_refused_full` accept
     complete 2/4/8-byte float heads while refusing all **94** Appendix F.1
     malformed sequences (including Group 1's 3 truncated float heads
     `f900`, `fa0000`, `fb000000`).

---

## Conformance vector counts (verified against official RFC 8949 XML)

All vectors were cross-checked directly against the official RFC Editor XML
(`rfc8949.xml`, SHA-256
`49ee4cb6abd49d775cb7477bd66fc116dc97b970f040714010a01290a3270eb2`):

1. **Appendix A — all 81 rows verified bidirectionally in-kernel (`58` float-free + `23` float = `81`):**
   * **58 float-free rows verified bidirectionally in [`Vectors/AppendixA.lean`](Cbor/Rfc8949/Vectors/AppendixA.lean):**
     rows `1..18` (integers and tag-2/3 bignums), `41..48` (simple values and
     tags `0`, `1(1363896240)`), and `50..81` (tags `23`, `24`, `32`, definite
     byte/text strings including 2/3/4-byte UTF-8, definite arrays/maps, and
     11 indefinite-length strings/arrays/maps `71..81`).
   * **23 float-containing rows verified bidirectionally in [`Float/Vectors.lean`](Cbor/Rfc8949/Float/Vectors.lean):**
     rows `19..40` (16 preferred bare half/single/double float rows `19..34` and
     6 well-formed non-preferred `binary32`/`binary64` `Infinity`/`NaN`/`-Infinity`
     rows `35..40`) **plus row `49`**, `1(1363896240.5)`
     (`c1 fb 41 d4 52 d9 ec 20 00 00`), proved in `appendixAFloat_all_bidirectional`
     and joined with the 58 float-free rows in `appendixA_complete_81_rows`.
2. **Appendix F.1 — all 94 malformed byte sequences refused in [`Vectors/AppendixF1.lean`](Cbor/Rfc8949/Vectors/AppendixF1.lean) and [`Float/DataModel.lean`](Cbor/Rfc8949/Float/DataModel.lean):**
   * Exact group counts across the 14 RFC categories:
     `[18, 6, 7, 1, 2, 8, 24, 4, 8, 2, 1, 8, 2, 3]` (sum = `94`, all distinct).
   * Refused both by Milestone 1's float-free decoders (`appendixF1_all_refused`)
     and by Milestone 2's full float-enabled decoders `parseFullRaw`,
     `parseFullWellFormed`, and `decodeFullDeterministic`
     (`appendixF1_all_refused_full`), while complete 2/4/8-byte float heads are
     accepted.
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
  module coverage across all **25** `.lean` source files (`23` audited modules)
  and checks transitive foundations across all **5,090** project declarations
  (`⊆ {propext, Classical.choice, Quot.sound}`, zero `sorryAx`).
  Run `CBOR_AUDIT_VERBOSE=1 lake env lean Cbor/Rfc8949/Audit.lean` to log each
  declaration individually.
