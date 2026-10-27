# UTF-8 (RFC 3629 / Unicode Table 3-7), milestone 1

A standalone Lean 4.34.1 project specifying well-formed UTF-8 byte
sequences directly from the document — Unicode Standard Table 3-7
("Well-Formed UTF-8 Byte Sequences"), equivalently RFC 3629 §3 —
implementing [programme ticket #18](https://github.com/derekblair/formalize-everything/issues/18).
It defines an independent inductive specification, an executable
decoder written to that specification, the characterization theorem
that the two agree, the exact agreement with Lean core's validity
predicate and runtime validator, and kernel-checked examples.
Milestone 1 remains in progress until the coordinator-appointed
crossed review passes and the PR is merged.

Nothing in the specification is defined via any decoder or via Lean
core's encoder: `Utf8.Seq` is the table, row by row, and `Utf8.Valid`
is a finite concatenation of well-formed sequences. The restricted
second-byte ranges in the `E0`, `ED`, `F0`, and `F4` rows are stated
exactly as the table states them; they are what exclude overlong
(non-shortest) forms, the UTF-16 surrogate code points
U+D800–U+DFFF, and code points above U+10FFFF.

## Source coverage

| Table 3-7 row (first byte) | `Seq` constructor | Decoder branch |
|---|---|---|
| `00–7F` | `Seq.one` | one byte, payload is the byte |
| `C2–DF`, then `80–BF` | `Seq.two` | `payload2` |
| `E0`, then `A0–BF`, then `80–BF` | `Seq.threeE0` | `payload3`, `secondOk3` disjunct 1 |
| `E1–EC`, then two `80–BF` | `Seq.three` | `payload3`, `secondOk3` disjunct 2 |
| `ED`, then `80–9F`, then `80–BF` | `Seq.threeED` | `payload3`, `secondOk3` disjunct 3 |
| `EE–EF`, then two `80–BF` | `Seq.threeEF` | `payload3`, `secondOk3` disjunct 4 |
| `F0`, then `90–BF`, then two `80–BF` | `Seq.fourF0` | `payload4`, `secondOk4` disjunct 1 |
| `F1–F3`, then three `80–BF` | `Seq.four` | `payload4`, `secondOk4` disjunct 2 |
| `F4`, then `80–8F`, then two `80–BF` | `Seq.fourF4` | `payload4`, `secondOk4` disjunct 3 |

Bytes `80–C1` and `F5–FF` begin no row: `80–BF` are continuation
bytes, `C0–C1` could only start overlong two-byte forms, and
`F5–FF` could only start forms for code points above U+10FFFF.
`Utf8.Examples.decodeSeq?_lead_invalid` and its corollaries prove
the decoder rejects every such lead unconditionally.

The encoder `encodeCodepoint n` is the canonical shortest-form
encoding, written with the division/modulo formulas that produce
exactly the table's bit patterns; `encodeAll` encodes a list of
characters with it. `encodeCodepoint` is only ever used at valid
Unicode scalar values; its value at other naturals carries no claim.

## The characterization

These are the main statements verbatim, in namespace `Utf8`:

```lean
theorem valid_iff_decode {l : List UInt8} :
    Valid l ↔ ∃ cs, decode l = some cs ∧ encodeAll cs = l

theorem decode_encodeAll (cs : List Char) :
    decode (encodeAll cs) = some cs

theorem decode_eq_none_iff {l : List UInt8} :
    decode l = none ↔ ¬ Valid l
```

The proof goes through fuel-general statements, so no fuel
irrelevance lemma is needed: `decodeFuel_of_valid` shows every
well-formed list decodes under *any* sufficient fuel with
re-encoding exact, and `valid_of_decodeFuel` shows every list
accepted under *any* fuel is well-formed with re-encoding exact.
`decode` is `decodeFuel` at fuel `l.length`. The one-step engine
is `seq_of_decodeSeq?` / `decodeSeq?_of_seq`: a successful
single-sequence step consumes exactly one `Seq`, and the decoded
character re-encodes to exactly the consumed bytes
(`encode_payload2/3/4` do the arithmetic).

`decodeFuel` is fuelled only to make the iteration structurally
acceptable to Lean; every successful step consumes at least one
byte, so `l.length` units always suffice. The fuel is not part of
the specification, and the characterization quantifies over it
rather than hiding it.

## Agreement with Lean core

Lean core does not define validity via Table 3-7. Core's predicate
is *defined* through its encoder:

```lean
inductive ByteArray.IsValidUTF8 (b : ByteArray) : Prop
  | intro (m : List Char) (hm : Eq b (List.utf8Encode m))
```

and `ByteArray.validateUTF8` is core's executable validator, which
core itself proves equivalent to that predicate
(`ByteArray.validateUTF8_eq_true_iff`). The exact agreement
statements core's API supports are proved in `Utf8/Core.lean`:

```lean
theorem encodeCodepoint_eq_core (c : Char) :
    encodeCodepoint c.val.toNat = String.utf8EncodeChar c

theorem valid_iff_core {l : List UInt8} :
    Valid l ↔ ByteArray.IsValidUTF8 l.toByteArray

theorem valid_iff_validate {l : List UInt8} :
    Valid l ↔ l.toByteArray.validateUTF8 = true

theorem valid_iff_exists_string {l : List UInt8} :
    Valid l ↔ ∃ s : String, s.toByteArray = l.toByteArray
```

There is **no gap**: `encodeCodepoint_eq_core` holds by `rfl`
(core's `String.utf8EncodeChar` uses literally the same
division/modulo formulas), so `encodeAll` is exactly the list
underlying core's `List.utf8Encode`, and the Table 3-7 predicate
characterizes the same byte arrays as core's predicate and its
runtime validator. The honest content note is about what core's
definition *is*: because core defines validity as "is the encoding
of some character list", `valid_iff_core` says the document's table
and the range of core's encoder coincide — it is not a comparison
against a second, independent core specification, since core has
none (that absence is part of ticket #18's prior-art finding).

## Examples

`Utf8/Examples.lean` contains kernel-checked theorems. The
concrete valid and invalid examples are proved by `decide`
through the proved characterization (`valid_iff_decode`); the
file's general exclusion theorems are ordinary proofs over
arbitrary byte tails. No `native_decide` occurs in code:

- **Valid**: the empty sequence; U+0024 `$`; U+00A2 `¢`; U+00E9;
  U+0800 (the `E0` floor); U+20AC `€`; U+D7FF and U+E000 (the two
  code points bracketing the surrogate range); U+10000 (the `F0`
  floor); U+10348 (the Unicode standard's four-byte example); U+1F600;
  U+10FFFF (the `F4` ceiling); and a mixed-width concatenation —
  each with its exact decoded character list and re-encoding.
- **Invalid** (each with `decode … = none` and `¬ Valid …`):
  overlong forms `C0 80`, `C1 BF`, `E0 80 80`, `E0 9F BF`,
  `F0 80 80 80`, `F0 8F BF BF`; surrogates `ED A0 80` (U+D800) and
  `ED BF BF` (U+DFFF); above the maximum `F4 90 80 80`; leads
  `F5 …` and `FF`; a lone continuation byte `80`; the bad
  continuation `C2 41`; truncations `C2`, `E2 82`, `F0 90 8D`;
  and a valid prefix followed by an invalid tail.
- **General exclusions**, for all choices of the remaining bytes:
  leads `C0`/`C1` never decode (`not_valid_overlong_two`); every
  `ED` sequence with second byte in `A0–BF` is invalid
  (`not_valid_surrogate`); every `E0` sequence with a continuation
  second byte below `A0` is invalid (`not_valid_overlong_e0`);
  every `F0` sequence with a continuation second byte below `90`
  is invalid (`not_valid_overlong_f0`); every `F4` sequence with
  a continuation second byte above `8F` is invalid
  (`not_valid_above_max`).

## Build and axiom audit

From this directory:

```sh
lake build
UTF8_AUDIT_VERBOSE=1 lake env lean Utf8/Audit.lean
```

`lean-toolchain` pins `leanprover/lean4:v4.34.1`. The project uses
only Lean core; there are no external packages and no Mathlib
dependency. The default target builds every module of the library,
including the audit entrypoint.

[`Utf8/Audit.lean`](Utf8/Audit.lean) imports the umbrella module
`Utf8`, so it runs over the complete library import graph. It
selects declarations by their originating project module,
including private helpers and compiler-generated equations and
termination declarations, checks their transitive axiom
dependencies, and fails the build on any project axiom
declaration or any dependency outside `propext`,
`Classical.choice`, and `Quot.sound` — so a `sorryAx` dependency
also fails the build. A module-inventory guard compares the
project modules actually present in the environment (derived from
`env.header.moduleNames`) against an explicit expected inventory
in both directions: a project module in the import graph that is
missing from the inventory fails the build, and so does an
expected module absent from the import graph, so no module in the
library import graph can escape the audit. (The inventory
accounts explicitly for the two import-only modules: the umbrella
`Utf8` and the audit entrypoint `Utf8.Audit` itself.) It
additionally prints axioms for the principal theorems and
definitions. No proof uses `sorry`, `admit`, or `native_decide`.

## Prior art

Ticket #18's live-Google prior-art verdict (2026-10-26) is
**PARTIAL**. o-santi/rocq_utf8 (Rocq) transcribes the same
Table 3-7 ranges but its decoder-side theorems are `Admitted`, so
the decoding characterization is not proved there.
iainmcgin/smooth-utf8 (Verus) proves a boolean validator equivalent
to its spec, but Verus is SMT-trusted rather than kernel-checked
and proves no decoder characterization. Lean core proves decoder
internals against its own encoder-defined validity, with no
independent Table 3-7 specification and no agreement theorem
against the document. This milestone closes that gap in Lean:
an independent document-first spec, a proved decoder
characterization, and a proved exact agreement with core.

## Deferred work

Nothing in ticket #18's scope is deferred: specification,
characterization, core agreement, and RFC/Unicode examples are all
in this milestone. Possible future work outside the ticket: a
streaming/incremental decoder interface, UTF-8 as used by specific
wire formats, and complexity bounds. The coordinator appoints the
crossed reviewer; the implementation lane does not arrange its own
review.
