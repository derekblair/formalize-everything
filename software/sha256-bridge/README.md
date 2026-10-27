# SHA-256 pure Lean bridge

This package proves that `etheorem/LeanSha256`'s `hash` and `combine` agree
with `pure-algebra/lean4-hash`'s independent bit-string FIPS 180-4
specification. It targets ticket [#26](https://github.com/derekblair/formalize-everything/issues/26).

**This pure↔pure bridge discharges NONE of SizzLean's three C/OpenSSL FFI
axioms:** `sha256Hash_eq_spec`, `sha256Combine_eq_spec`, and
`sha256BatchCombine_eq_spec`. The C shims, OpenSSL, compiler execution,
and cryptographic security properties are outside these theorems.

## Statements and domain

All theorem names below are in `Sha256Bridge` and refer to the original,
unmodified upstream definitions.

| Theorem | Statement |
| --- | --- |
| `spec_pad_length_no_wraparound` | Under `data.size < 2^61`, the spec's length suffix denotes exactly `8 * data.size`. |
| `hash_bits_eq_fips_spec` | Under that explicit bound, hash output bits equal `Spec.sha256` of input bits. |
| `hash_bits_eq_spec_unconditional` | The same bit equality for every `ByteArray`. |
| `hash_toList_eq_spec_bytes` | Hash output bytes equal `Spec.sha256_bytes`, unconditionally. |
| `hash_eq_lean4_hash` | Direct equality with `(Hash.Sha256.sha256 data).bytes`. |
| `hash_eq_of_spec_bytes` | Equality with the canonical byte array reconstructed from spec bytes. |
| `combine_bits_eq_fips_spec` | Bounded bit equality for two concatenated byte arrays. |
| `combine_toList_eq_spec_bytes` | Unconditional byte equality for concatenation. |
| `batch_combine_map_eq_spec_bytes` | Pointwise equality of the exact pure array zip/map batch expression. |
| `hash_empty_take28_ne_sha224_empty` | SHA-256's empty digest prefix differs from SHA-224's empty digest. |

FIPS 180-4's byte-aligned domain is **strictly fewer than `2^61` bytes**
(fewer than `2^64` bits). Both total Lean implementations encode length
modulo `2^64` beyond that bound. The unconditional theorems equate these
total extensions; they do not enlarge the FIPS domain. The batch theorem
preserves `Array.zip`'s truncation to the shorter input array.

The proof aligns constants, schedule prefixes, rounds, padding, block reads,
block folds, and output serialization with `Hash.Sha256.Fast`. Its existing
`sha256_eq_impl` and `Bridge.sha256_bridge` then connect to the bit-level
specification. `Upstream.lean` uses a small term elaborator to refer directly
to the pinned private `LeanSha256.Core` constants. The aliases contain no
copied implementation bodies, and the kernel checks proofs against the
original declarations. Bridge files omit the `module` header because Lean
4.34.1 disallows importing non-module `LeanSha256.Core` from a module file.

## Reproduce

Use the already installed `leanprover/lean4:v4.34.1` toolchain. From this
package directory:

```sh
lake build
lake exe sha256-bridge-vectors
```

The default targets build the whole library (including `Audit.lean`) and the
compiled runner. For a clean-slate reproduction, remove `.lake` first, or
move it outside the package on the same filesystem, verify it is absent,
and run the two commands again. Both pinned repositories are fetched anew;
no dependency build artifact is needed. Do not copy native build artifacts
between machines: LeanSha256's upstream build uses `-march=native`.

### Scoped deprecation configuration

The committed root `lakefile.lean` replaces Lake's `presetup` module facet
and delegates to `Module.presetupFacetConfig.run`. It appends
`warningAsError=false` to the **in-memory module library configuration only
when the package base name is `hash` and the module name is `Hash.Sha256`
or has `Hash.Sha256` as a name-component prefix**. It does not edit any
upstream source or configuration file. The prefix includes SHA-224 and
Context within that module family, but excludes `Hash.Sha3`, `Hash` itself,
LeanSha256, and every package-owned bridge module. This family lives in the
upstream Lake library named `Hash`; a library-name-only override would be
too broad.

Lean 4.34.1 deprecates `if_pos`, `dif_pos`, and `dif_neg` in favor of
`ite_eq_left`, `dite_eq_left`, and `dite_eq_right`. The pinned upstream
predates those renames and sets `warningAsError=true` at
`lakefile.toml:17`. Ticket #26's second coordinator ruling authorizes this
configuration exception. Our own modules retain `warningAsError=true`;
LeanSha256 retains its unchanged upstream options. A successful clean build
has exactly 13 deprecation diagnostics: Spec (4), Impl (2), Digest (1),
and Fast (6). Any other warning or error fails the acceptance gate.

The mechanism uses the installed Lake API for 4.34.1. Reproduction means
building the committed root package from an absent `.lake`, not applying
manual edits to a fetched dependency or relying on an existing cache.

### Proof and vector gates

`Audit.lean` follows the Utf8 pattern: a physical source-tree inventory must
match both the explicit expected inventory and the imported module graph.
It covers all package-owned declarations, including private and generated
ones and the runner. The only source exclusion besides `.lake` is the exact
root `lakefile.lean` build configuration. Every declaration's transitive
axioms must be contained in `propext`, `Classical.choice`, and `Quot.sound`;
headline axiom output is pinned with `#guard_msgs`. The audit covers **134
declarations across 9 imported modules**, with all **10** source modules
accounted for (the tenth is the declaration-free audit entrypoint). Upstream's unreferenced
smoke examples are outside the selected roots; the full dependency closure
of each selected declaration is still checked, including zero reachability
of `Lean.ofReduceBool`, `Lean.trustCompiler`, and `sorryAx`.

Ten `decide +kernel` known-answer gates cover empty, `abc`, FIPS Appendix
B.2, and repeated ASCII `a` at lengths 1, 55, 63, 64, 65, 119, and 120.
Their padded block counts total **17**, with at most three per vector.
The negative SHA-224 witness reuses the proved SHA-256 empty value and
adds one one-block SHA-224 reduction.

The **compiled runner only** checks the million-`a` vector (**15,626**
padded blocks), all **129** CAVP vectors (65 ShortMsg and 64 LongMsg), and
257 boundary lengths from 0 through 256. Both pure implementations must
match the published digest for every FIPS/CAVP case and each other in the
boundary sweep. CAVP files are read from the pinned LeanSha256 dependency;
`Len = 0` treats `Msg = 00` as an empty-message placeholder. Neither
`LeanSha256Tests` nor the dependency's CAVP proof suites are build targets.

## Provenance

| Dependency | Full commit pin | Upstream license |
| --- | --- | --- |
| [etheorem/LeanSha256](https://github.com/etheorem/LeanSha256) | `f3432475b3233b259b65443da762bb590bcf8398` | LGPL-3.0-only |
| [pure-algebra/lean4-hash](https://github.com/pure-algebra/lean4-hash) | `ab7eda433f0390fde7aa240189761540c9744c79` | MIT |

Both are unmodified Lake git dependencies, not vendored code. Their license
texts stay in their fetched repositories. This change adds no repository or
package license grant and distributes no compiled binary. License choices
remain the owner's decision. The standard-to-Lean transcription is a human
specification choice; the bridge establishes equality of the pinned Lean
functions, not an independent verification of that transcription.
