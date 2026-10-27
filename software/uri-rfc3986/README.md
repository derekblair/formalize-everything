# URI (RFC 3986) — generic syntax, formalized in Lean 4

A formalization of the Uniform Resource Identifier generic syntax of
[RFC 3986](https://www.rfc-editor.org/rfc/rfc3986), at the
formalize-everything programme bar: zero sorries, exit-0 build, standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`), faithful
statements.

**Milestone 2** (author implementation for [ticket #30](https://github.com/derekblair/formalize-everything/issues/30),
pending coordinator-appointed crossed review): §5.2 reference resolution,
with the literal two-buffer remove-dot-segments algorithm, merge and
transform case laws, an exact guarded target-validity characterization,
and all §5.4 examples as resolution theorems. Milestone 1's complete
Appendix A grammar and §5.3 recomposition bridge remain unchanged.

Build it with:

```
lake build        # toolchain leanprover/lean4:v4.34.1, via elan
```

No Mathlib or other package dependency; both milestones use Lean core.
`Checks.lean` retains the M1 audit, and `ResolveChecks.lean` prints the
axioms of the new theorem families into the build log. Concrete examples
use kernel `decide`. The toolchain remains `leanprover/lean4:v4.34.1`.

## Design: the grammar as derivation trees

Each ABNF rule is a Lean type of *derivation trees* (parse trees), with
a `render` function computing the character string a tree derives. A
string `s` belongs to rule `X` iff some tree `t : X` has
`X.render t = s`. Working with trees, rather than with a recognizer,
is what makes membership of concrete examples checkable by `decide`:
exhibit the tree, and `decide` verifies that it renders to the string.

The ABNF maps to Lean one-for-one:

| ABNF | Lean |
|---|---|
| alternation `A / B / C` | an inductive type, one constructor per alternative, in ABNF order |
| concatenation | structure fields / constructor arguments |
| `*X` | `List X` |
| `1*X` | `NEList X` (a head and a tail) |
| `[ X ]` | `Option X` |
| a rule that is only a repetition/option of others | a definition (alias) with its own `render` |
| character classes (`ALPHA`, `unreserved`, …) | decidable predicates on `Char`, stated with the ABNF's own `%x` code-point ranges |
| numeric side conditions (`dec-octet` ranges, `h16 = 1*4HEXDIG`, the `*k` IPv6 prefix bounds) | proof fields of the tree — they are part of the rule as written |

Because `[ X ]` is `Option X`, the specification never conflates an
*absent* component with a *present but empty* one: an authority with no
port (`none`) is a different tree from one with an empty port
(`some []`, from `":"` followed by zero digits), exactly as the ABNF
distinguishes them.

## Prior art (dossier v2, 2026-10-27)

The M2 scoping dossier and its crossed re-review classify proved-level
novelty as **PARTIAL**, not CLEAN. In particular,
[`danbri/factoidal`](https://github.com/danbri/factoidal/blob/claude/main/formal/lean4/L4Factoidal/Syntax/TurtleTheorems.lean)
and its [`factoidal-core` mirror](https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Syntax/TurtleTheorems.lean)
contain **19 proved §5.2 theorems**: eight on §5.2.2 Case 1 and eleven
on a no-dot-segments invariant. This corrects the earlier claim that
there were no proved §5.2 results. The file has 25 theorem declarations
in total, with six additional helper definitions; its six other theorems
concern Turtle parsing and streaming folds.

The dossier identifies four gaps between that work and this milestone:

1. Its segment-stack dot-removal differs from the RFC buffer algorithm:
   the exact input `..` returns `/`, contrary to rule D's empty result.
2. Its dot-removal proof establishes a no-dot-segments postcondition;
   it does not establish fuel sufficiency, idempotence, leading-slash
   preservation, conservation, fixed points, or the official traces.
3. It has no merge or Branches 2–5 theorem families or compatibility
   mode; its §5.4 checks are elaborator `#guard`s, rather than named
   kernel-checked resolution theorems.
4. It works over an unvalidated string splitter, without an Appendix A
   grammar or a target-validity characterization against that grammar.

Other precedents are partial in different ways. Lean v4.34.1's
`Std.Http.Data.URI` provides HTTP-oriented parsers, an unproved
stack-based path `normalize`, and internal encoding proofs; it does not
supply a §5.2 resolver or grammar-validity proof. Its host syntax is
narrower than Appendix A. `josephmckinsey/lean-uri` implements resolution
with a partial dot-removal function and tests, but no theorems;
`ammkrn/lean-url` targets WHATWG and has no RFC §5.2 proof package.
ACL2 Community Books includes RFC 3986 ABNF work, so no claim is made
that RFC 3986 has never been mechanized elsewhere. The dossier's
cross-prover search found no equivalent proved M2 package; `CoqURL`
remained unverified. These are the dated dossier findings, not a claim
of exhaustive or permanent uniqueness.

## Coverage account

The specification was written against, and then checked rule by rule
against, the **collected ABNF in Appendix A** of the RFC (reproduced
below — it is the specification being formalized). Every rule of
Appendix A is present:

- Top level: `URI`, `URI-reference`, `absolute-URI`, `relative-ref`,
  `relative-part`, `hier-part`.
- Authority: `authority`, `userinfo`, `host`, `port`.
- Hosts: `IP-literal`, `IPv6address` (all nine alternatives),
  `IPvFuture`, `h16`, `ls32`, `IPv4address`, `dec-octet` (all five
  alternatives), `reg-name`.
- Paths: `path` and all five of its alternatives — `path-abempty`,
  `path-absolute`, `path-noscheme`, `path-rootless`, `path-empty` —
  plus `segment`, `segment-nz`, `segment-nz-nc`, `pchar`.
- Leaves: `scheme`, `query`, `fragment`, `pct-encoded`, `unreserved`,
  `reserved`, `gen-delims`, `sub-delims`, and the core rules `ALPHA`,
  `DIGIT`, `HEXDIG`.

Five fidelity points that a from-memory transcription typically gets
wrong; the first four were caught by working from Appendix A itself,
the fifth in review:

1. **`IP-literal` has no zone-id alternative.** As published, it is
   `"[" ( IPv6address / IPvFuture ) "]"`. `IPv6addrz` is RFC 6874
   (2013), an update to RFC 3986, and is deliberately *not* included;
   it is listed under future scope below.
2. **The sixth `IPv6address` alternative** ends `… "::" h16 ":" ls32`,
   not `… "::" 1( h16 ":" ) ls32` (the latter is the RFC 4291 style).
   The constructor `IPv6Address.compressed4` follows the RFC 3986 text.
3. **`relative-part` has no `path-rootless` alternative.** Rootless
   paths occur only in `hier-part`; a relative reference whose first
   segment is nonempty goes through `path-noscheme`, with its stronger
   no-colon first segment. The two part types are distinct inductives
   here, so the distinction is enforced by construction.
4. **`path` keeps its five alternatives separate**, including
   `path-empty` (exactly zero characters), and `path-absolute`'s
   bracketed tail is two constructors (`empty` / `nonempty`), so a
   tree cannot render `//…` while claiming to be path-absolute.
5. **The `IPvFuture` marker is case-insensitive.** Appendix A writes
   the rule with a lowercase `"v"`, but §3.2.2 states that an
   IP-literal starts with `"v"` (case-insensitive), so `V…` literals
   are in the language too. The tree preserves the marker's case
   (`IPvFutureMarker`) and both spellings carry `decide`-checked
   examples; a renderer hardcoding `'v'` would silently drop half
   the rule.

One honest limitation of the tree presentation: the ABNF is ambiguous
as a *language* definition — e.g. a dotted-quad string matches both
`IPv4address` and `reg-name` in `host`. The specification defines the
language as the union over the alternatives, which is what the ABNF
means. Disambiguation (the RFC's "first-match-wins" discussion) is a
property of a *parser*, and belongs to the parser milestone below.

### §5.2 — reference resolution

`Resolve.lean` implements the published §5.2 algorithm over M1's
`Components`. `removeDotSegments` follows rules A–E in order, with
separate input and output buffers. Rule E leaves the next slash in the
input; rule C removes the last output segment and its preceding slash.
The delimiter-preserving splitter satisfies
`joinSlash (splitSlash p) = p`, including empty, leading, repeated, and
trailing segments. Structural fuel ensures termination, and
`rds_fuel_sufficient` proves that every budget at least the input length
agrees with the public `length + 2` budget.

The theorem families establish idempotence, absence of complete `.` and
`..` output segments, preservation of an initial slash, character and
segment conservation, and the fixed-point property for dot-free input.
Both official §5.2.4 buffer traces are golden theorems. The literal
rootless behavior is also pinned: `a/../b` becomes `/b`, and `a/../..`
becomes `/`. These are consequences of the buffer rules.

`merge` takes the base authority as well as both paths, making the
context needed by §5.2.3's first bullet explicit. Its case family covers
an authority-bearing empty base path, a base containing a slash, and
the no-slash case under the first bullet's "otherwise" condition.
`applyStrict` performs the optional equal-scheme undefinition before
`transformReferencesCore`; five case lemmas then mirror the five
pseudocode branches. The main theorems quantify over a base `URI` tree
and a `URIReference` tree, supplying §5.2.1's parsed-input preconditions.
Both strict modes are covered.

Resolution does **not** unconditionally preserve the URI grammar.
For `T = transformReferences strict b.components x.components`, the
exact characterization is:

```lean
(∃ t : URI, t.components = T) ↔
  (T.authority.isSome ∨ ¬ ['/', '/'].isPrefixOf T.path)
```

The predicate on the right is `ValidTargetComponents`. `target` takes
its proof and constructs a target tree; `target_components` and
`target_render` identify that tree's components and rendering with `T`
and §5.3 recomposition. Path reconstruction retains segment witnesses
from the input trees, including entire percent-encoded tokens.
`targetRelOfAuthority` discharges the guard for a `RelativeRef` and an
authority-bearing base.

The boundary is substantive. Against base `g:h`, reference `/.//g`
produces no target tree with the computed components, although
recomposition yields `g://g`, which assigns `g` to the authority when
read as a URI. Reference `/.//a:b` yields `g://a:b`, for which no URI
tree exists at all: `b` cannot be a port digit. The corresponding
nonexistence and recomposition statements are proved structurally
against M1's grammar.

The published algorithm is retained in the errata cases identified by
the dossier: eid2933 explains the authority context needed by merge;
eid4789's dotted-base proposal does not replace the published merge;
eid4547 does not replace §5.4.2's beyond-root clamp. All three were
Held for Document Update in the dossier's 2026-10-27 snapshot. Editorial
eid7590 concerns a hyperlink in a trace label, not buffer semantics.

### §5.3 — components and recomposition

`Components.lean` defines the five components (scheme, authority, path,
query, fragment — the path always defined, the rest `Option`s, per the
RFC's undefined-vs-empty distinction) and `recompose`, the §5.3
algorithm transcribed step for step. Recomposition is *stated against
the grammar* as a theorem family: for every tree `t` of `URI`,
`absolute-URI`, `relative-ref`, and `URI-reference`,

```
recompose t.components = t.render
```

i.e. extracting a tree's components and recomposing them returns the
string the tree derives. All four theorems are proved; each depends
only on `propext` (see `Checks.lean`, whose `#print axioms` output is
part of the build log).

### §5.4 — the resolution examples

`Examples.lean` represents, as derivation trees:

- the §5.4 base URI `http://a/b/c/d;p?q`;
- **all 23 references of §5.4.1** (normal examples), and **all 18
  target URIs** they resolve to, each target as a `URI` tree;
- **all 19 references of §5.4.2** (abnormal examples), including the
  dot-segments-in-query/fragment cases and the strict reading of
  `http:g`;
- extra trees exercising what §5.4 does not: an IPv4 host with a port
  (`http://192.168.0.250:8080/p?q#f`), IPv6 literals (compressed
  `2001:db8::1`, full `1:2:3:4:5:6:7:8`, and `::`), IPvFuture literals
  in both marker cases (`http://[v1.a]/` and `http://[V1.a]/`), a
  userinfo authority (`ftp://user@example.com/`), and a
  percent-encoded segment (`http://a/%7Euser`).

Every one of these carries a `*_render` theorem proved by `decide` —
73 membership checks in all — exhibiting the tree and verifying it
derives the example string character for character. M1's file is
byte-identical to the landed version.

`Examples54.lean` adds the correspondence: all **42 references** are
resolved against `base`, with **43 component-level theorems and 43
recomposed-string theorems**, because `http:g` is checked in both modes.
It also supplies the twelve additional §5.4.2 target trees with kernel
`decide` render proofs. The numbered theorem comments record each
branch, dot-removal input, and rule sequence from dossier v2 §4.

Exactly the **40 relative references (#2–#41)** instantiate
`targetRelOfAuthority`. The scheme-bearing Branch-1 cases **#1 `g:h`**
and **#42 strict `http:g`** instantiate guarded `target` directly.
A URI-reference wrapper also covers the compatibility-mode `http:g`
assertion, for 41 of the 43 assertions. The two direct guarded cases
satisfy the no-leading-`//` disjunct, not the authority disjunct.

Six further resolution pairs are explicitly labelled **beyond-RFC
pins**, covering dossier §4.3 items 1–5: an authority-bearing empty
base path with `g` and with an empty reference; dropping a base fragment;
a rootless base; a dotted base path; and a foreign-scheme rootless path
whose dot removal becomes absolute (`s2:a/../b` → `s2:/b`).

## What this does not show

The result concerns the published RFC algorithm on grammar trees and
its computed components. It does not prove a parser correct, accept
arbitrary input strings, implement retrieval-context base discovery
(§5.1), or establish networking behavior. It does not assert that every
resolved component tuple is a URI, that recomposition preserves component
boundaries for invalid tuples, or that all syntactically valid URIs
identify usable resources. Percent-encoding theory, URI equivalence,
and §6 normalization remain outside this milestone.

## Remaining scope (later milestones)

- **Executable parser**: a function from strings to trees (or failure),
  with *soundness* (every accepted string is derivable) and
  *completeness* (every derivable string is accepted) against this
  specification, including first-match-wins disambiguation for `host`
  and the Appendix B regular-expression equivalence.
- **Percent-encoding theory**: the §2.1 encoding/decoding maps and their
  round-trip properties.
- **Normalization and comparison**: the §6 ladder — case
  normalization, percent-encoding normalization, path-segment
  normalization — and equivalence of URIs.
- **Updates**: RFC 6874 zone identifiers for IP literals.

## The specification being formalized

RFC 3986, Appendix A (the ABNF rules only):

```
   URI           = scheme ":" hier-part [ "?" query ] [ "#" fragment ]

   hier-part     = "//" authority path-abempty
                 / path-absolute
                 / path-rootless
                 / path-empty

   URI-reference = URI / relative-ref

   absolute-URI  = scheme ":" hier-part [ "?" query ]

   relative-ref  = relative-part [ "?" query ] [ "#" fragment ]

   relative-part = "//" authority path-abempty
                 / path-absolute
                 / path-noscheme
                 / path-empty

   scheme        = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )

   authority     = [ userinfo "@" ] host [ ":" port ]
   userinfo      = *( unreserved / pct-encoded / sub-delims / ":" )
   host          = IP-literal / IPv4address / reg-name
   port          = *DIGIT

   IP-literal    = "[" ( IPv6address / IPvFuture  ) "]"

   IPvFuture     = "v" 1*HEXDIG "." 1*( unreserved / sub-delims / ":" )

   IPv6address   =                            6( h16 ":" ) ls32
                 /                       "::" 5( h16 ":" ) ls32
                 / [               h16 ] "::" 4( h16 ":" ) ls32
                 / [ *1( h16 ":" ) h16 ] "::" 3( h16 ":" ) ls32
                 / [ *2( h16 ":" ) h16 ] "::" 2( h16 ":" ) ls32
                 / [ *3( h16 ":" ) h16 ] "::"    h16 ":"   ls32
                 / [ *4( h16 ":" ) h16 ] "::"              ls32
                 / [ *5( h16 ":" ) h16 ] "::"              h16
                 / [ *6( h16 ":" ) h16 ] "::"

   h16           = 1*4HEXDIG
   ls32          = ( h16 ":" h16 ) / IPv4address
   IPv4address   = dec-octet "." dec-octet "." dec-octet "." dec-octet

   dec-octet     = DIGIT                 ; 0-9
                 / %x31-39 DIGIT         ; 10-99
                 / "1" 2DIGIT            ; 100-199
                 / "2" %x30-34 DIGIT     ; 200-249
                 / "25" %x30-35          ; 250-255

   reg-name      = *( unreserved / pct-encoded / sub-delims )

   path          = path-abempty    ; begins with "/" or is empty
                 / path-absolute   ; begins with "/" but not "//"
                 / path-noscheme   ; begins with a non-colon segment
                 / path-rootless   ; begins with a segment
                 / path-empty      ; zero characters

   path-abempty  = *( "/" segment )
   path-absolute = "/" [ segment-nz *( "/" segment ) ]
   path-noscheme = segment-nz-nc *( "/" segment )
   path-rootless = segment-nz *( "/" segment )
   path-empty    = 0<pchar>

   segment       = *pchar
   segment-nz    = 1*pchar
   segment-nz-nc = 1*( unreserved / pct-encoded / sub-delims / "@" )

   pchar         = unreserved / pct-encoded / sub-delims / ":" / "@"

   query         = *( pchar / "/" / "?" )
   fragment      = *( pchar / "/" / "?" )

   pct-encoded   = "%" HEXDIG HEXDIG

   unreserved    = ALPHA / DIGIT / "-" / "." / "_" / "~"
   reserved      = gen-delims / sub-delims
   gen-delims    = ":" / "/" / "?" / "#" / "[" / "]" / "@"
   sub-delims    = "!" / "$" / "&" / "'" / "(" / ")"
                 / "*" / "+" / "," / ";" / "="
```

## Layout

```
lean-toolchain            leanprover/lean4:v4.34.1
lakefile.lean             package uri-rfc3986, lib UriRfc3986
UriRfc3986.lean           root module
UriRfc3986/Chars.lean     character classes (decidable, %x ranges)
UriRfc3986/Grammar.lean   the Appendix A grammar as derivation trees
UriRfc3986/Components.lean  §5.3 components, recompose, and its theorems
UriRfc3986/Examples.lean  §5.4 examples as trees, decide-checked
UriRfc3986/Checks.lean    unchanged #print axioms audit for M1
UriRfc3986/Resolve.lean   §5.2 definitions, laws, and target-validity package
UriRfc3986/Examples54.lean  §5.4 resolution pairs and beyond-RFC pins
UriRfc3986/ResolveChecks.lean  #print axioms audit for M2
```
