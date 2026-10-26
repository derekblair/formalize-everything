# URI (RFC 3986) — generic syntax, formalized in Lean 4

A formalization of the Uniform Resource Identifier generic syntax of
[RFC 3986](https://www.rfc-editor.org/rfc/rfc3986), at the
formalize-everything programme bar: zero sorries, exit-0 build, standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`), faithful
statements.

**Milestone 1** (this state): the complete ABNF of RFC 3986 as an
inductive specification; the §5.3 components and recomposition
algorithm, proved consistent with the grammar; and the §5.4 examples
represented at spec level with machine-checked membership.

Build it with:

```
lake build        # toolchain leanprover/lean4:v4.34.1, via elan
```

No Mathlib. Milestone 1 is pure Lean core — a grammar specification
needs nothing from a mathematics library, and keeping the dependency
surface empty keeps the specification light and its axiom audit
trivial to read.

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

## Prior art (checked 2026-10-26; the Std account corrected in review)

A sweep of Lean libraries and of other proof assistants found:

- **Lean's own standard library ships an RFC 3986-oriented URI
  library**: `Std.Http.Data.URI`, part of the Lean v4.34.1 toolchain
  this project pins. It provides *executable parsers* (`URI.parse?`,
  `URIReference.parse?`) for a narrower, HTTP-oriented subset of the
  syntax — its own documentation states that hosts are limited to
  IPv4, bracketed IPv6, and DNS-style domain names (the full
  `reg-name` syntax is not accepted) and that `IPvFuture` is
  currently rejected. It contains no specification of the Appendix A
  grammar and no proofs about the grammar or the parsers' fidelity
  to it: it is a parsing library, not a formalization.
- The one other Lean URL library targets the **WHATWG** URL
  Standard — a different, living-standard specification (forgiving
  parsing, a mutable URL object) — and proves nothing about it.
- No mechanization of RFC 3986 was found in Coq, Isabelle, or Dafny
  either.

So this is, as far as the sweep could determine, the first
machine-checked *specification* of the complete RFC 3986 grammar in
any proof assistant: all of Appendix A as derivation trees, including
the complete `IPvFuture` alternative (both marker cases) that Std's
parser rejects. (Adjacent work exists for other specifications and
other assistants, and WHATWG formalizations exist elsewhere; neither
is this grammar in Lean.)

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
derives the example string character for character. The
reference↔target *correspondence* of §5.4 is not claimed yet: that is
the resolution milestone.

## Remaining scope (later milestones)

- **Executable parser**: a function from strings to trees (or failure),
  with *soundness* (every accepted string is derivable) and
  *completeness* (every derivable string is accepted) against this
  specification, including first-match-wins disambiguation for `host`
  and the Appendix B regular-expression equivalence.
- **Reference resolution**: the §5.2 algorithm (transform references,
  merge paths, remove dot segments) as a function on trees, and the
  §5.4 correspondence theorem: resolving each example reference against
  the §5.4 base yields its stated target.
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
UriRfc3986/Checks.lean    #print axioms audit for the milestone
```
