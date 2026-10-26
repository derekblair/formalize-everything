import UriRfc3986.Chars

/-!
# The RFC 3986 grammar (Appendix A) as an inductive specification

Each ABNF rule becomes a type of *derivation trees*: an inhabitant is a
parse tree for that rule, and the rule's `render` function computes the
character string the tree derives. A string `s` belongs to rule `X` iff
there is a tree `t : X` with `X.render t = s`.

Conventions, mirroring the ABNF one-for-one:

* an alternation `A / B / C` becomes an inductive type whose constructors
  are the alternatives, in ABNF order;
* a concatenation becomes structure fields (or constructor arguments);
* `*X` becomes `List X`, `1*X` becomes `NEList X`, `[ X ]` becomes
  `Option X` — so *absent* and *present-but-empty* are never conflated;
* a rule that is nothing but a repetition or option of other rules is a
  definition (alias), not a new inductive, and carries its own `render`.

The one place where a tree carries a proof is where the ABNF itself is
proof-shaped: digit ranges in `dec-octet`, the `1*4` bound in `h16`, and
the `*k` bounds on IPv6 compression prefixes. Those side conditions are
part of the rule as written, so they are fields of the tree.

Two fidelity points that are easy to get wrong from memory (both checked
against the collected ABNF in Appendix A of the RFC):

* `IP-literal = "[" ( IPv6address / IPvFuture ) "]"` — there is **no**
  zone-id alternative; `IPv6addrz` is RFC 6874, not RFC 3986.
* The sixth `IPv6address` alternative ends in `h16 ":" ls32`, not in
  `1( h16 ":" ) ls32`.
-/

/-- A nonempty list of items: the ABNF repetition `1*`. -/
structure NEList (α : Type) where
  head : α
  tail : List α

/-- Render a nonempty list, given a rendering for its items. -/
def NEList.render {α : Type} (f : α → List Char) (l : NEList α) : List Char :=
  f l.head ++ l.tail.flatMap f

/-! ## Percent-encoding and the character-level rules -/

/-- `pct-encoded = "%" HEXDIG HEXDIG` -/
structure PctEncoded where
  h₁ : HexDigChar
  h₂ : HexDigChar

def PctEncoded.render (p : PctEncoded) : List Char :=
  ['%', p.h₁.1, p.h₂.1]

/-- `pchar = unreserved / pct-encoded / sub-delims / ":" / "@"` -/
inductive PChar where
  | unreserved (c : Char) (h : IsUnreserved c)
  | pctEncoded (p : PctEncoded)
  | subDelims (c : Char) (h : IsSubDelim c)
  | colon
  | at

def PChar.render : PChar → List Char
  | .unreserved c _ => [c]
  | .pctEncoded p => p.render
  | .subDelims c _ => [c]
  | .colon => [':']
  | .at => ['@']

/-- One character of `userinfo = *( unreserved / pct-encoded / sub-delims / ":" )`. -/
inductive UserinfoChar where
  | unreserved (c : Char) (h : IsUnreserved c)
  | pctEncoded (p : PctEncoded)
  | subDelims (c : Char) (h : IsSubDelim c)
  | colon

def UserinfoChar.render : UserinfoChar → List Char
  | .unreserved c _ => [c]
  | .pctEncoded p => p.render
  | .subDelims c _ => [c]
  | .colon => [':']

/-- One character of `reg-name = *( unreserved / pct-encoded / sub-delims )`. -/
inductive RegNameChar where
  | unreserved (c : Char) (h : IsUnreserved c)
  | pctEncoded (p : PctEncoded)
  | subDelims (c : Char) (h : IsSubDelim c)

def RegNameChar.render : RegNameChar → List Char
  | .unreserved c _ => [c]
  | .pctEncoded p => p.render
  | .subDelims c _ => [c]

/-- One character of
`segment-nz-nc = 1*( unreserved / pct-encoded / sub-delims / "@" )`. -/
inductive SegNZNCChar where
  | unreserved (c : Char) (h : IsUnreserved c)
  | pctEncoded (p : PctEncoded)
  | subDelims (c : Char) (h : IsSubDelim c)
  | at

def SegNZNCChar.render : SegNZNCChar → List Char
  | .unreserved c _ => [c]
  | .pctEncoded p => p.render
  | .subDelims c _ => [c]
  | .at => ['@']

/-- One character of `query = *( pchar / "/" / "?" )`. -/
inductive QueryChar where
  | pchar (p : PChar)
  | slash
  | qmark

def QueryChar.render : QueryChar → List Char
  | .pchar p => p.render
  | .slash => ['/']
  | .qmark => ['?']

/-- One character of `fragment = *( pchar / "/" / "?" )`. The rule body is
textually identical to `query`; it is a separate type so that the two rule
names stay one-for-one with the ABNF. -/
inductive FragmentChar where
  | pchar (p : PChar)
  | slash
  | qmark

def FragmentChar.render : FragmentChar → List Char
  | .pchar p => p.render
  | .slash => ['/']
  | .qmark => ['?']

/-! ## Scheme -/

/-- One character of the tail of a scheme: `ALPHA / DIGIT / "+" / "-" / "."`. -/
inductive SchemeChar where
  | alpha (c : Char) (h : IsAlpha c)
  | digit (c : Char) (h : IsDigit c)
  | plus
  | minus
  | dot

def SchemeChar.render : SchemeChar → List Char
  | .alpha c _ => [c]
  | .digit c _ => [c]
  | .plus => ['+']
  | .minus => ['-']
  | .dot => ['.']

/-- `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )` -/
structure Scheme where
  first : AlphaChar
  rest : List SchemeChar

def Scheme.render (s : Scheme) : List Char :=
  s.first.1 :: s.rest.flatMap SchemeChar.render

/-! ## IP addresses and host -/

/-- `dec-octet`, with one constructor per ABNF alternative:
`DIGIT` (0–9), `%x31-39 DIGIT` (10–99), `"1" 2DIGIT` (100–199),
`"2" %x30-34 DIGIT` (200–249), `"25" %x30-35` (250–255). -/
inductive DecOctet where
  | single (d : Char) (h : IsDigit d)
  | twoDigit (d₁ d₂ : Char) (h₁ : 49 ≤ d₁.toNat ∧ d₁.toNat ≤ 57) (h₂ : IsDigit d₂)
  | oneHundred (d₂ d₃ : Char) (h₂ : IsDigit d₂) (h₃ : IsDigit d₃)
  | twoHundred (d₂ d₃ : Char) (h₂ : 48 ≤ d₂.toNat ∧ d₂.toNat ≤ 52) (h₃ : IsDigit d₃)
  | twoFifty (d₃ : Char) (h₃ : 48 ≤ d₃.toNat ∧ d₃.toNat ≤ 53)

def DecOctet.render : DecOctet → List Char
  | .single d _ => [d]
  | .twoDigit d₁ d₂ _ _ => [d₁, d₂]
  | .oneHundred d₂ d₃ _ _ => ['1', d₂, d₃]
  | .twoHundred d₂ d₃ _ _ => ['2', d₂, d₃]
  | .twoFifty d₃ _ => ['2', '5', d₃]

/-- `IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet` -/
structure IPv4Address where
  o₁ : DecOctet
  o₂ : DecOctet
  o₃ : DecOctet
  o₄ : DecOctet

def IPv4Address.render (a : IPv4Address) : List Char :=
  a.o₁.render ++ ['.'] ++ a.o₂.render ++ ['.'] ++ a.o₃.render ++ ['.'] ++ a.o₄.render

/-- `h16 = 1*4HEXDIG` — one to four hexadecimal digits. -/
structure H16 where
  digits : List HexDigChar
  hnonempty : 0 < digits.length
  hmax : digits.length ≤ 4

def H16.render (h : H16) : List Char :=
  h.digits.flatMap fun d => [d.1]

/-- `ls32 = ( h16 ":" h16 ) / IPv4address` -/
inductive Ls32 where
  | h16Pair (a b : H16)
  | ipv4 (addr : IPv4Address)

def Ls32.render : Ls32 → List Char
  | .h16Pair a b => a.render ++ [':'] ++ b.render
  | .ipv4 addr => addr.render

/-- Exactly `n` copies of `h16 ":"` — the fixed repetitions `n( h16 ":" )`
in `IPv6address`. -/
structure H16Run (n : Nat) where
  groups : List H16
  hlen : groups.length = n

def H16Run.render {n : Nat} (r : H16Run n) : List Char :=
  r.groups.flatMap fun h => h.render ++ [':']

/-- A compression prefix `*k( h16 ":" ) h16` — at most `k` copies of
`h16 ":"` followed by a final `h16`. These are the bracketed prefixes of
the `IPv6address` alternatives. -/
structure IPv6Prefix (k : Nat) where
  groups : List H16
  last : H16
  hlen : groups.length ≤ k

def IPv6Prefix.render {k : Nat} (p : IPv6Prefix k) : List Char :=
  p.groups.flatMap (fun h => h.render ++ [':']) ++ p.last.render

/-- `IPv6address`, one constructor per ABNF alternative, in order:

1. `6( h16 ":" ) ls32`
2. `"::" 5( h16 ":" ) ls32`
3. `[ h16 ] "::" 4( h16 ":" ) ls32`
4. `[ *1( h16 ":" ) h16 ] "::" 3( h16 ":" ) ls32`
5. `[ *2( h16 ":" ) h16 ] "::" 2( h16 ":" ) ls32`
6. `[ *3( h16 ":" ) h16 ] "::" h16 ":" ls32`
7. `[ *4( h16 ":" ) h16 ] "::" ls32`
8. `[ *5( h16 ":" ) h16 ] "::" h16`
9. `[ *6( h16 ":" ) h16 ] "::"`
-/
inductive IPv6Address where
  | full (run : H16Run 6) (ls : Ls32)
  | compressed0 (run : H16Run 5) (ls : Ls32)
  | compressed1 (head : Option H16) (run : H16Run 4) (ls : Ls32)
  | compressed2 (pre : Option (IPv6Prefix 1)) (run : H16Run 3) (ls : Ls32)
  | compressed3 (pre : Option (IPv6Prefix 2)) (run : H16Run 2) (ls : Ls32)
  | compressed4 (pre : Option (IPv6Prefix 3)) (h : H16) (ls : Ls32)
  | compressed5 (pre : Option (IPv6Prefix 4)) (ls : Ls32)
  | compressed6 (pre : Option (IPv6Prefix 5)) (h : H16)
  | compressed7 (pre : Option (IPv6Prefix 6))

def IPv6Address.render : IPv6Address → List Char
  | .full run ls => run.render ++ ls.render
  | .compressed0 run ls => [':', ':'] ++ run.render ++ ls.render
  | .compressed1 head run ls =>
      (head.map H16.render).getD [] ++ [':', ':'] ++ run.render ++ ls.render
  | .compressed2 pre run ls =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':'] ++ run.render ++ ls.render
  | .compressed3 pre run ls =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':'] ++ run.render ++ ls.render
  | .compressed4 pre h ls =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':'] ++ h.render ++ [':'] ++ ls.render
  | .compressed5 pre ls =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':'] ++ ls.render
  | .compressed6 pre h =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':'] ++ h.render
  | .compressed7 pre =>
      (pre.map IPv6Prefix.render).getD [] ++ [':', ':']

/-- One character of the tail of an `IPvFuture`:
`unreserved / sub-delims / ":"`. -/
inductive IPvFutureChar where
  | unreserved (c : Char) (h : IsUnreserved c)
  | subDelims (c : Char) (h : IsSubDelim c)
  | colon

def IPvFutureChar.render : IPvFutureChar → List Char
  | .unreserved c _ => [c]
  | .subDelims c _ => [c]
  | .colon => [':']

/-- `IPvFuture = "v" 1*HEXDIG "." 1*( unreserved / sub-delims / ":" )` -/
structure IPvFuture where
  version : NEList HexDigChar
  rest : NEList IPvFutureChar

def IPvFuture.render (f : IPvFuture) : List Char :=
  'v' :: (f.version.render fun d => [d.1]) ++
    '.' :: (f.rest.render IPvFutureChar.render)

/-- `IP-literal = "[" ( IPv6address / IPvFuture ) "]"`.
RFC 3986 has exactly these two alternatives; zone IDs (`IPv6addrz`)
were added later by RFC 6874 and are not part of this specification. -/
inductive IPLiteral where
  | ipv6 (a : IPv6Address)
  | ipvFuture (f : IPvFuture)

def IPLiteral.render : IPLiteral → List Char
  | .ipv6 a => '[' :: a.render ++ [']']
  | .ipvFuture f => '[' :: f.render ++ [']']

/-- `host = IP-literal / IPv4address / reg-name` -/
inductive Host where
  | ipLiteral (l : IPLiteral)
  | ipv4 (a : IPv4Address)
  | regName (chars : List RegNameChar)

def Host.render : Host → List Char
  | .ipLiteral l => l.render
  | .ipv4 a => a.render
  | .regName cs => cs.flatMap RegNameChar.render

/-! ## Authority -/

/-- `port = *DIGIT`. In `Authority` below the port is an `Option Port`, so
that an *absent* port (no `":"`) is distinguished from a *present but
empty* one (`":"` followed by zero digits), exactly as the ABNF
`[ ":" port ]` distinguishes them. -/
def Port := List DigitChar

def Port.render (p : Port) : List Char :=
  p.flatMap fun d => [d.1]

/-- `authority = [ userinfo "@" ] host [ ":" port ]` -/
structure Authority where
  userinfo : Option (List UserinfoChar)
  host : Host
  port : Option Port

def Authority.render (a : Authority) : List Char :=
  (match a.userinfo with
   | some u => u.flatMap UserinfoChar.render ++ ['@']
   | none => []) ++
  a.host.render ++
  (match a.port with
   | some p => ':' :: p.render
   | none => [])

/-! ## Paths -/

/-- `segment = *pchar` -/
def Segment := List PChar

def Segment.render (s : Segment) : List Char :=
  s.flatMap PChar.render

/-- `segment-nz = 1*pchar` -/
def SegmentNZ := NEList PChar

/-- `segment-nz-nc = 1*( unreserved / pct-encoded / sub-delims / "@" )`
(non-zero-length segment without any colon). -/
def SegmentNZNC := NEList SegNZNCChar

/-- `path-abempty = *( "/" segment )` -/
def PathAbempty := List Segment

def PathAbempty.render (p : PathAbempty) : List Char :=
  p.flatMap fun s => '/' :: Segment.render s

/-- `path-absolute = "/" [ segment-nz *( "/" segment ) ]`. The two
constructors are the two cases of the bracketed option: nothing after
the `"/"`, or a non-empty first segment followed by more segments. -/
inductive PathAbsolute where
  | empty
  | nonempty (first : SegmentNZ) (rest : List Segment)

def PathAbsolute.render : PathAbsolute → List Char
  | .empty => ['/']
  | .nonempty first rest =>
      '/' :: (first.render PChar.render) ++
        rest.flatMap fun s => '/' :: Segment.render s

/-- `path-rootless = segment-nz *( "/" segment )` -/
structure PathRootless where
  first : SegmentNZ
  rest : List Segment

def PathRootless.render (p : PathRootless) : List Char :=
  (p.first.render PChar.render) ++
    p.rest.flatMap fun s => '/' :: Segment.render s

/-- `path-noscheme = segment-nz-nc *( "/" segment )` -/
structure PathNoscheme where
  first : SegmentNZNC
  rest : List Segment

def PathNoscheme.render (p : PathNoscheme) : List Char :=
  (p.first.render SegNZNCChar.render) ++
    p.rest.flatMap fun s => '/' :: Segment.render s

/-- `path-empty = 0<pchar>` — exactly zero characters. -/
inductive PathEmpty where
  | mk

def PathEmpty.render : PathEmpty → List Char
  | .mk => []

/-- `path = path-abempty / path-absolute / path-noscheme / path-rootless
/ path-empty`, alternatives in ABNF order. -/
inductive Path where
  | abempty (p : PathAbempty)
  | absolute (p : PathAbsolute)
  | noscheme (p : PathNoscheme)
  | rootless (p : PathRootless)
  | empty (p : PathEmpty)

def Path.render : Path → List Char
  | .abempty p => p.render
  | .absolute p => p.render
  | .noscheme p => p.render
  | .rootless p => p.render
  | .empty p => p.render

/-! ## The top-level rules -/

/-- `hier-part = "//" authority path-abempty / path-absolute
/ path-rootless / path-empty` -/
inductive HierPart where
  | authority (a : Authority) (p : PathAbempty)
  | absolute (p : PathAbsolute)
  | rootless (p : PathRootless)
  | empty (p : PathEmpty)

def HierPart.render : HierPart → List Char
  | .authority a p => ['/', '/'] ++ a.render ++ p.render
  | .absolute p => p.render
  | .rootless p => p.render
  | .empty p => p.render

/-- The authority string of a `hier-part`, if it has one (§5.3 components). -/
def HierPart.authorityString : HierPart → Option (List Char)
  | .authority a _ => some a.render
  | .absolute _ => none
  | .rootless _ => none
  | .empty _ => none

/-- The path string of a `hier-part` (§5.3 components). -/
def HierPart.pathString : HierPart → List Char
  | .authority _ p => p.render
  | .absolute p => p.render
  | .rootless p => p.render
  | .empty p => p.render

/-- `relative-part = "//" authority path-abempty / path-absolute
/ path-noscheme / path-empty`. Note there is no `path-rootless` here:
that alternative exists only in `hier-part`. -/
inductive RelativePart where
  | authority (a : Authority) (p : PathAbempty)
  | absolute (p : PathAbsolute)
  | noscheme (p : PathNoscheme)
  | empty (p : PathEmpty)

def RelativePart.render : RelativePart → List Char
  | .authority a p => ['/', '/'] ++ a.render ++ p.render
  | .absolute p => p.render
  | .noscheme p => p.render
  | .empty p => p.render

/-- The authority string of a `relative-part`, if it has one. -/
def RelativePart.authorityString : RelativePart → Option (List Char)
  | .authority a _ => some a.render
  | .absolute _ => none
  | .noscheme _ => none
  | .empty _ => none

/-- The path string of a `relative-part`. -/
def RelativePart.pathString : RelativePart → List Char
  | .authority _ p => p.render
  | .absolute p => p.render
  | .noscheme p => p.render
  | .empty p => p.render

/-- `query = *( pchar / "/" / "?" )` -/
def Query := List QueryChar

def Query.render (q : Query) : List Char :=
  q.flatMap QueryChar.render

/-- `fragment = *( pchar / "/" / "?" )` -/
def Fragment := List FragmentChar

def Fragment.render (f : Fragment) : List Char :=
  f.flatMap FragmentChar.render

/-- `URI = scheme ":" hier-part [ "?" query ] [ "#" fragment ]` -/
structure URI where
  scheme : Scheme
  hierPart : HierPart
  query : Option Query
  fragment : Option Fragment

def URI.render (u : URI) : List Char :=
  u.scheme.render ++ [':'] ++ u.hierPart.render ++
  (match u.query with
   | some q => '?' :: q.render
   | none => []) ++
  (match u.fragment with
   | some f => '#' :: f.render
   | none => [])

/-- `absolute-URI = scheme ":" hier-part [ "?" query ]` -/
structure AbsoluteURI where
  scheme : Scheme
  hierPart : HierPart
  query : Option Query

def AbsoluteURI.render (u : AbsoluteURI) : List Char :=
  u.scheme.render ++ [':'] ++ u.hierPart.render ++
  (match u.query with
   | some q => '?' :: q.render
   | none => [])

/-- `relative-ref = relative-part [ "?" query ] [ "#" fragment ]` -/
structure RelativeRef where
  relPart : RelativePart
  query : Option Query
  fragment : Option Fragment

def RelativeRef.render (r : RelativeRef) : List Char :=
  r.relPart.render ++
  (match r.query with
   | some q => '?' :: q.render
   | none => []) ++
  (match r.fragment with
   | some f => '#' :: f.render
   | none => [])

/-- `URI-reference = URI / relative-ref` -/
inductive URIReference where
  | uri (u : URI)
  | relative (r : RelativeRef)

def URIReference.render : URIReference → List Char
  | .uri u => u.render
  | .relative r => r.render
