import UriRfc3986.Grammar

/-!
# §5.4 — Reference resolution examples, at spec level

The base URI of §5.4 and every example reference of §5.4.1 and §5.4.2,
represented as derivation trees of the Appendix A grammar, together with
the §5.4.1 target URIs as `URI` trees.

Each `*_render` theorem is the parse-membership check: it exhibits a
derivation tree and verifies by `decide` that the tree derives exactly
the example string. A string is in the language of a rule iff such a
tree exists, so these theorems are membership proofs for the examples.

Resolution itself — the §5.2 algorithm that maps a reference and a base
to its target — is a later milestone; the target strings of §5.4.1 are
included here as `URI` trees in their own right, not yet as values of a
resolution function.
-/

/-! ## Construction helpers

Small smart constructors so the trees below stay readable. These are
not part of the specification — every value they build is an ordinary
derivation tree, and the render theorems check the results. The class
proofs are discharged by `decide` at each use site. -/

/-- An unreserved `pchar` from a character. -/
def u (c : Char) (h : IsUnreserved c := by decide) : PChar :=
  .unreserved c h

/-- A sub-delims `pchar` from a character. -/
def sd (c : Char) (h : IsSubDelim c := by decide) : PChar :=
  .subDelims c h

/-- A percent-encoded `pchar` from its two hex digits. -/
def pct (a b : Char) (ha : IsHexDig a := by decide) (hb : IsHexDig b := by decide) :
    PChar :=
  .pctEncoded ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

/-- An unreserved `segment-nz-nc` character. -/
def nzu (c : Char) (h : IsUnreserved c := by decide) : SegNZNCChar :=
  .unreserved c h

/-- A sub-delims `segment-nz-nc` character. -/
def nzsd (c : Char) (h : IsSubDelim c := by decide) : SegNZNCChar :=
  .subDelims c h

/-! ## Segments that recur in §5.4 -/

/-- The segment `g`. -/
def segG : Segment := [u 'g']

/-- The segment `b`. -/
def segB : Segment := [u 'b']

/-- The segment `c`. -/
def segC : Segment := [u 'c']

/-- The segment `d;p`, from the §5.4 base URI. -/
def segDp : Segment := [u 'd', sd ';', u 'p']

/-- The segment `;x`. -/
def segSemiX : Segment := [sd ';', u 'x']

/-- The segment `g;x`. -/
def segGSemiX : Segment := [u 'g', sd ';', u 'x']

/-- The segment `.`. -/
def segDot : Segment := [u '.']

/-- The segment `..`. -/
def segDotDot : Segment := [u '.', u '.']

/-- The segment `h`. -/
def segH : Segment := [u 'h']

/-- The segment `y`. -/
def segY : Segment := [u 'y']

/-- The empty segment. -/
def segEmpty : Segment := []

/-- The non-colon segment `g`. -/
def nzG : SegmentNZNC := ⟨nzu 'g', []⟩

/-- The non-colon segment `.`. -/
def nzDot : SegmentNZNC := ⟨nzu '.', []⟩

/-- The non-colon segment `..`. -/
def nzDotDot : SegmentNZNC := ⟨nzu '.', [nzu '.']⟩

/-- The non-colon segment `;x`. -/
def nzSemiX : SegmentNZNC := ⟨nzsd ';', [nzu 'x']⟩

/-- The non-colon segment `g;x`. -/
def nzGSemiX : SegmentNZNC := ⟨nzu 'g', [nzsd ';', nzu 'x']⟩

/-- The non-colon segment `g;x=1`. (`=` is a sub-delim; `1` is unreserved,
being a digit.) -/
def nzGSemiXEq1 : SegmentNZNC := ⟨nzu 'g', [nzsd ';', nzu 'x', nzsd '=', nzu '1']⟩

/-- The nonempty segment `g`, as `pchar`s. -/
def nzSegG : SegmentNZ := ⟨u 'g', []⟩

/-- The nonempty segment `.`, as `pchar`s. -/
def nzSegDot : SegmentNZ := ⟨u '.', []⟩

/-- The nonempty segment `..`, as `pchar`s. -/
def nzSegDotDot : SegmentNZ := ⟨u '.', [u '.']⟩

/-! ## Recurring components -/

/-- The query `y`. -/
def qY : Query := [.pchar (u 'y')]

/-- The query `q`, from the §5.4 base URI. -/
def qQ : Query := [.pchar (u 'q')]

/-- The fragment `s`. -/
def fS : Fragment := [.pchar (u 's')]

/-- The scheme `g`. -/
def schemeG : Scheme := ⟨⟨'g', by decide⟩, []⟩

/-- The scheme `http`. -/
def schemeHttp : Scheme :=
  ⟨⟨'h', by decide⟩,
   [.alpha 't' (by decide), .alpha 't' (by decide), .alpha 'p' (by decide)]⟩

/-- The scheme `ftp`. -/
def schemeFtp : Scheme :=
  ⟨⟨'f', by decide⟩, [.alpha 't' (by decide), .alpha 'p' (by decide)]⟩

/-- The host `a`, as a reg-name. -/
def hostA : Host := .regName [.unreserved 'a' (by decide)]

/-- The host `g`, as a reg-name. -/
def hostG : Host := .regName [.unreserved 'g' (by decide)]

/-- The authority `a` (host only). -/
def authA : Authority := { userinfo := none, host := hostA, port := none }

/-- The authority `g` (host only). -/
def authG : Authority := { userinfo := none, host := hostG, port := none }

/-- A `URI` with scheme `http` and authority `a`, from a path, an optional
query and an optional fragment. -/
def httpURI (p : PathAbempty) (q : Option Query := none)
    (f : Option Fragment := none) : URI :=
  { scheme := schemeHttp, hierPart := .authority authA p, query := q, fragment := f }

/-- A relative reference from a non-scheme path, an optional query and an
optional fragment. -/
def relNoscheme (first : SegmentNZNC) (rest : List Segment)
    (q : Option Query := none) (f : Option Fragment := none) : URIReference :=
  .relative { relPart := .noscheme { first := first, rest := rest },
              query := q, fragment := f }

/-- A relative reference from an absolute path. -/
def relAbsolute (first : SegmentNZ) (rest : List Segment)
    (q : Option Query := none) (f : Option Fragment := none) : URIReference :=
  .relative { relPart := .absolute (.nonempty first rest), query := q, fragment := f }

/-- A relative reference with an empty relative part. -/
def relEmpty (q : Option Query := none) (f : Option Fragment := none) :
    URIReference :=
  .relative { relPart := .empty .mk, query := q, fragment := f }

/-- A relative reference with an authority part. -/
def relAuthority (a : Authority) (p : PathAbempty)
    (q : Option Query := none) (f : Option Fragment := none) : URIReference :=
  .relative { relPart := .authority a p, query := q, fragment := f }

/-! ## The §5.4 base URI -/

/-- The base URI of §5.4: `http://a/b/c/d;p?q`. -/
def base : URI := httpURI [segB, segC, segDp] (some qQ)

theorem base_render : base.render = "http://a/b/c/d;p?q".toList := by decide

/-! ## §5.4.1 normal examples — the references -/

/-- `g:h`, parsed as a URI (scheme `g`, rootless path `h`). -/
def uri_g_h : URI :=
  { scheme := schemeG,
    hierPart := .rootless { first := ⟨u 'h', []⟩, rest := [] },
    query := none, fragment := none }

theorem uri_g_h_render : uri_g_h.render = "g:h".toList := by decide

/-- The reference `g:h`, as a URI reference. -/
def ref_g_h : URIReference := .uri uri_g_h

theorem ref_g_h_render : ref_g_h.render = "g:h".toList := by decide

/-- The reference `g`. -/
def ref_g : URIReference := relNoscheme nzG []

theorem ref_g_render : ref_g.render = "g".toList := by decide

/-- The reference `./g`. -/
def ref_dot_g : URIReference := relNoscheme nzDot [segG]

theorem ref_dot_g_render : ref_dot_g.render = "./g".toList := by decide

/-- The reference `g/`. -/
def ref_g_slash : URIReference := relNoscheme nzG [segEmpty]

theorem ref_g_slash_render : ref_g_slash.render = "g/".toList := by decide

/-- The reference `/g`. -/
def ref_slash_g : URIReference := relAbsolute nzSegG []

theorem ref_slash_g_render : ref_slash_g.render = "/g".toList := by decide

/-- The reference `//g`. -/
def ref_slashslash_g : URIReference := relAuthority authG []

theorem ref_slashslash_g_render :
    ref_slashslash_g.render = "//g".toList := by decide

/-- The reference `?y`. -/
def ref_q_y : URIReference := relEmpty (some qY)

theorem ref_q_y_render : ref_q_y.render = "?y".toList := by decide

/-- The reference `g?y`. -/
def ref_g_q_y : URIReference := relNoscheme nzG [] (some qY)

theorem ref_g_q_y_render : ref_g_q_y.render = "g?y".toList := by decide

/-- The reference `#s`. -/
def ref_hash_s : URIReference := relEmpty none (some fS)

theorem ref_hash_s_render : ref_hash_s.render = "#s".toList := by decide

/-- The reference `g#s`. -/
def ref_g_hash_s : URIReference := relNoscheme nzG [] none (some fS)

theorem ref_g_hash_s_render : ref_g_hash_s.render = "g#s".toList := by decide

/-- The reference `g?y#s`. -/
def ref_g_qy_s : URIReference := relNoscheme nzG [] (some qY) (some fS)

theorem ref_g_qy_s_render : ref_g_qy_s.render = "g?y#s".toList := by decide

/-- The reference `;x`. -/
def ref_semi_x : URIReference := relNoscheme nzSemiX []

theorem ref_semi_x_render : ref_semi_x.render = ";x".toList := by decide

/-- The reference `g;x`. -/
def ref_g_semi_x : URIReference := relNoscheme nzGSemiX []

theorem ref_g_semi_x_render : ref_g_semi_x.render = "g;x".toList := by decide

/-- The reference `g;x?y#s`. -/
def ref_g_semi_x_qy_s : URIReference :=
  relNoscheme nzGSemiX [] (some qY) (some fS)

theorem ref_g_semi_x_qy_s_render :
    ref_g_semi_x_qy_s.render = "g;x?y#s".toList := by decide

/-- The empty reference ``. -/
def ref_empty : URIReference := relEmpty

theorem ref_empty_render : ref_empty.render = "".toList := by decide

/-- The reference `.`. -/
def ref_dot : URIReference := relNoscheme nzDot []

theorem ref_dot_render : ref_dot.render = ".".toList := by decide

/-- The reference `./`. -/
def ref_dot_slash : URIReference := relNoscheme nzDot [segEmpty]

theorem ref_dot_slash_render : ref_dot_slash.render = "./".toList := by decide

/-- The reference `..`. -/
def ref_dotdot : URIReference := relNoscheme nzDotDot []

theorem ref_dotdot_render : ref_dotdot.render = "..".toList := by decide

/-- The reference `../`. -/
def ref_dotdot_slash : URIReference := relNoscheme nzDotDot [segEmpty]

theorem ref_dotdot_slash_render :
    ref_dotdot_slash.render = "../".toList := by decide

/-- The reference `../g`. -/
def ref_dotdot_g : URIReference := relNoscheme nzDotDot [segG]

theorem ref_dotdot_g_render : ref_dotdot_g.render = "../g".toList := by decide

/-- The reference `../..`. -/
def ref_dotdot_dotdot : URIReference := relNoscheme nzDotDot [segDotDot]

theorem ref_dotdot_dotdot_render :
    ref_dotdot_dotdot.render = "../..".toList := by decide

/-- The reference `../../`. -/
def ref_dd_dd_slash : URIReference := relNoscheme nzDotDot [segDotDot, segEmpty]

theorem ref_dd_dd_slash_render :
    ref_dd_dd_slash.render = "../../".toList := by decide

/-- The reference `../../g`. -/
def ref_dd_dd_g : URIReference := relNoscheme nzDotDot [segDotDot, segG]

theorem ref_dd_dd_g_render : ref_dd_dd_g.render = "../../g".toList := by decide

/-! ## §5.4.1 normal examples — the target URIs

Each target string of §5.4.1 as a `URI` tree. The assertion that these
are the targets *of the references above, against `base`* is the
resolution theorem of a later milestone; here each target is checked as
a URI in its own right. -/

/-- Target of `g`: `http://a/b/c/g` (also of `./g`). -/
def tgt_bcg : URI := httpURI [segB, segC, segG]

theorem tgt_bcg_render : tgt_bcg.render = "http://a/b/c/g".toList := by decide

/-- Target of `g/`: `http://a/b/c/g/`. -/
def tgt_bcg_slash : URI := httpURI [segB, segC, segG, segEmpty]

theorem tgt_bcg_slash_render :
    tgt_bcg_slash.render = "http://a/b/c/g/".toList := by decide

/-- Target of `/g`: `http://a/g` (also of `../../g`). -/
def tgt_ag : URI := httpURI [segG]

theorem tgt_ag_render : tgt_ag.render = "http://a/g".toList := by decide

/-- Target of `//g`: `http://g` — authority `g`, empty path. -/
def tgt_g : URI :=
  { scheme := schemeHttp, hierPart := .authority authG [],
    query := none, fragment := none }

theorem tgt_g_render : tgt_g.render = "http://g".toList := by decide

/-- Target of `?y`: `http://a/b/c/d;p?y`. -/
def tgt_base_qy : URI := httpURI [segB, segC, segDp] (some qY)

theorem tgt_base_qy_render :
    tgt_base_qy.render = "http://a/b/c/d;p?y".toList := by decide

/-- Target of `g?y`: `http://a/b/c/g?y`. -/
def tgt_bcg_qy : URI := httpURI [segB, segC, segG] (some qY)

theorem tgt_bcg_qy_render :
    tgt_bcg_qy.render = "http://a/b/c/g?y".toList := by decide

/-- Target of `#s`: `http://a/b/c/d;p?q#s`. -/
def tgt_base_q_s : URI := httpURI [segB, segC, segDp] (some qQ) (some fS)

theorem tgt_base_q_s_render :
    tgt_base_q_s.render = "http://a/b/c/d;p?q#s".toList := by decide

/-- Target of `g#s`: `http://a/b/c/g#s`. -/
def tgt_bcg_s : URI := httpURI [segB, segC, segG] none (some fS)

theorem tgt_bcg_s_render :
    tgt_bcg_s.render = "http://a/b/c/g#s".toList := by decide

/-- Target of `g?y#s`: `http://a/b/c/g?y#s`. -/
def tgt_bcg_qy_s : URI := httpURI [segB, segC, segG] (some qY) (some fS)

theorem tgt_bcg_qy_s_render :
    tgt_bcg_qy_s.render = "http://a/b/c/g?y#s".toList := by decide

/-- Target of `;x`: `http://a/b/c/;x`. -/
def tgt_bc_semi_x : URI := httpURI [segB, segC, segSemiX]

theorem tgt_bc_semi_x_render :
    tgt_bc_semi_x.render = "http://a/b/c/;x".toList := by decide

/-- Target of `g;x`: `http://a/b/c/g;x`. -/
def tgt_bcg_semi_x : URI := httpURI [segB, segC, segGSemiX]

theorem tgt_bcg_semi_x_render :
    tgt_bcg_semi_x.render = "http://a/b/c/g;x".toList := by decide

/-- Target of `g;x?y#s`: `http://a/b/c/g;x?y#s`. -/
def tgt_bcg_semi_x_qy_s : URI := httpURI [segB, segC, segGSemiX] (some qY) (some fS)

theorem tgt_bcg_semi_x_qy_s_render :
    tgt_bcg_semi_x_qy_s.render = "http://a/b/c/g;x?y#s".toList := by decide

/-- Target of `.` and of `./`: `http://a/b/c/`. -/
def tgt_bc_slash : URI := httpURI [segB, segC, segEmpty]

theorem tgt_bc_slash_render :
    tgt_bc_slash.render = "http://a/b/c/".toList := by decide

/-- Target of `..` and of `../`: `http://a/b/`. -/
def tgt_b_slash : URI := httpURI [segB, segEmpty]

theorem tgt_b_slash_render :
    tgt_b_slash.render = "http://a/b/".toList := by decide

/-- Target of `../g`: `http://a/b/g`. -/
def tgt_bg : URI := httpURI [segB, segG]

theorem tgt_bg_render : tgt_bg.render = "http://a/b/g".toList := by decide

/-- Target of `../..` and of `../../`: `http://a/`. -/
def tgt_a_slash : URI := httpURI [segEmpty]

theorem tgt_a_slash_render :
    tgt_a_slash.render = "http://a/".toList := by decide

/-! ## §5.4.2 abnormal examples — the references

All of these are syntactically valid references; what is "abnormal"
about them is only how resolution treats them. They are represented
here, as in §5.4.1, as reference trees with `decide`-checked renders.
Their target strings are not listed separately: several coincide with
§5.4.1 targets (e.g. `../../../g` also resolves to `http://a/g`), and
the reference-to-target correspondence belongs to the resolution
milestone. -/

/-- The reference `../../../g`. -/
def ref_ddd_g : URIReference := relNoscheme nzDotDot [segDotDot, segDotDot, segG]

theorem ref_ddd_g_render : ref_ddd_g.render = "../../../g".toList := by decide

/-- The reference `../../../../g`. -/
def ref_dddd_g : URIReference :=
  relNoscheme nzDotDot [segDotDot, segDotDot, segDotDot, segG]

theorem ref_dddd_g_render :
    ref_dddd_g.render = "../../../../g".toList := by decide

/-- The reference `/./g`. -/
def ref_slash_dot_g : URIReference := relAbsolute nzSegDot [segG]

theorem ref_slash_dot_g_render :
    ref_slash_dot_g.render = "/./g".toList := by decide

/-- The reference `/../g`. -/
def ref_slash_dotdot_g : URIReference := relAbsolute nzSegDotDot [segG]

theorem ref_slash_dotdot_g_render :
    ref_slash_dotdot_g.render = "/../g".toList := by decide

/-- The reference `g.`. -/
def ref_g_dot : URIReference := relNoscheme ⟨nzu 'g', [nzu '.']⟩ []

theorem ref_g_dot_render : ref_g_dot.render = "g.".toList := by decide

/-- The reference `.g`. -/
def ref_dot_g2 : URIReference := relNoscheme ⟨nzu '.', [nzu 'g']⟩ []

theorem ref_dot_g2_render : ref_dot_g2.render = ".g".toList := by decide

/-- The reference `g..`. -/
def ref_g_dotdot : URIReference := relNoscheme ⟨nzu 'g', [nzu '.', nzu '.']⟩ []

theorem ref_g_dotdot_render : ref_g_dotdot.render = "g..".toList := by decide

/-- The reference `..g`. -/
def ref_dotdot_g2 : URIReference :=
  relNoscheme ⟨nzu '.', [nzu '.', nzu 'g']⟩ []

theorem ref_dotdot_g2_render : ref_dotdot_g2.render = "..g".toList := by decide

/-- The reference `./../g`. -/
def ref_dot_slashdot_g : URIReference := relNoscheme nzDot [segDotDot, segG]

theorem ref_dot_slashdot_g_render :
    ref_dot_slashdot_g.render = "./../g".toList := by decide

/-- The reference `./g/.`. -/
def ref_dot_g_dot : URIReference := relNoscheme nzDot [segG, segDot]

theorem ref_dot_g_dot_render :
    ref_dot_g_dot.render = "./g/.".toList := by decide

/-- The reference `g/./h`. -/
def ref_g_slash_dot_h : URIReference := relNoscheme nzG [segDot, segH]

theorem ref_g_slash_dot_h_render :
    ref_g_slash_dot_h.render = "g/./h".toList := by decide

/-- The reference `g/../h`. -/
def ref_g_slash_dotdot_h : URIReference := relNoscheme nzG [segDotDot, segH]

theorem ref_g_slash_dotdot_h_render :
    ref_g_slash_dotdot_h.render = "g/../h".toList := by decide

/-- The reference `g;x=1/./y`. -/
def ref_gx1_dot_y : URIReference := relNoscheme nzGSemiXEq1 [segDot, segY]

theorem ref_gx1_dot_y_render :
    ref_gx1_dot_y.render = "g;x=1/./y".toList := by decide

/-- The reference `g;x=1/../y`. -/
def ref_gx1_dotdot_y : URIReference := relNoscheme nzGSemiXEq1 [segDotDot, segY]

theorem ref_gx1_dotdot_y_render :
    ref_gx1_dotdot_y.render = "g;x=1/../y".toList := by decide

/-- The reference `g?y/./x` — the dot segments are in the *query*, where
resolution must not touch them. -/
def ref_g_q_y_dot_x : URIReference :=
  relNoscheme nzG []
    (some [.pchar (u 'y'), .slash, .pchar (u '.'), .slash, .pchar (u 'x')])

theorem ref_g_q_y_dot_x_render :
    ref_g_q_y_dot_x.render = "g?y/./x".toList := by decide

/-- The reference `g?y/../x`. -/
def ref_g_q_y_dotdot_x : URIReference :=
  relNoscheme nzG []
    (some [.pchar (u 'y'), .slash, .pchar (u '.'), .pchar (u '.'), .slash,
           .pchar (u 'x')])

theorem ref_g_q_y_dotdot_x_render :
    ref_g_q_y_dotdot_x.render = "g?y/../x".toList := by decide

/-- The reference `g#s/./x` — dot segments in the *fragment*. -/
def ref_g_f_s_dot_x : URIReference :=
  relNoscheme nzG [] none
    (some [.pchar (u 's'), .slash, .pchar (u '.'), .slash, .pchar (u 'x')])

theorem ref_g_f_s_dot_x_render :
    ref_g_f_s_dot_x.render = "g#s/./x".toList := by decide

/-- The reference `g#s/../x`. -/
def ref_g_f_s_dotdot_x : URIReference :=
  relNoscheme nzG [] none
    (some [.pchar (u 's'), .slash, .pchar (u '.'), .pchar (u '.'), .slash,
           .pchar (u 'x')])

theorem ref_g_f_s_dotdot_x_render :
    ref_g_f_s_dotdot_x.render = "g#s/../x".toList := by decide

/-- The reference `http:g`, as a strict parser reads it: a URI with
scheme `http` and rootless path `g`. -/
def uri_http_g : URI :=
  { scheme := schemeHttp,
    hierPart := .rootless { first := ⟨u 'g', []⟩, rest := [] },
    query := none, fragment := none }

theorem uri_http_g_render : uri_http_g.render = "http:g".toList := by decide

/-- The reference `http:g`, as a URI reference. -/
def ref_http_g : URIReference := .uri uri_http_g

theorem ref_http_g_render : ref_http_g.render = "http:g".toList := by decide

/-! ## Host coverage beyond §5.4

§5.4 exercises only reg-name hosts. The trees below check the remaining
`host` alternatives — IPv4, IP-literal over IPv6 (compressed and full),
and a `userinfo`-bearing authority — plus a port and a percent-encoded
segment, so that every `host` constructor and the port option are
covered by at least one `decide`-checked example. -/

/-- The length of a one-digit list is one, definitionally. -/
theorem hexDigSingleton_length (d : HexDigChar) : [d].length = 1 := rfl

/-- An `h16` from a single hex digit. -/
def h16Of (c : Char) (h : IsHexDig c := by decide) : H16 :=
  ⟨[⟨c, h⟩],
   by rw [hexDigSingleton_length]; decide,
   by rw [hexDigSingleton_length]; decide⟩

/-- The `h16` `2001`. -/
def h16_2001 : H16 :=
  ⟨[⟨'2', by decide⟩, ⟨'0', by decide⟩, ⟨'0', by decide⟩, ⟨'1', by decide⟩],
   by decide, by decide⟩

/-- The `h16` `db8`. -/
def h16_db8 : H16 :=
  ⟨[⟨'d', by decide⟩, ⟨'b', by decide⟩, ⟨'8', by decide⟩], by decide, by decide⟩

/-- `2001:db8::1` — IPv6 alternative 8, `[ *5( h16 ":" ) h16 ] "::" h16`,
with a one-group prefix. -/
def ipv6_2001_db8_1 : IPv6Address :=
  .compressed6 (some { groups := [h16_2001], last := h16_db8, hlen := by decide })
    (h16Of '1')

theorem ipv6_2001_db8_1_render :
    ipv6_2001_db8_1.render = "2001:db8::1".toList := by decide

/-- `1:2:3:4:5:6:7:8` — IPv6 alternative 1, `6( h16 ":" ) ls32` with an
`h16 ":" h16` tail. -/
def ipv6_full : IPv6Address :=
  .full { groups := [h16Of '1', h16Of '2', h16Of '3', h16Of '4', h16Of '5',
                     h16Of '6'],
          hlen := by decide }
    (.h16Pair (h16Of '7') (h16Of '8'))

theorem ipv6_full_render :
    ipv6_full.render = "1:2:3:4:5:6:7:8".toList := by decide

/-- `::` — IPv6 alternative 9 with an absent prefix: the shortest address. -/
def ipv6_unspecified : IPv6Address := .compressed7 none

theorem ipv6_unspecified_render :
    ipv6_unspecified.render = "::".toList := by decide

/-- The host `192.168.0.1`, an IPv4 address. Its octets exercise three of
the five `dec-octet` alternatives: `"1" 2DIGIT` (192, 168), `DIGIT` (0),
and `DIGIT` (1). -/
def hostIPv4 : Host :=
  .ipv4 { o₁ := .oneHundred '9' '2' (by decide) (by decide),
          o₂ := .oneHundred '6' '8' (by decide) (by decide),
          o₃ := .single '0' (by decide),
          o₄ := .single '1' (by decide) }

theorem hostIPv4_render : hostIPv4.render = "192.168.0.1".toList := by decide

/-- `http://192.168.0.1:8080/p?q#f` — IPv4 host, a present port, and all
five components defined. -/
def uri_ipv4 : URI :=
  { scheme := schemeHttp,
    hierPart := .authority
      { userinfo := none, host := hostIPv4,
        port := some [⟨'8', by decide⟩, ⟨'0', by decide⟩, ⟨'8', by decide⟩,
                      ⟨'0', by decide⟩] }
      [[u 'p']],
    query := some [.pchar (u 'q')],
    fragment := some [.pchar (u 'f')] }

theorem uri_ipv4_render :
    uri_ipv4.render = "http://192.168.0.1:8080/p?q#f".toList := by decide

/-- `http://[2001:db8::1]/x` — an IP-literal host. -/
def uri_ipv6 : URI :=
  { scheme := schemeHttp,
    hierPart := .authority
      { userinfo := none, host := .ipLiteral (.ipv6 ipv6_2001_db8_1),
        port := none }
      [[u 'x']],
    query := none, fragment := none }

theorem uri_ipv6_render :
    uri_ipv6.render = "http://[2001:db8::1]/x".toList := by decide

/-- `ftp://user@example.com/` — a userinfo-bearing authority and a
dotted reg-name, with a trailing empty segment. -/
def uri_userinfo : URI :=
  { scheme := schemeFtp,
    hierPart := .authority
      { userinfo := some [.unreserved 'u' (by decide),
                          .unreserved 's' (by decide),
                          .unreserved 'e' (by decide),
                          .unreserved 'r' (by decide)],
        host := .regName
          [.unreserved 'e' (by decide), .unreserved 'x' (by decide),
           .unreserved 'a' (by decide), .unreserved 'm' (by decide),
           .unreserved 'p' (by decide), .unreserved 'l' (by decide),
           .unreserved 'e' (by decide), .unreserved '.' (by decide),
           .unreserved 'c' (by decide), .unreserved 'o' (by decide),
           .unreserved 'm' (by decide)],
        port := none }
      [segEmpty],
    query := none, fragment := none }

theorem uri_userinfo_render :
    uri_userinfo.render = "ftp://user@example.com/".toList := by decide

/-- `http://a/%7Euser` — a percent-encoded segment. -/
def uri_pct : URI := httpURI [[pct '7' 'E', u 'u', u 's', u 'e', u 'r']]

theorem uri_pct_render :
    uri_pct.render = "http://a/%7Euser".toList := by decide
