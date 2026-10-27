import UriRfc3986.Resolve

/-!
# RFC 3986 §5.4 as resolution theorems

Every row of §5.4 is checked at both the component and recomposed-string
levels, in the order of dossier v2 §4. The two readings of `http:g` give
43 assertions for the RFC's 42 references. These are kernel `decide`
proofs over the §5.2 functions and the Appendix A derivation trees.

The 40 relative references (#2–#41) fall under `targetRelOfAuthority`.
The scheme-bearing Branch-1 cases #1 and #42 strict require the guarded
`target` directly; they do not instantiate that relative-reference corollary.

RFC §5.2.2: "T.path      = remove_dot_segments(R.path);"
RFC §5.2.2: "T.fragment = R.fragment;"
-/

/-! ## Twelve additional §5.4.2 target trees -/

/-- Target tree for §5.4.2's `http://a/b/c/g.`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_dot : URI := httpURI [segB, segC, [u 'g', u '.']]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_dot_render :
    tgt_bcg_dot.render = "http://a/b/c/g.".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/.g`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bc_dot_g : URI := httpURI [segB, segC, [u '.', u 'g']]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bc_dot_g_render :
    tgt_bc_dot_g.render = "http://a/b/c/.g".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g..`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_dotdot : URI := httpURI [segB, segC, [u 'g', u '.', u '.']]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_dotdot_render :
    tgt_bcg_dotdot.render = "http://a/b/c/g..".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/..g`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bc_dotdot_g : URI := httpURI [segB, segC, [u '.', u '.', u 'g']]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bc_dotdot_g_render :
    tgt_bc_dotdot_g.render = "http://a/b/c/..g".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g/h`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcgh : URI := httpURI [segB, segC, segG, segH]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcgh_render :
    tgt_bcgh.render = "http://a/b/c/g/h".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/h`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bch : URI := httpURI [segB, segC, segH]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bch_render :
    tgt_bch.render = "http://a/b/c/h".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g;x=1/y`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcgx1_y : URI := httpURI [segB, segC, [u 'g', sd ';', u 'x', sd '=', u '1'], segY]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcgx1_y_render :
    tgt_bcgx1_y.render = "http://a/b/c/g;x=1/y".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/y`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcy : URI := httpURI [segB, segC, segY]

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcy_render :
    tgt_bcy.render = "http://a/b/c/y".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g?y/./x`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_q_y_dot_x : URI := httpURI [segB, segC, segG]
  (some [.pchar (u 'y'), .slash, .pchar (u '.'), .slash, .pchar (u 'x')])

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_q_y_dot_x_render :
    tgt_bcg_q_y_dot_x.render = "http://a/b/c/g?y/./x".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g?y/../x`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_q_y_dotdot_x : URI := httpURI [segB, segC, segG]
  (some [.pchar (u 'y'), .slash, .pchar (u '.'), .pchar (u '.'), .slash,
         .pchar (u 'x')])

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_q_y_dotdot_x_render :
    tgt_bcg_q_y_dotdot_x.render = "http://a/b/c/g?y/../x".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g#s/./x`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_f_s_dot_x : URI := httpURI [segB, segC, segG] none
  (some [.pchar (u 's'), .slash, .pchar (u '.'), .slash, .pchar (u 'x')])

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_f_s_dot_x_render :
    tgt_bcg_f_s_dot_x.render = "http://a/b/c/g#s/./x".toList := by decide

/-- Target tree for §5.4.2's `http://a/b/c/g#s/../x`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def tgt_bcg_f_s_dotdot_x : URI := httpURI [segB, segC, segG] none
  (some [.pchar (u 's'), .slash, .pchar (u '.'), .pchar (u '.'), .slash,
         .pchar (u 'x')])

/-- Target-tree rendering for §5.4.2; RFC §5.2.2:
"T.path      = remove_dot_segments(R.path);" -/
theorem tgt_bcg_f_s_dotdot_x_render :
    tgt_bcg_f_s_dotdot_x.render = "http://a/b/c/g#s/../x".toList := by decide

/-! ## All §5.4 resolution assertions, in RFC order -/

/-- §5.4.1 #01: `"g:h" = "g:h"`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);"
Branch 1; remove-dot-segments input `h`; rules E (identity). -/
theorem ex01_g_h :
    transformReferences true base.components ref_g_h.components =
      uri_g_h.components := by decide

/-- §5.4.1 #01 recomposed target.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
theorem ex01_g_h_str :
    recompose (transformReferences true base.components ref_g_h.components) =
      "g:h".toList := by decide

/-- §5.4.1 #02: `"g" = "http://a/b/c/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (identity). -/
theorem ex02_g :
    transformReferences true base.components ref_g.components =
      tgt_bcg.components := by decide

/-- §5.4.1 #02 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex02_g_str :
    recompose (transformReferences true base.components ref_g.components) =
      "http://a/b/c/g".toList := by decide

/-- §5.4.1 #03: `"./g" = "http://a/b/c/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/./g`; rules EEBE. -/
theorem ex03_dot_g :
    transformReferences true base.components ref_dot_g.components =
      tgt_bcg.components := by decide

/-- §5.4.1 #03 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex03_dot_g_str :
    recompose (transformReferences true base.components ref_dot_g.components) =
      "http://a/b/c/g".toList := by decide

/-- §5.4.1 #04: `"g/" = "http://a/b/c/g/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g/`; rules EEEE (identity). -/
theorem ex04_g_slash :
    transformReferences true base.components ref_g_slash.components =
      tgt_bcg_slash.components := by decide

/-- §5.4.1 #04 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex04_g_slash_str :
    recompose (transformReferences true base.components ref_g_slash.components) =
      "http://a/b/c/g/".toList := by decide

/-- §5.4.1 #05: `"/g" = "http://a/g"`.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);"
Branch 4; remove-dot-segments input `/g`; rules E (identity). -/
theorem ex05_slash_g :
    transformReferences true base.components ref_slash_g.components =
      tgt_ag.components := by decide

/-- §5.4.1 #05 recomposed target.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);" -/
theorem ex05_slash_g_str :
    recompose (transformReferences true base.components ref_slash_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.1 #06: `"//g" = "http://g"`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);"
Branch 2; remove-dot-segments input ``; rules none (empty input). -/
theorem ex06_slashslash_g :
    transformReferences true base.components ref_slashslash_g.components =
      tgt_g.components := by decide

/-- §5.4.1 #06 recomposed target.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
theorem ex06_slashslash_g_str :
    recompose (transformReferences true base.components ref_slashslash_g.components) =
      "http://g".toList := by decide

/-- §5.4.1 #07: `"?y" = "http://a/b/c/d;p?y"`.
RFC §5.2.2: "T.path = Base.path;"
Branch 3; remove-dot-segments input not invoked; rules no removal: base path reused. -/
theorem ex07_q_y :
    transformReferences true base.components ref_q_y.components =
      tgt_base_qy.components := by decide

/-- §5.4.1 #07 recomposed target.
RFC §5.2.2: "T.path = Base.path;" -/
theorem ex07_q_y_str :
    recompose (transformReferences true base.components ref_q_y.components) =
      "http://a/b/c/d;p?y".toList := by decide

/-- §5.4.1 #08: `"g?y" = "http://a/b/c/g?y"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE. -/
theorem ex08_g_q_y :
    transformReferences true base.components ref_g_q_y.components =
      tgt_bcg_qy.components := by decide

/-- §5.4.1 #08 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex08_g_q_y_str :
    recompose (transformReferences true base.components ref_g_q_y.components) =
      "http://a/b/c/g?y".toList := by decide

/-- §5.4.1 #09: `"#s" = "http://a/b/c/d;p?q#s"`.
RFC §5.2.2: "T.path = Base.path;"
Branch 3; remove-dot-segments input not invoked; rules no removal: base path reused. -/
theorem ex09_hash_s :
    transformReferences true base.components ref_hash_s.components =
      tgt_base_q_s.components := by decide

/-- §5.4.1 #09 recomposed target.
RFC §5.2.2: "T.path = Base.path;" -/
theorem ex09_hash_s_str :
    recompose (transformReferences true base.components ref_hash_s.components) =
      "http://a/b/c/d;p?q#s".toList := by decide

/-- §5.4.1 #10: `"g#s" = "http://a/b/c/g#s"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE. -/
theorem ex10_g_hash_s :
    transformReferences true base.components ref_g_hash_s.components =
      tgt_bcg_s.components := by decide

/-- §5.4.1 #10 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex10_g_hash_s_str :
    recompose (transformReferences true base.components ref_g_hash_s.components) =
      "http://a/b/c/g#s".toList := by decide

/-- §5.4.1 #11: `"g?y#s" = "http://a/b/c/g?y#s"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE. -/
theorem ex11_g_qy_s :
    transformReferences true base.components ref_g_qy_s.components =
      tgt_bcg_qy_s.components := by decide

/-- §5.4.1 #11 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex11_g_qy_s_str :
    recompose (transformReferences true base.components ref_g_qy_s.components) =
      "http://a/b/c/g?y#s".toList := by decide

/-- §5.4.1 #12: `";x" = "http://a/b/c/;x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/;x`; rules EEE. -/
theorem ex12_semi_x :
    transformReferences true base.components ref_semi_x.components =
      tgt_bc_semi_x.components := by decide

/-- §5.4.1 #12 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex12_semi_x_str :
    recompose (transformReferences true base.components ref_semi_x.components) =
      "http://a/b/c/;x".toList := by decide

/-- §5.4.1 #13: `"g;x" = "http://a/b/c/g;x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g;x`; rules EEE. -/
theorem ex13_g_semi_x :
    transformReferences true base.components ref_g_semi_x.components =
      tgt_bcg_semi_x.components := by decide

/-- §5.4.1 #13 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex13_g_semi_x_str :
    recompose (transformReferences true base.components ref_g_semi_x.components) =
      "http://a/b/c/g;x".toList := by decide

/-- §5.4.1 #14: `"g;x?y#s" = "http://a/b/c/g;x?y#s"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g;x`; rules EEE. -/
theorem ex14_g_semi_x_qy_s :
    transformReferences true base.components ref_g_semi_x_qy_s.components =
      tgt_bcg_semi_x_qy_s.components := by decide

/-- §5.4.1 #14 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex14_g_semi_x_qy_s_str :
    recompose (transformReferences true base.components ref_g_semi_x_qy_s.components) =
      "http://a/b/c/g;x?y#s".toList := by decide

/-- §5.4.1 #15: `"" = "http://a/b/c/d;p?q"`.
RFC §5.2.2: "T.path = Base.path;"
Branch 3; remove-dot-segments input not invoked; rules no removal: base path and query reused. -/
theorem ex15_empty :
    transformReferences true base.components ref_empty.components =
      base.components := by decide

/-- §5.4.1 #15 recomposed target.
RFC §5.2.2: "T.path = Base.path;" -/
theorem ex15_empty_str :
    recompose (transformReferences true base.components ref_empty.components) =
      "http://a/b/c/d;p?q".toList := by decide

/-- §5.4.1 #16: `"." = "http://a/b/c/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/.`; rules EEBE. -/
theorem ex16_dot :
    transformReferences true base.components ref_dot.components =
      tgt_bc_slash.components := by decide

/-- §5.4.1 #16 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex16_dot_str :
    recompose (transformReferences true base.components ref_dot.components) =
      "http://a/b/c/".toList := by decide

/-- §5.4.1 #17: `"./" = "http://a/b/c/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/./`; rules EEBE. -/
theorem ex17_dot_slash :
    transformReferences true base.components ref_dot_slash.components =
      tgt_bc_slash.components := by decide

/-- §5.4.1 #17 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex17_dot_slash_str :
    recompose (transformReferences true base.components ref_dot_slash.components) =
      "http://a/b/c/".toList := by decide

/-- §5.4.1 #18: `".." = "http://a/b/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/..`; rules EECE. -/
theorem ex18_dotdot :
    transformReferences true base.components ref_dotdot.components =
      tgt_b_slash.components := by decide

/-- §5.4.1 #18 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex18_dotdot_str :
    recompose (transformReferences true base.components ref_dotdot.components) =
      "http://a/b/".toList := by decide

/-- §5.4.1 #19: `"../" = "http://a/b/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../`; rules EECE. -/
theorem ex19_dotdot_slash :
    transformReferences true base.components ref_dotdot_slash.components =
      tgt_b_slash.components := by decide

/-- §5.4.1 #19 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex19_dotdot_slash_str :
    recompose (transformReferences true base.components ref_dotdot_slash.components) =
      "http://a/b/".toList := by decide

/-- §5.4.1 #20: `"../g" = "http://a/b/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../g`; rules EECE. -/
theorem ex20_dotdot_g :
    transformReferences true base.components ref_dotdot_g.components =
      tgt_bg.components := by decide

/-- §5.4.1 #20 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex20_dotdot_g_str :
    recompose (transformReferences true base.components ref_dotdot_g.components) =
      "http://a/b/g".toList := by decide

/-- §5.4.1 #21: `"../.." = "http://a/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../..`; rules EECCE. -/
theorem ex21_dotdot_dotdot :
    transformReferences true base.components ref_dotdot_dotdot.components =
      tgt_a_slash.components := by decide

/-- §5.4.1 #21 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex21_dotdot_dotdot_str :
    recompose (transformReferences true base.components ref_dotdot_dotdot.components) =
      "http://a/".toList := by decide

/-- §5.4.1 #22: `"../../" = "http://a/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../../`; rules EECCE. -/
theorem ex22_dd_dd_slash :
    transformReferences true base.components ref_dd_dd_slash.components =
      tgt_a_slash.components := by decide

/-- §5.4.1 #22 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex22_dd_dd_slash_str :
    recompose (transformReferences true base.components ref_dd_dd_slash.components) =
      "http://a/".toList := by decide

/-- §5.4.1 #23: `"../../g" = "http://a/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../../g`; rules EECCE. -/
theorem ex23_dd_dd_g :
    transformReferences true base.components ref_dd_dd_g.components =
      tgt_ag.components := by decide

/-- §5.4.1 #23 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex23_dd_dd_g_str :
    recompose (transformReferences true base.components ref_dd_dd_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.2 #24: `"../../../g" = "http://a/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../../../g`; rules EECCCE (beyond-root clamp). -/
theorem ex24_ddd_g :
    transformReferences true base.components ref_ddd_g.components =
      tgt_ag.components := by decide

/-- §5.4.2 #24 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex24_ddd_g_str :
    recompose (transformReferences true base.components ref_ddd_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.2 #25: `"../../../../g" = "http://a/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/../../../../g`; rules EECCCCE (beyond-root clamp). -/
theorem ex25_dddd_g :
    transformReferences true base.components ref_dddd_g.components =
      tgt_ag.components := by decide

/-- §5.4.2 #25 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex25_dddd_g_str :
    recompose (transformReferences true base.components ref_dddd_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.2 #26: `"/./g" = "http://a/g"`.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);"
Branch 4; remove-dot-segments input `/./g`; rules BE. -/
theorem ex26_slash_dot_g :
    transformReferences true base.components ref_slash_dot_g.components =
      tgt_ag.components := by decide

/-- §5.4.2 #26 recomposed target.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);" -/
theorem ex26_slash_dot_g_str :
    recompose (transformReferences true base.components ref_slash_dot_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.2 #27: `"/../g" = "http://a/g"`.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);"
Branch 4; remove-dot-segments input `/../g`; rules CE. -/
theorem ex27_slash_dotdot_g :
    transformReferences true base.components ref_slash_dotdot_g.components =
      tgt_ag.components := by decide

/-- §5.4.2 #27 recomposed target.
RFC §5.2.2: "T.path = remove_dot_segments(R.path);" -/
theorem ex27_slash_dotdot_g_str :
    recompose (transformReferences true base.components ref_slash_dotdot_g.components) =
      "http://a/g".toList := by decide

/-- §5.4.2 #28: `"g." = "http://a/b/c/g."`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g.`; rules EEE (identity: dot is not a complete segment). -/
theorem ex28_g_dot :
    transformReferences true base.components ref_g_dot.components =
      tgt_bcg_dot.components := by decide

/-- §5.4.2 #28 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex28_g_dot_str :
    recompose (transformReferences true base.components ref_g_dot.components) =
      "http://a/b/c/g.".toList := by decide

/-- §5.4.2 #29: `".g" = "http://a/b/c/.g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/.g`; rules EEE (identity). -/
theorem ex29_dot_g :
    transformReferences true base.components ref_dot_g2.components =
      tgt_bc_dot_g.components := by decide

/-- §5.4.2 #29 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex29_dot_g_str :
    recompose (transformReferences true base.components ref_dot_g2.components) =
      "http://a/b/c/.g".toList := by decide

/-- §5.4.2 #30: `"g.." = "http://a/b/c/g.."`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g..`; rules EEE (identity). -/
theorem ex30_g_dotdot :
    transformReferences true base.components ref_g_dotdot.components =
      tgt_bcg_dotdot.components := by decide

/-- §5.4.2 #30 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex30_g_dotdot_str :
    recompose (transformReferences true base.components ref_g_dotdot.components) =
      "http://a/b/c/g..".toList := by decide

/-- §5.4.2 #31: `"..g" = "http://a/b/c/..g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/..g`; rules EEE (identity). -/
theorem ex31_dotdot_g :
    transformReferences true base.components ref_dotdot_g2.components =
      tgt_bc_dotdot_g.components := by decide

/-- §5.4.2 #31 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex31_dotdot_g_str :
    recompose (transformReferences true base.components ref_dotdot_g2.components) =
      "http://a/b/c/..g".toList := by decide

/-- §5.4.2 #32: `"./../g" = "http://a/b/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/./../g`; rules EEBCE. -/
theorem ex32_dot_slashdot_g :
    transformReferences true base.components ref_dot_slashdot_g.components =
      tgt_bg.components := by decide

/-- §5.4.2 #32 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex32_dot_slashdot_g_str :
    recompose (transformReferences true base.components ref_dot_slashdot_g.components) =
      "http://a/b/g".toList := by decide

/-- §5.4.2 #33: `"./g/." = "http://a/b/c/g/"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/./g/.`; rules EEBEBE. -/
theorem ex33_dot_g_dot :
    transformReferences true base.components ref_dot_g_dot.components =
      tgt_bcg_slash.components := by decide

/-- §5.4.2 #33 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex33_dot_g_dot_str :
    recompose (transformReferences true base.components ref_dot_g_dot.components) =
      "http://a/b/c/g/".toList := by decide

/-- §5.4.2 #34: `"g/./h" = "http://a/b/c/g/h"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g/./h`; rules EEEBE. -/
theorem ex34_g_slash_dot_h :
    transformReferences true base.components ref_g_slash_dot_h.components =
      tgt_bcgh.components := by decide

/-- §5.4.2 #34 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex34_g_slash_dot_h_str :
    recompose (transformReferences true base.components ref_g_slash_dot_h.components) =
      "http://a/b/c/g/h".toList := by decide

/-- §5.4.2 #35: `"g/../h" = "http://a/b/c/h"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g/../h`; rules EEECE (E/C interaction). -/
theorem ex35_g_slash_dotdot_h :
    transformReferences true base.components ref_g_slash_dotdot_h.components =
      tgt_bch.components := by decide

/-- §5.4.2 #35 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex35_g_slash_dotdot_h_str :
    recompose (transformReferences true base.components ref_g_slash_dotdot_h.components) =
      "http://a/b/c/h".toList := by decide

/-- §5.4.2 #36: `"g;x=1/./y" = "http://a/b/c/g;x=1/y"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g;x=1/./y`; rules EEEBE. -/
theorem ex36_gx1_dot_y :
    transformReferences true base.components ref_gx1_dot_y.components =
      tgt_bcgx1_y.components := by decide

/-- §5.4.2 #36 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex36_gx1_dot_y_str :
    recompose (transformReferences true base.components ref_gx1_dot_y.components) =
      "http://a/b/c/g;x=1/y".toList := by decide

/-- §5.4.2 #37: `"g;x=1/../y" = "http://a/b/c/y"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g;x=1/../y`; rules EEECE. -/
theorem ex37_gx1_dotdot_y :
    transformReferences true base.components ref_gx1_dotdot_y.components =
      tgt_bcy.components := by decide

/-- §5.4.2 #37 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex37_gx1_dotdot_y_str :
    recompose (transformReferences true base.components ref_gx1_dotdot_y.components) =
      "http://a/b/c/y".toList := by decide

/-- §5.4.2 #38: `"g?y/./x" = "http://a/b/c/g?y/./x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (dots remain in query). -/
theorem ex38_g_q_y_dot_x :
    transformReferences true base.components ref_g_q_y_dot_x.components =
      tgt_bcg_q_y_dot_x.components := by decide

/-- §5.4.2 #38 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex38_g_q_y_dot_x_str :
    recompose (transformReferences true base.components ref_g_q_y_dot_x.components) =
      "http://a/b/c/g?y/./x".toList := by decide

/-- §5.4.2 #39: `"g?y/../x" = "http://a/b/c/g?y/../x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (dots remain in query). -/
theorem ex39_g_q_y_dotdot_x :
    transformReferences true base.components ref_g_q_y_dotdot_x.components =
      tgt_bcg_q_y_dotdot_x.components := by decide

/-- §5.4.2 #39 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex39_g_q_y_dotdot_x_str :
    recompose (transformReferences true base.components ref_g_q_y_dotdot_x.components) =
      "http://a/b/c/g?y/../x".toList := by decide

/-- §5.4.2 #40: `"g#s/./x" = "http://a/b/c/g#s/./x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (dots remain in fragment). -/
theorem ex40_g_f_s_dot_x :
    transformReferences true base.components ref_g_f_s_dot_x.components =
      tgt_bcg_f_s_dot_x.components := by decide

/-- §5.4.2 #40 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex40_g_f_s_dot_x_str :
    recompose (transformReferences true base.components ref_g_f_s_dot_x.components) =
      "http://a/b/c/g#s/./x".toList := by decide

/-- §5.4.2 #41: `"g#s/../x" = "http://a/b/c/g#s/../x"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (dots remain in fragment). -/
theorem ex41_g_f_s_dotdot_x :
    transformReferences true base.components ref_g_f_s_dotdot_x.components =
      tgt_bcg_f_s_dotdot_x.components := by decide

/-- §5.4.2 #41 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex41_g_f_s_dotdot_x_str :
    recompose (transformReferences true base.components ref_g_f_s_dotdot_x.components) =
      "http://a/b/c/g#s/../x".toList := by decide

/-- §5.4.2 #42: `"http:g" = "http:g"`.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);"
Branch 1; remove-dot-segments input `g`; rules E (identity; strict). -/
theorem ex42_strict_http_g :
    transformReferences true base.components ref_http_g.components =
      uri_http_g.components := by decide

/-- §5.4.2 #42 recomposed target.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
theorem ex42_strict_http_g_str :
    recompose (transformReferences true base.components ref_http_g.components) =
      "http:g".toList := by decide

/-- §5.4.2 #42: `"http:g" = "http://a/b/c/g"`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);"
Branch 5; remove-dot-segments input `/b/c/g`; rules EEE (equal scheme undefined in compatibility mode). -/
theorem ex42_legacy_http_g :
    transformReferences false base.components ref_http_g.components =
      tgt_bcg.components := by decide

/-- §5.4.2 #42 recomposed target.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem ex42_legacy_http_g_str :
    recompose (transformReferences false base.components ref_http_g.components) =
      "http://a/b/c/g".toList := by decide

/-! ## Beyond-RFC pins — dossier §4.3 items 1–5

These are consequences of the published algorithm on additional grammar
inputs, not additional examples claimed to appear in the RFC's §5.4 table.
-/

/-- Beyond-RFC item 1, `http://a` with an empty path.
RFC §5.2.3: "If the base URI has a defined authority component and an empty path". -/
def beyondBaseEmptyPath : URI := httpURI []

/-- Beyond-RFC item 1 input-tree rendering.
RFC §5.2.3: "If the base URI has a defined authority component and an empty path". -/
theorem beyondBaseEmptyPath_render :
    beyondBaseEmptyPath.render = "http://a".toList := by decide

/-- Beyond-RFC item 2 base includes a fragment.
RFC §5.2.2: "T.fragment = R.fragment;" -/
def beyondBaseFragment : URI :=
  httpURI [segB, segC, segDp] (some qQ) (some [.pchar (u 'f')])

/-- Beyond-RFC item 2 input-tree rendering.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem beyondBaseFragment_render :
    beyondBaseFragment.render = "http://a/b/c/d;p?q#f".toList := by decide

/-- Beyond-RFC item 3 rootless base `s:a/b`.
RFC §5.2.1: "only the scheme component is required to be present". -/
def beyondBaseRootless : URI :=
  { scheme := ⟨⟨'s', by decide⟩, []⟩,
    hierPart := .rootless { first := ⟨u 'a', []⟩, rest := [segB] },
    query := none, fragment := none }

/-- Beyond-RFC item 3 input-tree rendering.
RFC §5.2.1: "only the scheme component is required to be present". -/
theorem beyondBaseRootless_render :
    beyondBaseRootless.render = "s:a/b".toList := by decide

/-- Beyond-RFC item 3 target `s:a/g`.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
def beyondTargetRootless : URI :=
  { beyondBaseRootless with
    hierPart := .rootless { first := ⟨u 'a', []⟩, rest := [segG] } }

/-- Beyond-RFC item 3 target-tree rendering.
RFC §5.2.2: "T.path = merge(Base.path, R.path);" -/
theorem beyondTargetRootless_render :
    beyondTargetRootless.render = "s:a/g".toList := by decide

/-- Beyond-RFC item 4 dotted base; the published merge removes its last segment.
RFC §5.2.3: "all but the last segment of the base URI's path". -/
def beyondBaseDotted : URI := httpURI [segB, segC, segDotDot]

/-- Beyond-RFC item 4 input-tree rendering.
RFC §5.2.3: "all but the last segment of the base URI's path". -/
theorem beyondBaseDotted_render :
    beyondBaseDotted.render = "http://a/b/c/..".toList := by decide

/-- Beyond-RFC item 5 scheme-bearing reference with a rootless dotted path.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
def beyondRefForeignScheme : URIReference := .uri
  { scheme := ⟨⟨'s', by decide⟩, [.digit '2' (by decide)]⟩,
    hierPart := .rootless { first := ⟨u 'a', []⟩, rest := [segDotDot, segB] },
    query := none, fragment := none }

/-- Beyond-RFC item 5 input-tree rendering.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
theorem beyondRefForeignScheme_render :
    beyondRefForeignScheme.render = "s2:a/../b".toList := by decide

/-- Beyond-RFC item 5 target: rule C pops `a`, rule E moves `/b`.
RFC §5.2.4: "remove the last segment and its preceding "/" (if any)". -/
def beyondTargetForeignScheme : URI :=
  { scheme := ⟨⟨'s', by decide⟩, [.digit '2' (by decide)]⟩,
    hierPart := .absolute (.nonempty ⟨u 'b', []⟩ []),
    query := none, fragment := none }

/-- Beyond-RFC item 5 target-tree rendering.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);" -/
theorem beyondTargetForeignScheme_render :
    beyondTargetForeignScheme.render = "s2:/b".toList := by decide

/-- Beyond-RFC item 1, component-level consequence.
RFC §5.2.3: "then return a string consisting of "/" concatenated with the reference's path". -/
theorem beyond01_empty_path_g :
    transformReferences true beyondBaseEmptyPath.components ref_g.components =
      tgt_ag.components := by decide

/-- Beyond-RFC item 1, recomposed-string consequence.
RFC §5.2.3: "then return a string consisting of "/" concatenated with the reference's path". -/
theorem beyond01_empty_path_g_str :
    recompose (transformReferences true beyondBaseEmptyPath.components ref_g.components) =
      "http://a/g".toList := by decide

/-- Beyond-RFC item 1, component-level consequence.
RFC §5.2.2: "T.path = Base.path;". -/
theorem beyond01_empty_path_empty :
    transformReferences true beyondBaseEmptyPath.components ref_empty.components =
      beyondBaseEmptyPath.components := by decide

/-- Beyond-RFC item 1, recomposed-string consequence.
RFC §5.2.2: "T.path = Base.path;". -/
theorem beyond01_empty_path_empty_str :
    recompose (transformReferences true beyondBaseEmptyPath.components ref_empty.components) =
      "http://a".toList := by decide

/-- Beyond-RFC item 2, component-level consequence.
RFC §5.2.2: "T.fragment = R.fragment;". -/
theorem beyond02_drop_fragment :
    transformReferences true beyondBaseFragment.components ref_empty.components =
      base.components := by decide

/-- Beyond-RFC item 2, recomposed-string consequence.
RFC §5.2.2: "T.fragment = R.fragment;". -/
theorem beyond02_drop_fragment_str :
    recompose (transformReferences true beyondBaseFragment.components ref_empty.components) =
      "http://a/b/c/d;p?q".toList := by decide

/-- Beyond-RFC item 3, component-level consequence.
RFC §5.2.2: "T.path = merge(Base.path, R.path);". -/
theorem beyond03_rootless_base :
    transformReferences true beyondBaseRootless.components ref_g.components =
      beyondTargetRootless.components := by decide

/-- Beyond-RFC item 3, recomposed-string consequence.
RFC §5.2.2: "T.path = merge(Base.path, R.path);". -/
theorem beyond03_rootless_base_str :
    recompose (transformReferences true beyondBaseRootless.components ref_g.components) =
      "s:a/g".toList := by decide

/-- Beyond-RFC item 4, component-level consequence.
RFC §5.2.3: "all but the last segment of the base URI's path". -/
theorem beyond04_dotted_base :
    transformReferences true beyondBaseDotted.components ref_g.components =
      tgt_bcg.components := by decide

/-- Beyond-RFC item 4, recomposed-string consequence.
RFC §5.2.3: "all but the last segment of the base URI's path". -/
theorem beyond04_dotted_base_str :
    recompose (transformReferences true beyondBaseDotted.components ref_g.components) =
      "http://a/b/c/g".toList := by decide

/-- Beyond-RFC item 5, component-level consequence.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);". -/
theorem beyond05_foreign_scheme :
    transformReferences true base.components beyondRefForeignScheme.components =
      beyondTargetForeignScheme.components := by decide

/-- Beyond-RFC item 5, recomposed-string consequence.
RFC §5.2.2: "T.path      = remove_dot_segments(R.path);". -/
theorem beyond05_foreign_scheme_str :
    recompose (transformReferences true base.components beyondRefForeignScheme.components) =
      "s2:/b".toList := by decide



/-! ## Target-tree witnesses for the §5.4 resolution theorems

Forty relative-reference rows use `targetRelOfAuthority`; the two strict
scheme-bearing Branch-1 rows use `target` with its explicit validity guard.
The compatibility `http:g` uses the URI-reference authority wrapper after
the equal scheme has been undefined. Thus every assertion instantiates the
appropriate target-construction theorem without claiming all 42 references
are relative references.
-/

/-- §5.4 #01 target-tree witness for `g:h`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex01_g_h_target_render :
    (target true base ref_g_h (by decide)).render =
      "g:h".toList := by
  rw [target_render]
  exact ex01_g_h_str

/-- §5.4 #02 target-tree witness for `g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex02_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g (by decide))).render =
      "http://a/b/c/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex02_g_str

/-- §5.4 #03 target-tree witness for `./g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex03_dot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot_g (by decide))).render =
      "http://a/b/c/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex03_dot_g_str

/-- §5.4 #04 target-tree witness for `g/`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex04_g_slash_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_slash (by decide))).render =
      "http://a/b/c/g/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex04_g_slash_str

/-- §5.4 #05 target-tree witness for `/g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex05_slash_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_slash_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex05_slash_g_str

/-- §5.4 #06 target-tree witness for `//g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex06_slashslash_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_slashslash_g (by decide))).render =
      "http://g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex06_slashslash_g_str

/-- §5.4 #07 target-tree witness for `?y`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex07_q_y_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_q_y (by decide))).render =
      "http://a/b/c/d;p?y".toList := by
  rw [targetRelOfAuthority_render]
  exact ex07_q_y_str

/-- §5.4 #08 target-tree witness for `g?y`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex08_g_q_y_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_q_y (by decide))).render =
      "http://a/b/c/g?y".toList := by
  rw [targetRelOfAuthority_render]
  exact ex08_g_q_y_str

/-- §5.4 #09 target-tree witness for `#s`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex09_hash_s_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_hash_s (by decide))).render =
      "http://a/b/c/d;p?q#s".toList := by
  rw [targetRelOfAuthority_render]
  exact ex09_hash_s_str

/-- §5.4 #10 target-tree witness for `g#s`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex10_g_hash_s_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_hash_s (by decide))).render =
      "http://a/b/c/g#s".toList := by
  rw [targetRelOfAuthority_render]
  exact ex10_g_hash_s_str

/-- §5.4 #11 target-tree witness for `g?y#s`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex11_g_qy_s_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_qy_s (by decide))).render =
      "http://a/b/c/g?y#s".toList := by
  rw [targetRelOfAuthority_render]
  exact ex11_g_qy_s_str

/-- §5.4 #12 target-tree witness for `;x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex12_semi_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_semi_x (by decide))).render =
      "http://a/b/c/;x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex12_semi_x_str

/-- §5.4 #13 target-tree witness for `g;x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex13_g_semi_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_semi_x (by decide))).render =
      "http://a/b/c/g;x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex13_g_semi_x_str

/-- §5.4 #14 target-tree witness for `g;x?y#s`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex14_g_semi_x_qy_s_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_semi_x_qy_s (by decide))).render =
      "http://a/b/c/g;x?y#s".toList := by
  rw [targetRelOfAuthority_render]
  exact ex14_g_semi_x_qy_s_str

/-- §5.4 #15 target-tree witness for ``.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex15_empty_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_empty (by decide))).render =
      "http://a/b/c/d;p?q".toList := by
  rw [targetRelOfAuthority_render]
  exact ex15_empty_str

/-- §5.4 #16 target-tree witness for `.`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex16_dot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot (by decide))).render =
      "http://a/b/c/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex16_dot_str

/-- §5.4 #17 target-tree witness for `./`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex17_dot_slash_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot_slash (by decide))).render =
      "http://a/b/c/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex17_dot_slash_str

/-- §5.4 #18 target-tree witness for `..`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex18_dotdot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dotdot (by decide))).render =
      "http://a/b/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex18_dotdot_str

/-- §5.4 #19 target-tree witness for `../`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex19_dotdot_slash_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dotdot_slash (by decide))).render =
      "http://a/b/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex19_dotdot_slash_str

/-- §5.4 #20 target-tree witness for `../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex20_dotdot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dotdot_g (by decide))).render =
      "http://a/b/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex20_dotdot_g_str

/-- §5.4 #21 target-tree witness for `../..`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex21_dotdot_dotdot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dotdot_dotdot (by decide))).render =
      "http://a/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex21_dotdot_dotdot_str

/-- §5.4 #22 target-tree witness for `../../`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex22_dd_dd_slash_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dd_dd_slash (by decide))).render =
      "http://a/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex22_dd_dd_slash_str

/-- §5.4 #23 target-tree witness for `../../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex23_dd_dd_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dd_dd_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex23_dd_dd_g_str

/-- §5.4 #24 target-tree witness for `../../../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex24_ddd_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_ddd_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex24_ddd_g_str

/-- §5.4 #25 target-tree witness for `../../../../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex25_dddd_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dddd_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex25_dddd_g_str

/-- §5.4 #26 target-tree witness for `/./g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex26_slash_dot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_slash_dot_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex26_slash_dot_g_str

/-- §5.4 #27 target-tree witness for `/../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex27_slash_dotdot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_slash_dotdot_g (by decide))).render =
      "http://a/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex27_slash_dotdot_g_str

/-- §5.4 #28 target-tree witness for `g.`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex28_g_dot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_dot (by decide))).render =
      "http://a/b/c/g.".toList := by
  rw [targetRelOfAuthority_render]
  exact ex28_g_dot_str

/-- §5.4 #29 target-tree witness for `.g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex29_dot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot_g2 (by decide))).render =
      "http://a/b/c/.g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex29_dot_g_str

/-- §5.4 #30 target-tree witness for `g..`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex30_g_dotdot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_dotdot (by decide))).render =
      "http://a/b/c/g..".toList := by
  rw [targetRelOfAuthority_render]
  exact ex30_g_dotdot_str

/-- §5.4 #31 target-tree witness for `..g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex31_dotdot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dotdot_g2 (by decide))).render =
      "http://a/b/c/..g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex31_dotdot_g_str

/-- §5.4 #32 target-tree witness for `./../g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex32_dot_slashdot_g_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot_slashdot_g (by decide))).render =
      "http://a/b/g".toList := by
  rw [targetRelOfAuthority_render]
  exact ex32_dot_slashdot_g_str

/-- §5.4 #33 target-tree witness for `./g/.`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex33_dot_g_dot_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_dot_g_dot (by decide))).render =
      "http://a/b/c/g/".toList := by
  rw [targetRelOfAuthority_render]
  exact ex33_dot_g_dot_str

/-- §5.4 #34 target-tree witness for `g/./h`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex34_g_slash_dot_h_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_slash_dot_h (by decide))).render =
      "http://a/b/c/g/h".toList := by
  rw [targetRelOfAuthority_render]
  exact ex34_g_slash_dot_h_str

/-- §5.4 #35 target-tree witness for `g/../h`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex35_g_slash_dotdot_h_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_slash_dotdot_h (by decide))).render =
      "http://a/b/c/h".toList := by
  rw [targetRelOfAuthority_render]
  exact ex35_g_slash_dotdot_h_str

/-- §5.4 #36 target-tree witness for `g;x=1/./y`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex36_gx1_dot_y_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_gx1_dot_y (by decide))).render =
      "http://a/b/c/g;x=1/y".toList := by
  rw [targetRelOfAuthority_render]
  exact ex36_gx1_dot_y_str

/-- §5.4 #37 target-tree witness for `g;x=1/../y`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex37_gx1_dotdot_y_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_gx1_dotdot_y (by decide))).render =
      "http://a/b/c/y".toList := by
  rw [targetRelOfAuthority_render]
  exact ex37_gx1_dotdot_y_str

/-- §5.4 #38 target-tree witness for `g?y/./x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex38_g_q_y_dot_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_q_y_dot_x (by decide))).render =
      "http://a/b/c/g?y/./x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex38_g_q_y_dot_x_str

/-- §5.4 #39 target-tree witness for `g?y/../x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex39_g_q_y_dotdot_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_q_y_dotdot_x (by decide))).render =
      "http://a/b/c/g?y/../x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex39_g_q_y_dotdot_x_str

/-- §5.4 #40 target-tree witness for `g#s/./x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex40_g_f_s_dot_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_f_s_dot_x (by decide))).render =
      "http://a/b/c/g#s/./x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex40_g_f_s_dot_x_str

/-- §5.4 #41 target-tree witness for `g#s/../x`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex41_g_f_s_dotdot_x_target_render :
    (targetRelOfAuthority true base (by decide)
      (relativeRefOfNoScheme ref_g_f_s_dotdot_x (by decide))).render =
      "http://a/b/c/g#s/../x".toList := by
  rw [targetRelOfAuthority_render]
  exact ex41_g_f_s_dotdot_x_str

/-- §5.4 #42 target-tree witness for `http:g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex42_strict_http_g_target_render :
    (target true base ref_http_g (by decide)).render =
      "http:g".toList := by
  rw [target_render]
  exact ex42_strict_http_g_str

/-- §5.4 #42 target-tree witness for `http:g`.
RFC §5.2.2: "T.fragment = R.fragment;" -/
theorem ex42_legacy_http_g_target_render :
    (targetReferenceOfAuthority false base (by decide) ref_http_g (by decide)).render =
      "http://a/b/c/g".toList := by
  rw [targetReferenceOfAuthority_render]
  exact ex42_legacy_http_g_str
