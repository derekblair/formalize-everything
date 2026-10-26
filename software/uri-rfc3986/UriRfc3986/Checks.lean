import UriRfc3986.Components
import UriRfc3986.Examples

/-!
# Milestone-1 audit checks

The programme bar is: zero `sorry`s, and no axioms beyond the standard
three (`propext`, `Classical.choice`, `Quot.sound`). This file prints the
axiom dependence of the milestone's theorems so the build log itself
carries the audit. (`#print axioms` output appears in the build log;
this file intentionally contains no theorems of its own.)
-/

-- The §5.3 recomposition theorems.
#print axioms URI.recompose_components
#print axioms AbsoluteURI.recompose_components
#print axioms RelativeRef.recompose_components
#print axioms URIReference.recompose_components

-- A sample of the §5.4 `decide`-checked membership theorems.
#print axioms base_render
#print axioms ref_g_qy_s_render
#print axioms ref_dddd_g_render
#print axioms uri_ipv4_render
#print axioms ipv6_full_render
