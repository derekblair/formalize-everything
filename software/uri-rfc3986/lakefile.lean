import Lake
open Lake DSL

package «uri-rfc3986» where
  -- RFC 3986 URI generic syntax as an inductive specification.
  -- Pure Lean core: no Mathlib dependency for milestone 1.

@[default_target]
lean_lib «UriRfc3986» where
