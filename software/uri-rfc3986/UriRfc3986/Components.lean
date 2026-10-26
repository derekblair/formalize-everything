import UriRfc3986.Grammar

/-!
# §5.3 — Component recomposition

The five components of a URI reference, and the recomposition algorithm
of §5.3, as a function. The correctness statement against the grammar of
`Grammar.lean` is the theorem family at the bottom: for every derivation
tree, recomposing its components reproduces exactly the string the tree
derives.
-/

/-- The five components of a URI reference (§3; extracted per Appendix B).

The path is *always defined* (possibly empty) — the §5.3 algorithm
appends it unconditionally. The other four components are `Option`s,
preserving the distinction the RFC is careful about in §5.3: a component
that is *undefined* (its separator was not present) versus one that is
*defined but empty* (the separator was present and immediately followed
by the next separator or the end of the reference). -/
structure Components where
  scheme : Option (List Char)
  authority : Option (List Char)
  path : List Char
  query : Option (List Char)
  fragment : Option (List Char)

/-- The §5.3 recomposition algorithm, step for step as the RFC states it:

```
result = ""
if defined(scheme)   then append scheme and ":" to result
if defined(authority) then append "//" and authority to result
append path to result
if defined(query)    then append "?" and query to result
if defined(fragment) then append "#" and fragment to result
return result
```
-/
def recompose (c : Components) : List Char :=
  (match c.scheme with
   | some s => s ++ [':']
   | none => []) ++
  (match c.authority with
   | some a => ['/', '/'] ++ a
   | none => []) ++
  c.path ++
  (match c.query with
   | some q => '?' :: q
   | none => []) ++
  (match c.fragment with
   | some f => '#' :: f
   | none => [])

/-- The components of a `URI` derivation tree, extracted componentwise:
the scheme and the rendered subtrees for authority, path, query and
fragment. This is the spec-level counterpart of the Appendix B parse. -/
def URI.components (u : URI) : Components :=
  { scheme := some u.scheme.render
    authority := u.hierPart.authorityString
    path := u.hierPart.pathString
    query := u.query.map Query.render
    fragment := u.fragment.map Fragment.render }

/-- Recomposition stated against the §3 grammar: a URI's components,
recomposed by the §5.3 algorithm, give exactly the string the URI tree
derives. -/
theorem URI.recompose_components (u : URI) :
    recompose u.components = u.render := by
  obtain ⟨s, hp, q, f⟩ := u
  cases hp <;> cases q <;> cases f <;>
    simp [recompose, URI.components, URI.render, HierPart.render,
      HierPart.authorityString, HierPart.pathString, Authority.render,
      PathAbempty.render, List.append_assoc]

/-- The components of an `absolute-URI` tree. -/
def AbsoluteURI.components (u : AbsoluteURI) : Components :=
  { scheme := some u.scheme.render
    authority := u.hierPart.authorityString
    path := u.hierPart.pathString
    query := u.query.map Query.render
    fragment := none }

theorem AbsoluteURI.recompose_components (u : AbsoluteURI) :
    recompose u.components = u.render := by
  obtain ⟨s, hp, q⟩ := u
  cases hp <;> cases q <;>
    simp [recompose, AbsoluteURI.components, AbsoluteURI.render,
      HierPart.render, HierPart.authorityString, HierPart.pathString,
      Authority.render, PathAbempty.render, List.append_assoc]

/-- The components of a `relative-ref` tree: no scheme; authority, path,
query and fragment from the relative part. -/
def RelativeRef.components (r : RelativeRef) : Components :=
  { scheme := none
    authority := r.relPart.authorityString
    path := r.relPart.pathString
    query := r.query.map Query.render
    fragment := r.fragment.map Fragment.render }

theorem RelativeRef.recompose_components (r : RelativeRef) :
    recompose r.components = r.render := by
  obtain ⟨rp, q, f⟩ := r
  cases rp <;> cases q <;> cases f <;>
    simp [recompose, RelativeRef.components, RelativeRef.render,
      RelativePart.render, RelativePart.authorityString,
      RelativePart.pathString, Authority.render, PathAbempty.render,
      List.append_assoc]

/-- The components of a `URI-reference` tree. -/
def URIReference.components : URIReference → Components
  | .uri u => u.components
  | .relative r => r.components

theorem URIReference.recompose_components (x : URIReference) :
    recompose x.components = x.render := by
  cases x with
  | uri u => exact u.recompose_components
  | relative r => exact r.recompose_components
