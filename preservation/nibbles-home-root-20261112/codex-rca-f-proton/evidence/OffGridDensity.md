# Off-grid density and identity extension draft

`OffGridDensity.lean` is unvalidated scratch code for a subsequent aggregate
check. It proves density after deleting any countable sets of horizontal and
vertical coordinate lines, so it includes both finite grid-line sets and the
entire integer square lattice. The proof uses density of the complements of
countable subsets of the real line and `Complex.closure_reProdIm`.

`open_subset_closure_off_coordinate_lines` says every open subset lies in the
closure of its off-grid points. The two identity-extension lemmas then cover:

- equality at a single point, assuming continuity of the two functions only
  at that point and an off-grid identity in an open neighborhood;
- equality throughout an open region, assuming continuity on that region.

These discharge the topological extension step of printed 13.5 once the grid
sum has been calculated off the grid lines. For a point of K, the neighborhood
can be the intersection of the interior of the selected-cell union and the
complement of the residual contour support. `ContourContinuity.lean` supplies
the contour integral's required continuity at that point.

Five axiom-print statements are present; no validation claim is made yet.
