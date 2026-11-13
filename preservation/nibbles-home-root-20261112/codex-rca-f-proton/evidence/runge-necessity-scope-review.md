# Independent assessment of Rudin 13.8 necessity scope

Read directly from the printed third edition, pp. 271–272 (`source-rudin.txt`, around lines 14842–14865), independently of the formal theorem draft.

The paragraph starts with the explicit hypothesis that the compact set K has disconnected spherical complement. It proves failure of polynomial approximation by choosing a bounded complementary component and a point α there. The final sentence then refers to “the same argument” and says that the prescribed representatives in Theorem 13.6 cannot be omitted.

There are two possible scopes for that final sentence:

1. **Context-qualified reading:** the preceding disconnected-complement hypothesis remains in force. This is a natural reading of the paragraph. The singleton example has connected complement and therefore does not contradict this claim. The maximum-modulus argument proves necessity for each omitted bounded component directly. Treating a component containing infinity requires the equivalent spherical argument or a Möbius change of coordinates with chart center in a different component.
2. **Unrestricted converse reading:** for every compact K allowed in 13.6, approximation of all holomorphic-near-K functions requires an allowed pole in every spherical complementary component. This fails for K={0}: every function on K is represented exactly by the constant f(0), which has no spherical poles. The empty compact set is also degenerate. The parent's `RungeNecessityException.lean` records the singleton counterexample, subject to its pending compiler check.

Recommended disclosure: the unrestricted extrapolation is false and the singleton counterexample documents why its extra quantifier cannot be silently inserted. It is **not** a counterexample to Runge's approximation theorem, nor to 13.8 with its preceding disconnected-complement hypothesis retained. The faithful node inventory should state that scope explicitly. Do not describe the printed main theorem as false.

A plausible unrestricted corrected necessity statement excludes compact sets with fewer than two points: when the spherical complement is connected and the only representative is omitted, the allowed rational functions have no poles anywhere and are constants; a function taking different values at two points cannot be uniformly approximated by constants. For disconnected complements, the context-qualified necessity argument applies. This correction is a mathematical assessment, not an assertion that its complete Lean proof has been checked.
