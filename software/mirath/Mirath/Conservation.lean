import Mirath.Distribution

/-!
The headline is quantified over all configurations in the explicit model
domain, including unbounded child/sibling counts and every named policy.
It is a conservation theorem, not a proof that the historical source texts
have been translated correctly; that separate fidelity obligation is exposed
in the rule table and the independently sourced numerical cases.
-/

namespace Mirath

/-- Every valid configuration distributes exactly one whole estate. -/
theorem distribution_total (c : Config) (h : Valid c) :
    total (distribution c) = 1 := by
  unfold distribution
  rw [total_canonical]
  exact total_settle _ _ _ h.2

/-- All final entitlements are nonnegative. This even holds on malformed
inputs; the `Valid` check is needed separately for conservation and scope.
-/
theorem distribution_nonnegative (c : Config) : Nonnegative (distribution c) := by
  apply canonical_nonnegative
  exact settle_nonnegative _ _ _ (fixedShares_nonnegative c)
    (residuaryWeights_nonnegative c) (returnWeights_nonnegative c)

theorem share_nonnegative (c : Config) (r : Role) : 0 ≤ share c r :=
  allocationShare_nonnegative r _ (distribution_nonnegative c)

/-- The checked API only returns estate-conserving distributions. -/
theorem distribute?_total (c : Config) (d : Allocation Role)
    (h : distribute? c = some d) : total d = 1 := by
  unfold distribute? at h
  split at h
  next hc =>
    have hd : distribution c = d := Option.some.inj h
    rw [← hd]
    exact distribution_total c hc
  next hc => contradiction

end Mirath
