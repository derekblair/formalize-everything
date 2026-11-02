import Mirath.Model
import Mirath.Settlement
import Mirath.Totals

/-!
Public executable interface. `Valid` is a domain check on the input: legal
cardinalities, the explicit finite-role scope, and the existence of a recipient
for a surplus. It does not assume the output's conservation. A sole spouse in
the default nonspousal-radd mode fails this check; selecting the sourced
spousal-radd or public-treasury policy makes that case representable.
-/

namespace Mirath

def Valid (c : Config) : Prop :=
  Supported c ∧ SettlementValid (fixedShares c) (residuaryWeights c) (returnWeights c)

instance (c : Config) : Decidable (Valid c) := by
  unfold Valid SettlementValid
  infer_instance

/-- The complete estate ledger, with exactly one entry for every modeled role
(including zero entries and the explicitly selected public-treasury account).
Shares are aggregate totals for the role, not one share for each member.
-/
def distribution (c : Config) : Allocation Role :=
  canonical (settle (fixedShares c) (residuaryWeights c) (returnWeights c))

/-- Aggregate entitlement of a role in the final estate distribution. -/
def share (c : Config) (r : Role) : Rat := allocationShare r (distribution c)

/-- Equal division within an aggregate role. Absent roles and the non-person
treasury account have no per-person share. Q4:12's maternal brother and sister
roles have equal per-person entitlements; the other paired sibling/child roles
receive their 2:1 ratio in `residuaryWeights` before this division.
-/
def perPersonShare (c : Config) (r : Role) : Option Rat :=
  if c.count r = 0 then none else some (share c r / (c.count r : Rat))

/-- Checked entry point. `distribution` itself is total on every input, while
this interface refuses inputs outside the advertised domain.
-/
def distribute? (c : Config) : Option (Allocation Role) :=
  if Valid c then some (distribution c) else none

end Mirath
