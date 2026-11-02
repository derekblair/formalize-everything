import Mirath.Cases

/-!
Domain checks, separate from the 31 sourced numerical inheritance examples.
These establish the declared representation boundaries and check the public
API's refusal of unsupported inputs; they are not new classical distributions.
-/

namespace Mirath.DomainChecks

theorem empty_default_rejected : distribute? {} = none := by decide +kernel

theorem sole_spouse_default_rejected :
    distribute? { husband := 1 } = none := by decide +kernel

theorem simultaneous_spouses_rejected :
    distribute? { husband := 1, wives := 1, sons := 1 } = none := by decide +kernel

theorem five_wives_rejected :
    distribute? { wives := 5, sons := 1 } = none := by decide +kernel

theorem two_fathers_rejected :
    distribute? { father := 2 } = none := by decide +kernel

theorem grandfather_sibling_dispute_rejected :
    distribute? { paternalGrandfather := 1, fullBrothers := 1 } = none := by decide +kernel

theorem mushtaraka_rejected :
    distribute? { husband := 1, mother := 1, maternalBrothers := 2, fullBrothers := 2 }
      = none := by decide +kernel

theorem mushtaraka_with_grandmother_rejected :
    distribute? { husband := 1, maternalGrandmother := 1, maternalBrothers := 2, fullBrothers := 2 }
      = none := by decide +kernel

/-- The dispute exclusion does not reject a grandfather already blocked by
the father, nor invent an overlap when no agnatic sibling is present. -/
theorem blocked_grandfather_allowed :
    Valid { father := 1, paternalGrandfather := 1, fullBrothers := 1 } := by decide +kernel

/-- The denominator check is a recipient-availability condition; the named
spousal-radd option can make a previously unsupported input valid. No unsourced
final numerical vector is asserted here (see CASE-SOURCES.md). -/
theorem sole_spouse_inclusive_domain :
    Valid { husband := 1, raddPolicy := .includeSpouses } := by decide +kernel

theorem sole_spouse_treasury_domain :
    Valid { husband := 1, surplusPolicy := .publicTreasury } := by decide +kernel

/-- Per-person interpretation of C12, whose source explicitly divides the
estate equally between the two daughters (U, PDF p.18). -/
theorem two_daughters_per_person :
    perPersonShare Cases.c12 .daughter = some (1/2) := by decide +kernel

end Mirath.DomainChecks
