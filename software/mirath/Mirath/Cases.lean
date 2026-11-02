import Mirath.Conservation

/-!
Classical/reference-source cases C01–C31. Expected ledgers C01–C29 come from
al-Uthaymin's *Summary of the Fiqh of Inheritance*; C30–C31 come from the two
positions in IslamQA answer 13632. Exact locators and source portions are
recorded individually in CASE-SOURCES.md. `CaseMatches` checks
both input validity and EVERY role, including zeros, using `decide +kernel`.
The sibling and daughter entries are aggregate shares for all persons of that
role. No unsourced numerical case is included in this classical battery.
-/

namespace Mirath.Cases

def CaseMatches (c : Config) (expected : Allocation Role) : Prop :=
  Valid c ∧ distribution c = canonical expected

instance (c : Config) (e : Allocation Role) : Decidable (CaseMatches c e) := by
  unfold CaseMatches
  infer_instance

-- Pure fixed shares.
def c01 : Config := { husband := 1, fullSisters := 1 }
/-- C01, U PDF p.3: husband and full sister, one half each. -/
theorem husband_fullSister : CaseMatches c01
    [(.husband, 1/2), (.fullSister, 1/2)] := by decide +kernel

def c02 : Config := { daughters := 3, mother := 1, father := 1 }
/-- C02, U PDF p.8: three daughters collectively two thirds, parents one sixth each. -/
theorem daughters_parents : CaseMatches c02
    [(.daughter, 2/3), (.mother, 1/6), (.father, 1/6)] := by decide +kernel

def c03 : Config :=
  { maternalSisters := 1, fullSisters := 1, paternalSisters := 2, mother := 1 }
/-- C03, U PDF p.10: the paternal sisters complete two thirds with one sixth. -/
theorem sister_completion : CaseMatches c03
    [(.maternalSister, 1/6), (.fullSister, 1/2), (.paternalSister, 1/6),
     (.mother, 1/6)] := by decide +kernel

def c04 : Config := { maternalBrothers := 2, fullSisters := 2 }
/-- C04, U PDF p.10: maternal brothers one third, full sisters two thirds. -/
theorem maternal_brothers_full_sisters : CaseMatches c04
    [(.maternalBrother, 1/3), (.fullSister, 2/3)] := by decide +kernel

-- Pure residuary, including both sibling degrees.
def c05 : Config := { sons := 1, daughters := 1 }
/-- C05, U PDF p.7: son twice the daughter's share. -/
theorem son_daughter : CaseMatches c05
    [(.son, 2/3), (.daughter, 1/3)] := by decide +kernel

def c06 : Config := { fullBrothers := 1, fullSisters := 1 }
/-- C06, U PDF p.9: full brother twice the full sister's share. -/
theorem full_sibling_pair : CaseMatches c06
    [(.fullBrother, 2/3), (.fullSister, 1/3)] := by decide +kernel

def c07 : Config := { paternalBrothers := 1, paternalSisters := 1 }
/-- C07, U PDF p.13: paternal brother twice the paternal sister's share. -/
theorem paternal_sibling_pair : CaseMatches c07
    [(.paternalBrother, 2/3), (.paternalSister, 1/3)] := by decide +kernel

-- Fixed shares plus residue.
def c08 : Config := { father := 1, daughters := 1 }
/-- C08, U PDF p.6: the father combines his sixth and the residue. -/
theorem father_daughter : CaseMatches c08
    [(.father, 1/2), (.daughter, 1/2)] := by decide +kernel

def c09 : Config := { daughters := 1, fullSisters := 1 }
/-- C09, U PDF p.13: a full sister is residuary with a daughter. -/
theorem daughter_fullSister : CaseMatches c09
    [(.daughter, 1/2), (.fullSister, 1/2)] := by decide +kernel

def c10 : Config := { wives := 1, daughters := 1, fullBrothers := 1 }
/-- C10, U PDF p.7: eighth, half, and the remaining three eighths. -/
theorem wife_daughter_brother : CaseMatches c10
    [(.wives, 1/8), (.daughter, 1/2), (.fullBrother, 3/8)] := by decide +kernel

-- Radd, with the majority nonspousal-return default.
def c11 : Config := { daughters := 1 }
/-- C11, U PDF p.18: the sole daughter receives the estate by share and return. -/
theorem sole_daughter : CaseMatches c11 [(.daughter, 1)] := by decide +kernel

def c12 : Config := { daughters := 2 }
/-- C12, U PDF p.18: two daughters divide the entire estate equally. -/
theorem two_daughters : CaseMatches c12 [(.daughter, 1)] := by decide +kernel

def c13 : Config := { wives := 1, mother := 1, maternalBrothers := 1 }
/-- C13, U PDF p.18: the wife retains one fourth; only the blood sharers receive return. -/
theorem wife_mother_maternalBrother : CaseMatches c13
    [(.wives, 1/4), (.mother, 1/2), (.maternalBrother, 1/4)] := by decide +kernel

-- Awl, including 6→7, 6→10, 12→13, and 24→27.
def c14 : Config := { husband := 1, fullSisters := 2 }
/-- C14, U PDF p.10: the stipulated classical husband-and-two-sisters case. -/
theorem husband_two_sisters : CaseMatches c14
    [(.husband, 3/7), (.fullSister, 4/7)] := by decide +kernel

theorem husband_two_sisters_before_awl : total (fixedShares c14) = 7/6 := by decide +kernel

def c15 : Config :=
  { husband := 1, mother := 1, fullSisters := 2, maternalSisters := 2 }
/-- C15, U PDF p.10: source portions 3,1,4,2 out of ten. -/
theorem awl_ten : CaseMatches c15
    [(.husband, 3/10), (.mother, 1/10), (.fullSister, 2/5),
     (.maternalSister, 1/5)] := by decide +kernel

def c16 : Config := { wives := 1, fullSisters := 2, maternalSisters := 1 }
/-- C16, U PDF p.10: source portions 3,8,2 out of thirteen. -/
theorem awl_thirteen : CaseMatches c16
    [(.wives, 3/13), (.fullSister, 8/13), (.maternalSister, 2/13)] := by decide +kernel

def c17 : Config := { wives := 1, daughters := 2, mother := 1, father := 1 }
/-- C17, U PDF p.11: source portions 3,16,4,4 out of twenty-seven. -/
theorem awl_twenty_seven : CaseMatches c17
    [(.wives, 1/9), (.daughter, 16/27), (.mother, 4/27), (.father, 4/27)] := by decide +kernel

-- Umariyyatayn and basic verse/classical examples.
def c18 : Config := { husband := 1, mother := 1, father := 1 }
/-- C18, U PDF p.6: mother takes one third of what remains after the husband. -/
theorem umari_husband : CaseMatches c18
    [(.husband, 1/2), (.mother, 1/6), (.father, 1/3)] := by decide +kernel

def c19 : Config := { wives := 1, mother := 1, father := 1 }
/-- C19, U PDF p.6: mother takes one third of what remains after the wife. -/
theorem umari_wife : CaseMatches c19
    [(.wives, 1/4), (.mother, 1/4), (.father, 1/2)] := by decide +kernel

def c20 : Config := { husband := 1, father := 1 }
/-- C20, U PDF p.5. -/
theorem husband_father : CaseMatches c20
    [(.husband, 1/2), (.father, 1/2)] := by decide +kernel

def c21 : Config := { husband := 1, sons := 1 }
/-- C21, U PDF p.5. -/
theorem husband_son : CaseMatches c21
    [(.husband, 1/4), (.son, 3/4)] := by decide +kernel

def c22 : Config := { wives := 1, father := 1 }
/-- C22, U PDF pp.5–6. -/
theorem wife_father : CaseMatches c22
    [(.wives, 1/4), (.father, 3/4)] := by decide +kernel

def c23 : Config := { wives := 1, sons := 1 }
/-- C23, U PDF p.6. -/
theorem wife_son : CaseMatches c23
    [(.wives, 1/8), (.son, 7/8)] := by decide +kernel

def c24 : Config := { mother := 1, father := 1 }
/-- C24, U PDF p.6. -/
theorem mother_father : CaseMatches c24
    [(.mother, 1/3), (.father, 2/3)] := by decide +kernel

def c25 : Config := { mother := 1, sons := 1 }
/-- C25, U PDF p.6. -/
theorem mother_son : CaseMatches c25
    [(.mother, 1/6), (.son, 5/6)] := by decide +kernel

-- Immediate grandparents (the source's paternal-line grandfather definition).
def c26 : Config := { paternalGrandmother := 1, sons := 1 }
/-- C26, U PDF p.7: one eligible grandmother receives a sixth. -/
theorem grandmother_son : CaseMatches c26
    [(.paternalGrandmother, 1/6), (.son, 5/6)] := by decide +kernel

def c27 : Config := { paternalGrandfather := 1, sons := 1 }
/-- C27, U PDF p.7: grandfather by fixed share only. -/
theorem grandfather_son : CaseMatches c27
    [(.paternalGrandfather, 1/6), (.son, 5/6)] := by decide +kernel

def c28 : Config := { mother := 1, paternalGrandfather := 1 }
/-- C28, U PDF p.7: grandfather by residue only. -/
theorem mother_grandfather : CaseMatches c28
    [(.mother, 1/3), (.paternalGrandfather, 2/3)] := by decide +kernel

def c29 : Config := { daughters := 1, paternalGrandfather := 1 }
/-- C29, U PDF p.7: grandfather by fixed share and residue. -/
theorem daughter_grandfather : CaseMatches c29
    [(.daughter, 1/2), (.paternalGrandfather, 1/2)] := by decide +kernel

-- The independently sourced two positions in B13632.
def c30 : Config := { mother := 1, father := 1, fullBrothers := 4 }
/-- C30, B13632: majority counts siblings blocked by the father. -/
theorem blocked_siblings_majority : CaseMatches c30
    [(.mother, 1/6), (.father, 5/6)] := by decide +kernel

def c31 : Config := { c30 with motherSiblingPolicy := .ignoreFatherBlockedSiblings }
/-- C31, B13632: the named Ibn Taymiyya/al-Sa'di alternative. -/
theorem blocked_siblings_alternative : CaseMatches c31
    [(.mother, 1/3), (.father, 2/3)] := by decide +kernel

end Mirath.Cases
