import Init.Data.Rat.Lemmas
import Init.Data.List.Lemmas

/-!
The finite-role kinship schedule for milestone 1. All shares are *role totals*;
members of the same role share that total equally. Source keys below resolve in
`SOURCES.md`: Q4:11, Q4:12 and Q4:176 are the three verses; U is al-Uthaymin's
`Summary of the Fiqh of Inheritance`. The model assumes the listed persons are
otherwise legally eligible heirs. Absent roles, such as grandchildren, nephews,
uncles and distant kindred, are not silently represented by another role.
-/

namespace Mirath

inductive Role where
  | husband | wives | father | mother
  | paternalGrandfather | paternalGrandmother | maternalGrandmother
  | son | daughter | fullBrother | fullSister
  | paternalBrother | paternalSister | maternalBrother | maternalSister
  | publicTreasury
  deriving DecidableEq, BEq, Repr

def Role.all : List Role :=
  [.husband, .wives, .father, .mother, .paternalGrandfather,
   .paternalGrandmother, .maternalGrandmother, .son, .daughter,
   .fullBrother, .fullSister, .paternalBrother, .paternalSister,
   .maternalBrother, .maternalSister, .publicTreasury]

def Role.isSpouse : Role → Bool
  | .husband | .wives => true
  | _ => false

/-- Radd's default excludes spouses. The historically attributed spousal-return
variant is explicit; it is not asserted to be the consensus rule. See SOURCES.md.
-/
inductive RaddPolicy where
  | excludeSpouses | includeSpouses
  deriving DecidableEq, BEq, Repr

/-- The majority excludes the paternal grandmother through her living son (the
father). The Hanbali alternative permits her; U p.7 uses that alternative.
-/
inductive PaternalGrandmotherPolicy where
  | blockedByFather | inheritsWithFather
  deriving DecidableEq, BEq, Repr

/-- Majority counts even excluded siblings when reducing the mother's third.
Ibn Taymiyya/al-Sa'di count only structurally eligible siblings (IslamQA 13632).
-/
inductive MotherSiblingPolicy where
  | allSiblings | eligibleSiblings
  deriving DecidableEq, BEq, Repr

/-- The brief's radd approach is the default. The classical treasury alternative
of Zayd, Malik and al-Shafi'i is named explicitly (al-Mughni, §4855). Treasury
is an estate destination, not an invented relative; its person count is zero.
-/
inductive SurplusPolicy where
  | returnToHeirs | publicTreasury
  deriving DecidableEq, BEq, Repr

structure Config where
  husband : Nat := 0
  wives : Nat := 0
  father : Nat := 0
  mother : Nat := 0
  paternalGrandfather : Nat := 0
  paternalGrandmother : Nat := 0
  maternalGrandmother : Nat := 0
  sons : Nat := 0
  daughters : Nat := 0
  fullBrothers : Nat := 0
  fullSisters : Nat := 0
  paternalBrothers : Nat := 0
  paternalSisters : Nat := 0
  maternalBrothers : Nat := 0
  maternalSisters : Nat := 0
  raddPolicy : RaddPolicy := .excludeSpouses
  paternalGrandmotherPolicy : PaternalGrandmotherPolicy := .blockedByFather
  motherSiblingPolicy : MotherSiblingPolicy := .allSiblings
  surplusPolicy : SurplusPolicy := .returnToHeirs
  deriving DecidableEq, Repr

def Config.count (c : Config) : Role → Nat
  | .husband => c.husband
  | .wives => c.wives
  | .father => c.father
  | .mother => c.mother
  | .paternalGrandfather => c.paternalGrandfather
  | .paternalGrandmother => c.paternalGrandmother
  | .maternalGrandmother => c.maternalGrandmother
  | .son => c.sons
  | .daughter => c.daughters
  | .fullBrother => c.fullBrothers
  | .fullSister => c.fullSisters
  | .paternalBrother => c.paternalBrothers
  | .paternalSister => c.paternalSisters
  | .maternalBrother => c.maternalBrothers
  | .maternalSister => c.maternalSisters
  | .publicTreasury => 0

def Config.hasChildren (c : Config) : Bool := c.sons + c.daughters > 0

def Config.hasMaleAscendant (c : Config) : Bool :=
  c.father + c.paternalGrandfather > 0

def Config.siblingCount (c : Config) : Nat :=
  c.fullBrothers + c.fullSisters + c.paternalBrothers + c.paternalSisters +
    c.maternalBrothers + c.maternalSisters

def Config.agnaticSiblingCount (c : Config) : Nat :=
  c.fullBrothers + c.fullSisters + c.paternalBrothers + c.paternalSisters

/-- Structural eligibility for the named minority mother's-share policy.
An exhausted remainder is not exclusion: an eligible residuary still counts.
Hajb follows U pp.9–15; the policy's source is IslamQA 13632.
-/
def Config.eligibleSiblingCount (c : Config) : Nat :=
  if c.sons > 0 || c.hasMaleAscendant then 0
  else c.fullBrothers + c.fullSisters +
    (if c.fullBrothers > 0 || (c.daughters > 0 && c.fullSisters > 0) then 0
     else c.paternalBrothers +
       (if c.paternalBrothers > 0 || c.fullSisters < 2 then c.paternalSisters else 0)) +
    (if c.hasChildren then 0 else c.maternalBrothers + c.maternalSisters)

def Config.motherReducingSiblingCount (c : Config) : Nat :=
  match c.motherSiblingPolicy with
  | .allSiblings => c.siblingCount
  | .eligibleSiblings => c.eligibleSiblingCount

/-- The disputed common-third case (mushtaraka) is explicitly outside milestone
1, rather than silently choosing between the Hanafi/Hanbali and Maliki/Shafi'i
answers. Presence of a grandmother is included conservatively. See SOURCES.md.
-/
def Config.isMushtaraka (c : Config) : Bool :=
  !c.hasChildren && !c.hasMaleAscendant && c.husband > 0 &&
    c.maternalBrothers + c.maternalSisters ≥ 2 && c.fullBrothers > 0 &&
    c.mother + c.maternalGrandmother + c.paternalGrandmother > 0

/-- Structural scope, separate from the numerical availability of a recipient.
The grandfather/sibling dispute is excluded only when the grandfather is not
himself blocked by the father. Counts represent living, eligible relatives.
-/
def Supported (c : Config) : Prop :=
  c.husband ≤ 1 ∧ c.wives ≤ 4 ∧ (c.husband = 0 ∨ c.wives = 0) ∧
  c.father ≤ 1 ∧ c.mother ≤ 1 ∧ c.paternalGrandfather ≤ 1 ∧
  c.paternalGrandmother ≤ 1 ∧ c.maternalGrandmother ≤ 1 ∧
  (c.father > 0 ∨ c.paternalGrandfather = 0 ∨ c.agnaticSiblingCount = 0) ∧
  c.isMushtaraka = false

instance (c : Config) : Decidable (Supported c) := inferInstanceAs
  (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Q4:12: spouses' collective fixed entitlement before awl or radd. -/
def spouseShare (c : Config) : Rat :=
  (if c.husband > 0 then (if c.hasChildren then 1 / 4 else 1 / 2) else 0) +
  (if c.wives > 0 then (if c.hasChildren then 1 / 8 else 1 / 4) else 0)

/-- Q4:11; U p.6, including the two spouse-and-parents (`Umariyyatayn`) cases.
Under the default policy, two or more siblings reduce the mother even when the
father excludes them; `MotherSiblingPolicy` names the minority alternative.
-/
def motherShare (c : Config) : Rat :=
  if c.mother = 0 then 0
  else if c.hasChildren || c.motherReducingSiblingCount ≥ 2 then 1 / 6
  else if c.father > 0 && c.husband + c.wives > 0 then (1 - spouseShare c) / 3
  else 1 / 3

/-- U p.7: the mother excludes both grandmothers. The father's exclusion of his
mother follows the explicit policy; the maternal grandmother is not excluded
by the father. The two surviving eligible grandmothers share one sixth equally.
-/
def eligibleGrandmothers (c : Config) : Nat × Nat :=
  if c.mother > 0 then (0, 0)
  else
    (if c.paternalGrandmother > 0 &&
          (c.father = 0 || c.paternalGrandmotherPolicy == .inheritsWithFather)
      then 1 else 0,
     if c.maternalGrandmother > 0 then 1 else 0)

/-- The fixed-share schedule, before normalization. Children and siblings are
aggregate classes. Q4:11 supplies daughters/parents, Q4:12 spouses and maternal
siblings, Q4:176 full/paternal sisters; U pp.6–10 supplies the classical
completion/exclusion rules and grandmother entitlements.
-/
def fixedShare (c : Config) : Role → Rat
  | .husband =>
      if c.husband = 0 then 0 else if c.hasChildren then 1 / 4 else 1 / 2
  | .wives =>
      if c.wives = 0 then 0 else if c.hasChildren then 1 / 8 else 1 / 4
  | .father => if c.father > 0 && c.hasChildren then 1 / 6 else 0
  | .mother => motherShare c
  | .paternalGrandfather =>
      if c.father = 0 && c.paternalGrandfather > 0 && c.hasChildren then 1 / 6 else 0
  | .paternalGrandmother =>
      let (p, m) := eligibleGrandmothers c
      if p = 0 then 0 else (1 / 6) / ((p + m : Nat) : Rat)
  | .maternalGrandmother =>
      let (p, m) := eligibleGrandmothers c
      if m = 0 then 0 else (1 / 6) / ((p + m : Nat) : Rat)
  | .daughter =>
      if c.sons > 0 || c.daughters = 0 then 0
      else if c.daughters = 1 then 1 / 2 else 2 / 3
  | .fullSister =>
      if c.sons > 0 || c.hasMaleAscendant || c.fullBrothers > 0 ||
          c.daughters > 0 || c.fullSisters = 0 then 0
      else if c.fullSisters = 1 then 1 / 2 else 2 / 3
  | .paternalSister =>
      if c.sons > 0 || c.hasMaleAscendant || c.fullBrothers > 0 ||
          c.paternalBrothers > 0 || c.daughters > 0 || c.paternalSisters = 0 then 0
      else if c.fullSisters = 0 then
        if c.paternalSisters = 1 then 1 / 2 else 2 / 3
      else if c.fullSisters = 1 then 1 / 6 else 0
  | .maternalBrother =>
      if c.hasChildren || c.hasMaleAscendant || c.maternalBrothers = 0 then 0
      else if c.maternalBrothers + c.maternalSisters = 1 then 1 / 6
      else (1 / 3) * (c.maternalBrothers : Rat) /
        ((c.maternalBrothers + c.maternalSisters : Nat) : Rat)
  | .maternalSister =>
      if c.hasChildren || c.hasMaleAscendant || c.maternalSisters = 0 then 0
      else if c.maternalBrothers + c.maternalSisters = 1 then 1 / 6
      else (1 / 3) * (c.maternalSisters : Rat) /
        ((c.maternalBrothers + c.maternalSisters : Nat) : Rat)
  | _ => 0

/-- Zero entries are omitted, so blocked and absent roles have no allocation. -/
def fixedShares (c : Config) : List (Role × Rat) :=
  (Role.all.map fun r => (r, fixedShare c r)).filter fun p => p.2 != 0

/-- Add one nonempty aggregate class with its natural-number weight. -/
def weightedRole (r : Role) (weight : Nat) : List (Role × Rat) :=
  if weight = 0 then [] else [(r, (weight : Rat))]

/-- U pp.12–15: nearest class takes the remainder, with full kin preferred over
paternal kin. Q4:11 and Q4:176 give paired males weight two, females weight one.
U p.6: father/grandfather may combine a sixth with the remainder alongside a
daughter. U p.9: sisters with daughters become residuaries; full sisters then
exclude paternal siblings. This list assigns weights, not fixed entitlements.
-/
def residuaryWeights (c : Config) : List (Role × Rat) :=
  if c.sons > 0 then
    weightedRole .son (2 * c.sons) ++ weightedRole .daughter c.daughters
  else if c.father > 0 then weightedRole .father 1
  else if c.paternalGrandfather > 0 then weightedRole .paternalGrandfather 1
  else if c.fullBrothers > 0 then
    weightedRole .fullBrother (2 * c.fullBrothers) ++ weightedRole .fullSister c.fullSisters
  else if c.daughters > 0 && c.fullSisters > 0 then weightedRole .fullSister c.fullSisters
  else if c.paternalBrothers > 0 then
    weightedRole .paternalBrother (2 * c.paternalBrothers) ++
      weightedRole .paternalSister c.paternalSisters
  else if c.daughters > 0 then weightedRole .paternalSister c.paternalSisters
  else []

/-- Return surplus in proportion to fixed entitlements; spouse participation is
the explicit classical policy parameter. See SOURCES.md (radd).
-/
def returnWeights (c : Config) : List (Role × Rat) :=
  match c.surplusPolicy with
  | .publicTreasury => [(.publicTreasury, 1)]
  | .returnToHeirs =>
      match c.raddPolicy with
      | .includeSpouses => fixedShares c
      | .excludeSpouses => (fixedShares c).filter fun p => !p.1.isSpouse

end Mirath
