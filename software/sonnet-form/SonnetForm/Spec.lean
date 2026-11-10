import Std

/-!
# A finite, decidable model of Shakespearean sonnet form

This specification checks supplied pronunciation annotations, not bare English.
The annotation boundary and every discretionary restriction are documented in
`../SPEC.md`. False means unstressed and true means stressed. All indices are
zero-based. The text field is never changed by these checks.
-/

namespace SonnetForm

/-- One annotated reading. An elision indexes a syllable in `stress` before deletion. -/
structure Scan where
  stress : List Bool
  elision : Option Nat := none
  deriving Repr, BEq, DecidableEq

/-- `none` means that a line-ending rhyme class has not been established.
An empty `scans` list means that no complete pronunciation annotation is available. -/
structure Line where
  text : String
  rhyme : Option String
  scans : List Scan
  deriving Repr, BEq, DecidableEq

structure Sonnet where
  number : Nat
  lines : List Line
  deriving Repr, BEq, DecidableEq

inductive License where
  | initialTrochaicInversion
  | interiorTrochaicInversion
  | feminineEnding
  | pyrrhicSubstitution
  | spondaicSubstitution
  | unstressedElision
  deriving Repr, BEq, DecidableEq

def licenseName : License → String
  | .initialTrochaicInversion => "INITIAL_TROCHAIC_INVERSION"
  | .interiorTrochaicInversion => "INTERIOR_TROCHAIC_INVERSION"
  | .feminineEnding => "FEMININE_ENDING"
  | .pyrrhicSubstitution => "PYRRHIC_SUBSTITUTION"
  | .spondaicSubstitution => "SPONDAIC_SUBSTITUTION"
  | .unstressedElision => "UNSTRESSED_ELISION"

/-- Exactly five unstressed/stressed pairs. -/
def pentameter : List Bool :=
  [false, true, false, true, false, true, false, true, false, true]

/-- Remove precisely the designated position; invalid positions fail `elisionValid`. -/
def eraseAt (xs : List Bool) (i : Nat) : List Bool :=
  xs.take i ++ xs.drop (i + 1)

/-- At most one explicitly annotated syllable may be elided, and it must be
unstressed. Linguistic eligibility for that annotation is an external assumption. -/
def elisionValid (s : Scan) : Bool :=
  match s.elision with
  | none => true
  | some i => i < s.stress.length && s.stress[i]? == some false

def afterElision (s : Scan) : List Bool :=
  match s.elision with
  | none => s.stress
  | some i => eraseAt s.stress i

/-- A feminine ending is precisely an eleventh, unstressed syllable. -/
def hasFeminineEnding (s : Scan) : Bool :=
  let xs := afterElision s
  xs.length == 11 && xs[10]? == some false

/-- A licensed scan still has a ten-syllable core, after a permitted elision
and/or the removal of a feminine ending. -/
def meterCore (s : Scan) : List Bool :=
  let xs := afterElision s
  if hasFeminineEnding s then xs.take 10 else xs

def feet : List Bool → List (Bool × Bool)
  | a :: b :: rest => (a, b) :: feet rest
  | _ => []

def isIamb (f : Bool × Bool) : Bool := f == (false, true)
def isTrochee (f : Bool × Bool) : Bool := f == (true, false)
def isPyrrhic (f : Bool × Bool) : Bool := f == (false, false)
def isSpondee (f : Bool × Bool) : Bool := f == (true, true)

/-- MD-INTERIOR-INVERSION: third/fourth feet are the admitted interior
positions. This positional approximation does not infer phrasal boundaries. -/
def interiorInversionFoot (i : Nat) : Bool := i == 2 || i == 3

/-- Trochees are allowed initially or in the third/fourth feet. The enclosing
check also limits interior inversions to one and all substitutions to two. -/
def allowedFoot (i : Nat) (f : Bool × Bool) : Bool :=
  isIamb f || isPyrrhic f || isSpondee f ||
    ((i == 0 || interiorInversionFoot i) && isTrochee f)

/-- Strict meter admits neither substitutions nor elisions nor extra syllables. -/
def scanStrict (s : Scan) : Bool :=
  s.elision == none && s.stress == pentameter

/-- MD-METER-BUDGET: exactly five feet, at least three of them iambic,
and at most one interior trochee. A feminine ending and a single annotated
unstressed elision can combine with these substitutions. No deletion can turn
a tetrameter into a pentameter. -/
def scanLicensed (s : Scan) : Bool :=
  let core := meterCore s
  let fs := feet core
  elisionValid s && core.length == 10 &&
    (fs.zipIdx.all fun (f, i) => allowedFoot i f) &&
    ((fs.drop 1).filter isTrochee).length ≤ 1 &&
    (fs.filter fun f => !isIamb f).length ≤ 2

/-- Each license has its own executable predicate. The enclosing licensed
check must succeed, so occurrence in a failed scan is not a license grant. -/
def initialTrochaicInversion (s : Scan) : Bool :=
  scanLicensed s && (feet (meterCore s)).head? == some (true, false)

def interiorTrochaicInversion (s : Scan) : Bool :=
  scanLicensed s && ((feet (meterCore s)).drop 1).any isTrochee

def feminineEnding (s : Scan) : Bool :=
  scanLicensed s && hasFeminineEnding s

def pyrrhicSubstitution (s : Scan) : Bool :=
  scanLicensed s && (feet (meterCore s)).any isPyrrhic

def spondaicSubstitution (s : Scan) : Bool :=
  scanLicensed s && (feet (meterCore s)).any isSpondee

def unstressedElision (s : Scan) : Bool :=
  scanLicensed s && s.elision.isSome

def usesLicense : License → Scan → Bool
  | .initialTrochaicInversion => initialTrochaicInversion
  | .interiorTrochaicInversion => interiorTrochaicInversion
  | .feminineEnding => feminineEnding
  | .pyrrhicSubstitution => pyrrhicSubstitution
  | .spondaicSubstitution => spondaicSubstitution
  | .unstressedElision => unstressedElision

def allLicenses : List License :=
  [.initialTrochaicInversion, .interiorTrochaicInversion, .feminineEnding,
   .pyrrhicSubstitution, .spondaicSubstitution, .unstressedElision]

def scanLicenses (s : Scan) : List License :=
  allLicenses.filter (fun license => usesLicense license s)

/-- Existential over the explicitly supplied readings, not over arbitrary stress strings. -/
def lineMeterStrict (l : Line) : Bool := l.scans.any scanStrict
def lineMeterLicensed (l : Line) : Bool := l.scans.any scanLicensed

/-- The first passing reading supplies diagnostic license names; data producers
must document their candidate ordering. This does not change existential verdicts. -/
def lineLicenses (l : Line) : List License :=
  match l.scans.find? scanLicensed with
  | some s => scanLicenses s
  | none => []

def lineCount (s : Sonnet) : Bool := s.lines.length == 14

def scheme : List Nat := [0, 1, 0, 1, 2, 3, 2, 3, 4, 5, 4, 5, 6, 6]

/-- MD-RHYME-EXACT: same letters mean the same class and different letters
mean different classes. Missing/empty annotations fail. This includes length14;
a non-14-line poem therefore fails rhyme as well as line count. -/
def rhymeScheme (s : Sonnet) : Bool :=
  let rs := s.lines.map (·.rhyme)
  rs.length == 14 &&
    rs.all (fun r => match r with | some c => !c.isEmpty | none => false) &&
    (List.range 14).all (fun i =>
      (List.range 14).all (fun j =>
        (rs[i]? == rs[j]?) == (scheme[i]? == scheme[j]?)))

/-- Meter is independent of line count but requires at least one line, avoiding
vacuous success for an empty poem. Every encoded line must pass. -/
def meterStrict (s : Sonnet) : Bool :=
  !s.lines.isEmpty && s.lines.all lineMeterStrict

def meterLicensed (s : Sonnet) : Bool :=
  !s.lines.isEmpty && s.lines.all lineMeterLicensed

/-- Propositional interfaces to the executable specification. -/
def HasFourteenLines (s : Sonnet) : Prop := lineCount s = true
def HasRhymeScheme (s : Sonnet) : Prop := rhymeScheme s = true
def HasStrictMeter (s : Sonnet) : Prop := meterStrict s = true
def HasLicensedMeter (s : Sonnet) : Prop := meterLicensed s = true

instance (s : Sonnet) : Decidable (HasFourteenLines s) := inferInstanceAs (Decidable (_ = _))
instance (s : Sonnet) : Decidable (HasRhymeScheme s) := inferInstanceAs (Decidable (_ = _))
instance (s : Sonnet) : Decidable (HasStrictMeter s) := inferInstanceAs (Decidable (_ = _))
instance (s : Sonnet) : Decidable (HasLicensedMeter s) := inferInstanceAs (Decidable (_ = _))

/-- Every component verdict is kept separately. -/
structure Verdict where
  number : Nat
  lineCount : Bool
  rhyme : Bool
  strictMeter : Bool
  licensedMeter : Bool
  deriving Repr, BEq, DecidableEq

def verdict (s : Sonnet) : Verdict :=
  ⟨s.number, lineCount s, rhymeScheme s, meterStrict s, meterLicensed s⟩

/- Small boundary checks of the actual specification, checked by the kernel. -/
theorem canonical_passes : scanStrict ⟨pentameter, none⟩ = true ∧
    scanLicensed ⟨pentameter, none⟩ = true := by decide

theorem tetrameter_fails :
    scanLicensed ⟨[false, true, false, true, false, true, false, true], none⟩ = false := by
  decide

theorem initial_inversion_passes : initialTrochaicInversion
    ⟨[true, false, false, true, false, true, false, true, false, true], none⟩ = true := by
  decide

theorem feminine_ending_passes : feminineEnding ⟨pentameter ++ [false], none⟩ = true := by
  decide

theorem pyrrhic_passes : pyrrhicSubstitution
    ⟨[false, false, false, true, false, true, false, true, false, true], none⟩ = true := by
  decide

theorem spondaic_passes : spondaicSubstitution
    ⟨[true, true, false, true, false, true, false, true, false, true], none⟩ = true := by
  decide

theorem elision_passes : unstressedElision ⟨false :: pentameter, some 0⟩ = true := by
  decide

theorem stressed_elision_fails :
    scanLicensed ⟨true :: pentameter, some 0⟩ = false := by decide

theorem invalid_elision_fails : scanLicensed ⟨pentameter, some 99⟩ = false := by decide

theorem second_foot_trochee_fails : scanLicensed
    ⟨[false, true, true, false, false, true, false, true, false, true], none⟩ = false := by
  decide

/-- Every permitted interior position has a named diagnostic. -/
theorem third_foot_inversion_passes : scanLicenses
    ⟨[false, true, false, true, true, false, false, true, false, true], none⟩ =
      [.interiorTrochaicInversion] := by decide

theorem fourth_foot_inversion_passes : scanLicenses
    ⟨[false, true, false, true, false, true, true, false, false, true], none⟩ =
      [.interiorTrochaicInversion] := by decide

theorem final_foot_trochee_fails : scanLicensed
    ⟨[false, true, false, true, false, true, false, true, true, false], none⟩ = false := by
  decide

/-- Two interior inversions violate their own bound, even within the total budget. -/
theorem two_interior_inversions_fail : scanLicensed
    ⟨[false, true, false, true, true, false, true, false, false, true], none⟩ = false := by
  decide

theorem initial_and_interior_inversions_pass : scanLicenses
    ⟨[true, false, false, true, false, true, true, false, false, true], none⟩ =
      [.initialTrochaicInversion, .interiorTrochaicInversion] := by decide

theorem interior_and_pyrrhic_pass : scanLicenses
    ⟨[false, true, false, false, false, true, true, false, false, true], none⟩ =
      [.interiorTrochaicInversion, .pyrrhicSubstitution] := by decide

theorem interior_then_spondee_pass : scanLicenses
    ⟨[false, true, false, true, false, true, true, false, true, true], none⟩ =
      [.interiorTrochaicInversion, .spondaicSubstitution] := by decide

theorem three_substitutions_including_interior_fail : scanLicensed
    ⟨[true, false, false, false, false, true, true, false, false, true], none⟩ = false := by
  decide

/-- Interior positions are counted on the core after elision and feminine ending. -/
theorem interior_elision_and_feminine_ending_pass : scanLicenses
    ⟨[false, false, true, false, true, false, true, true, false, false, true, false], some 0⟩ =
      [.interiorTrochaicInversion, .feminineEnding, .unstressedElision] := by decide

theorem failed_interior_scan_has_no_licenses : scanLicenses
    ⟨[false, true, false, true, true, false, true, false, false, true], none⟩ = [] := by
  decide

theorem three_substitutions_fail : scanLicensed
    ⟨[false, false, true, true, false, false, false, true, false, true], none⟩ = false := by
  decide

/- Rhyme boundary fixtures use arbitrary class names, not literary assertions. -/
private def rhymeFixture (classes : List (Option String)) : Sonnet :=
  ⟨0, classes.map fun c => ⟨"fixture", c, [⟨pentameter, none⟩]⟩⟩

private def exactRhymeFixture : List (Option String) :=
  [some "a", some "b", some "a", some "b", some "c", some "d", some "c", some "d",
   some "e", some "f", some "e", some "f", some "g", some "g"]

theorem exact_rhyme_passes : rhymeScheme (rhymeFixture exactRhymeFixture) = true := by
  decide

/-- Merely matching each expected pair is insufficient when differently named
signature classes coincide. -/
theorem repeated_cross_letter_rhyme_fails : rhymeScheme (rhymeFixture
    [some "a", some "b", some "a", some "b", some "a", some "d", some "a", some "d",
     some "e", some "f", some "e", some "f", some "g", some "g"]) = false := by
  decide

theorem missing_rhyme_class_fails : rhymeScheme (rhymeFixture
    (none :: exactRhymeFixture.drop 1)) = false := by decide

theorem empty_rhyme_class_fails : rhymeScheme (rhymeFixture
    (some "" :: exactRhymeFixture.drop 1)) = false := by decide

theorem fifteenth_line_rhyme_fails :
    rhymeScheme (rhymeFixture (exactRhymeFixture ++ [some "g"])) = false := by decide

theorem twelve_line_rhyme_fails :
    rhymeScheme (rhymeFixture (exactRhymeFixture.take 12)) = false := by decide

theorem empty_poem_fails_all_components : verdict ⟨0, []⟩ =
    ⟨0, false, false, false, false⟩ := by decide

theorem one_pentameter_is_not_sonnet : verdict
    (rhymeFixture [some "a"]) = ⟨0, false, false, true, true⟩ := by decide

end SonnetForm
