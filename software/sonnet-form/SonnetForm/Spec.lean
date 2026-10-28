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
  | feminineEnding
  | pyrrhicSubstitution
  | spondaicSubstitution
  | unstressedElision
  deriving Repr, BEq, DecidableEq

def licenseName : License → String
  | .initialTrochaicInversion => "INITIAL_TROCHAIC_INVERSION"
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

/-- Trochaic inversion is restricted to foot zero. Pyrrhics and spondees
are allowed at any foot, subject to the shared two-substitution budget. -/
def allowedFoot (i : Nat) (f : Bool × Bool) : Bool :=
  isIamb f || isPyrrhic f || isSpondee f || (i == 0 && isTrochee f)

/-- Strict meter admits neither substitutions nor elisions nor extra syllables. -/
def scanStrict (s : Scan) : Bool :=
  s.elision == none && s.stress == pentameter

/-- MD-METER-BUDGET: exactly five feet, at least three of them iambic.
A feminine ending and a single annotated unstressed elision can combine with
these substitutions. No deletion can turn a tetrameter into a pentameter. -/
def scanLicensed (s : Scan) : Bool :=
  let core := meterCore s
  let fs := feet core
  elisionValid s && core.length == 10 &&
    (fs.zipIdx.all fun (f, i) => allowedFoot i f) &&
    (fs.filter fun f => !isIamb f).length ≤ 2

/-- Each license has its own executable predicate. The enclosing licensed
check must succeed, so occurrence in a failed scan is not a license grant. -/
def initialTrochaicInversion (s : Scan) : Bool :=
  scanLicensed s && (feet (meterCore s)).head? == some (true, false)

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
  | .feminineEnding => feminineEnding
  | .pyrrhicSubstitution => pyrrhicSubstitution
  | .spondaicSubstitution => spondaicSubstitution
  | .unstressedElision => unstressedElision

def allLicenses : List License :=
  [.initialTrochaicInversion, .feminineEnding, .pyrrhicSubstitution,
   .spondaicSubstitution, .unstressedElision]

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

theorem medial_trochee_fails : scanLicensed
    ⟨[false, true, true, false, false, true, false, true, false, true], none⟩ = false := by
  decide

theorem three_substitutions_fail : scanLicensed
    ⟨[false, false, true, true, false, false, false, true, false, true], none⟩ = false := by
  decide

end SonnetForm
