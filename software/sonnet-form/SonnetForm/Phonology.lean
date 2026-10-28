import SonnetForm.Spec

/-!
# Explicit stress annotations and a deterministic realization

A fixed syllable is `some false` (unstressed) or `some true` (stressed).
`none` means *a known syllable with contextually flexible stress*, not an unknown
word or an unknown syllable count. An unannotated line has no scans instead.

MD-MONOSYLLABLE-FLEX permits the external annotator to mark known monosyllables
flexible. MD-REALIZATION chooses the alternating iambic value at flexible
positions. Fixed multisyllabic stresses are never overwritten. This is a
pattern-feasibility model, not a prediction of a uniquely correct performance.
-/

namespace SonnetForm

abbrev StressMask := Option Bool

/-- At fixed positions preserve the annotation; at flexible positions use the
alternating weak/strong template. The eleventh position is therefore weak. -/
def realizeFrom (strong : Bool) : List StressMask → List Bool
  | [] => []
  | m :: ms => m.getD strong :: realizeFrom (!strong) ms

def realizeStress (masks : List StressMask) : List Bool :=
  realizeFrom false masks

abbrev realize := realizeStress

def maskCompatible (m : StressMask) (stress : Bool) : Bool :=
  match m with
  | none => true
  | some fixed => fixed == stress

def masksCompatible : List StressMask → List Bool → Bool
  | [], [] => true
  | m :: ms, x :: xs => maskCompatible m x && masksCompatible ms xs
  | _, _ => false

/-- The canonical realization satisfies every supplied fixed stress. -/
theorem realizeFrom_compatible (strong : Bool) (masks : List StressMask) :
    masksCompatible masks (realizeFrom strong masks) = true := by
  induction masks generalizing strong with
  | nil => rfl
  | cons m ms ih =>
    cases m <;> simp [realizeFrom, masksCompatible, maskCompatible, ih]

theorem realizeStress_compatible (masks : List StressMask) :
    masksCompatible masks (realizeStress masks) = true :=
  realizeFrom_compatible false masks

theorem realizeFrom_length (strong : Bool) (masks : List StressMask) :
    (realizeFrom strong masks).length = masks.length := by
  induction masks generalizing strong with
  | nil => rfl
  | cons m ms ih => simp [realizeFrom, ih]

theorem realizeStress_length (masks : List StressMask) :
    (realizeStress masks).length = masks.length :=
  realizeFrom_length false masks

/-- Baseline reading, with no elision. -/
def scanFromMasks (masks : List StressMask) : Scan :=
  ⟨realizeStress masks, none⟩

/-- Delete an annotated weak syllable, realize the remaining positions, and
restore that weak syllable in the raw stress list so the Spec's elision operation
performs the deletion itself. Used only after `eligibleElision` succeeds. -/
def elidedScanFromMasks (masks : List StressMask) (i : Nat) : Scan :=
  let shortened := masks.take i ++ masks.drop (i + 1)
  let realized := realizeStress shortened
  ⟨realized.take i ++ false :: realized.drop i, some i⟩

/-- A supplied eligible site must actually index a fixed unstressed syllable.
Flexible stress is insufficient evidence for deleting a syllable. The textual
justification for an eligible index is supplied by the pronunciation model. -/
def eligibleElision (masks : List StressMask) (i : Nat) : Bool :=
  masks[i]? == some (some false)

/-- Finite, explicit readings: baseline first, then each eligible one-syllable
elision in the supplied order. Failed readings remain available for diagnosis.
Empty masks yield no readings, so incomplete lexical coverage cannot pass. -/
def scansFromMasks (masks : List StressMask) (eligibleElisions : List Nat := []) : List Scan :=
  if masks.isEmpty then [] else
    scanFromMasks masks ::
      ((eligibleElisions.filter (eligibleElision masks)).map (elidedScanFromMasks masks))

abbrev readingsToScans (masks : List StressMask) : List Scan := scansFromMasks masks

/-- Convenience constructor that retains the original text verbatim. -/
def lineFromMasks (text : String) (rhyme : Option String)
    (masks : List StressMask) (eligibleElisions : List Nat := []) : Line :=
  ⟨text, rhyme, scansFromMasks masks eligibleElisions⟩

theorem flexible_pentameter_passes :
    lineMeterStrict (lineFromMasks "" none (List.replicate 10 none)) = true := by decide

theorem flexible_tetrameter_fails :
    lineMeterLicensed (lineFromMasks "" none (List.replicate 8 none)) = false := by decide

theorem fixed_medial_inversion_not_overwritten :
    lineMeterLicensed (lineFromMasks "" none
      [none, none, some true, some false, none, none, none, none, none, none]) = false := by
  decide

theorem fixed_initial_inversion_licensed :
    lineLicenses (lineFromMasks "" none
      [some true, some false, none, none, none, none, none, none, none, none]) =
        [.initialTrochaicInversion] := by
  decide

theorem unknown_annotation_fails :
    lineMeterLicensed (lineFromMasks "" none []) = false := by decide

/-- Two surplus syllables become a pentameter with both the indexed elision
and a feminine ending; neither alone suffices for this twelve-syllable input. -/
theorem supplied_weak_elision_licenses :
    lineMeterLicensed (lineFromMasks "" none
      (some false :: List.replicate 11 none) [0]) = true := by decide

theorem flexible_elision_rejected :
    (scansFromMasks (List.replicate 12 none) [0]).length = 1 := by decide

theorem stressed_elision_rejected :
    (scansFromMasks (some true :: List.replicate 11 none) [0]).length = 1 := by decide

theorem out_of_range_elision_rejected :
    (scansFromMasks [some false] [1]).length = 1 := by decide

end SonnetForm
