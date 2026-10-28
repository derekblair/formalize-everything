import BibleNumbers.Data

/-!
Exact differences of the encoded records. A missing row or an unstated field is
`none`, so these comparisons include differences in presence as well as in
numeric values. They are statements about the named editions in `Data`, not
claims that one edition exhausts a textual tradition.
-/

namespace BibleNumbers

/-- A coordinate of the comparison space, independent of a witness. -/
structure Cell where
  chapter : Chapter
  patriarch : Patriarch
  field : Field
  deriving DecidableEq, Repr

/-- Every coordinate, including patriarchs absent from a given chapter. -/
def allCells : List Cell :=
  chapters.flatMap fun ch => allPatriarchs.flatMap fun p =>
    fields.map fun f => ⟨ch, p, f⟩

theorem allCells_complete (c : Cell) : c ∈ allCells := by
  rcases c with ⟨ch, p, f⟩
  cases ch <;> cases p <;> cases f <;> decide

/-- Ordered coordinate list on which the two editions have unequal cells. -/
def divergence (v w : Variant) : List Cell :=
  allCells.filter fun c => decide
    (cell v c.chapter c.patriarch c.field ≠ cell w c.chapter c.patriarch c.field)

/-- Completeness and soundness hold for arbitrary editions and coordinates. -/
theorem divergence_complete (v w : Variant) (c : Cell) :
    c ∈ divergence v w ↔
      cell v c.chapter c.patriarch c.field ≠ cell w c.chapter c.patriarch c.field := by
  simp [divergence, allCells_complete]

theorem divergence_self (v : Variant) : divergence v v = [] := by
  simp [divergence]

theorem divergence_symmetric (v w : Variant) : divergence v w = divergence w v := by
  simp only [divergence, ne_comm]

/-- A positive or zero offset between two actually present numeric cells. -/
def FieldOffset (v w : Variant) (ch : Chapter) (p : Patriarch)
    (f : Field) (delta : Nat) : Prop :=
  (cell v ch p f).isSome = true ∧
    cell w ch p f = (cell v ch p f).map (fun n => n + delta)

instance (v w : Variant) (ch : Chapter) (p : Patriarch)
    (f : Field) (delta : Nat) : Decidable (FieldOffset v w ch p f delta) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A begetting-age increase with an equal remaining-year decrease. -/
def CompensatedOffset (v w : Variant) (ch : Chapter) (p : Patriarch)
    (delta : Nat) : Prop :=
  FieldOffset v w ch p .begetting delta ∧
    FieldOffset w v ch p .remaining delta

instance (v w : Variant) (ch : Chapter) (p : Patriarch)
    (delta : Nat) : Decidable (CompensatedOffset v w ch p delta) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Compact notation for an explicit group of cell coordinates. -/
def cellsAt (ch : Chapter) (p : Patriarch) (fs : List Field) : List Cell :=
  fs.map fun f => ⟨ch, p, f⟩

/-- Explicit coordinate lists for all fifteen unordered pairs. These lists do
not inspect the dataset: `divergence_eq_expected` checks each against it. -/
def expectedDivergence : Variant → Variant → List Cell
  | .mt, .sp | .sp, .mt =>
    cellsAt .gen5 .jared [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shem [.lifespan] ++
    cellsAt .gen11 .arpachshad [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shelah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .eber [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .peleg [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .reu [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .serug [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .nahor [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .terah [.lifespan]
  | .mt, .lxxSmith | .lxxSmith, .mt =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .arpachshad [.begetting, .remaining] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.begetting] ++
    cellsAt .gen11 .eber [.begetting, .remaining] ++
    cellsAt .gen11 .peleg [.begetting] ++
    cellsAt .gen11 .reu [.begetting] ++
    cellsAt .gen11 .serug [.begetting] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .mt, .lxxBrenton | .lxxBrenton, .mt =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .arpachshad [.begetting, .remaining] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.begetting, .remaining] ++
    cellsAt .gen11 .eber [.begetting, .remaining] ++
    cellsAt .gen11 .peleg [.begetting] ++
    cellsAt .gen11 .reu [.begetting] ++
    cellsAt .gen11 .serug [.begetting] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .mt, .lxxArp330 | .lxxArp330, .mt =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .arpachshad [.begetting, .remaining] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.begetting] ++
    cellsAt .gen11 .eber [.begetting, .remaining] ++
    cellsAt .gen11 .peleg [.begetting] ++
    cellsAt .gen11 .reu [.begetting] ++
    cellsAt .gen11 .serug [.begetting] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .mt, .lxxShelah330 | .lxxShelah330, .mt =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .arpachshad [.begetting, .remaining] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.begetting, .remaining] ++
    cellsAt .gen11 .eber [.begetting, .remaining] ++
    cellsAt .gen11 .peleg [.begetting] ++
    cellsAt .gen11 .reu [.begetting] ++
    cellsAt .gen11 .serug [.begetting] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .sp, .lxxSmith | .lxxSmith, .sp =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .jared [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shem [.lifespan] ++
    cellsAt .gen11 .arpachshad [.remaining, .lifespan] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.remaining, .lifespan] ++
    cellsAt .gen11 .eber [.remaining, .lifespan] ++
    cellsAt .gen11 .peleg [.remaining, .lifespan] ++
    cellsAt .gen11 .reu [.remaining, .lifespan] ++
    cellsAt .gen11 .serug [.remaining, .lifespan] ++
    cellsAt .gen11 .nahor [.remaining, .lifespan] ++
    cellsAt .gen11 .terah [.lifespan]
  | .sp, .lxxBrenton | .lxxBrenton, .sp =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .jared [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shem [.lifespan] ++
    cellsAt .gen11 .arpachshad [.remaining, .lifespan] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.remaining, .lifespan] ++
    cellsAt .gen11 .eber [.lifespan] ++
    cellsAt .gen11 .peleg [.remaining, .lifespan] ++
    cellsAt .gen11 .reu [.remaining, .lifespan] ++
    cellsAt .gen11 .serug [.remaining, .lifespan] ++
    cellsAt .gen11 .nahor [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .terah [.lifespan]
  | .sp, .lxxArp330 | .lxxArp330, .sp =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .jared [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shem [.lifespan] ++
    cellsAt .gen11 .arpachshad [.remaining, .lifespan] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.remaining, .lifespan] ++
    cellsAt .gen11 .eber [.remaining, .lifespan] ++
    cellsAt .gen11 .peleg [.remaining, .lifespan] ++
    cellsAt .gen11 .reu [.remaining, .lifespan] ++
    cellsAt .gen11 .serug [.remaining, .lifespan] ++
    cellsAt .gen11 .nahor [.remaining, .lifespan] ++
    cellsAt .gen11 .terah [.lifespan]
  | .sp, .lxxShelah330 | .lxxShelah330, .sp =>
    cellsAt .gen5 .adam [.begetting, .remaining] ++
    cellsAt .gen5 .seth [.begetting, .remaining] ++
    cellsAt .gen5 .enosh [.begetting, .remaining] ++
    cellsAt .gen5 .kenan [.begetting, .remaining] ++
    cellsAt .gen5 .mahalalel [.begetting, .remaining] ++
    cellsAt .gen5 .jared [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .enoch [.begetting, .remaining] ++
    cellsAt .gen5 .methuselah [.begetting, .remaining, .lifespan] ++
    cellsAt .gen5 .lamech [.begetting, .remaining, .lifespan] ++
    cellsAt .gen11 .shem [.lifespan] ++
    cellsAt .gen11 .arpachshad [.remaining, .lifespan] ++
    cellsAt .gen11 .kainan [.begetting, .remaining] ++
    cellsAt .gen11 .shelah [.remaining, .lifespan] ++
    cellsAt .gen11 .eber [.remaining, .lifespan] ++
    cellsAt .gen11 .peleg [.remaining, .lifespan] ++
    cellsAt .gen11 .reu [.remaining, .lifespan] ++
    cellsAt .gen11 .serug [.remaining, .lifespan] ++
    cellsAt .gen11 .nahor [.remaining, .lifespan] ++
    cellsAt .gen11 .terah [.lifespan]
  | .lxxSmith, .lxxBrenton | .lxxBrenton, .lxxSmith =>
    cellsAt .gen5 .methuselah [.begetting, .remaining] ++
    cellsAt .gen11 .arpachshad [.remaining] ++
    cellsAt .gen11 .shelah [.remaining] ++
    cellsAt .gen11 .eber [.remaining] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .lxxSmith, .lxxArp330 | .lxxArp330, .lxxSmith =>
    cellsAt .gen11 .arpachshad [.remaining]
  | .lxxSmith, .lxxShelah330 | .lxxShelah330, .lxxSmith =>
    cellsAt .gen11 .shelah [.remaining]
  | .lxxBrenton, .lxxArp330 | .lxxArp330, .lxxBrenton =>
    cellsAt .gen5 .methuselah [.begetting, .remaining] ++
    cellsAt .gen11 .arpachshad [.remaining] ++
    cellsAt .gen11 .shelah [.remaining] ++
    cellsAt .gen11 .eber [.remaining] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .lxxBrenton, .lxxShelah330 | .lxxShelah330, .lxxBrenton =>
    cellsAt .gen5 .methuselah [.begetting, .remaining] ++
    cellsAt .gen11 .arpachshad [.remaining] ++
    cellsAt .gen11 .eber [.remaining] ++
    cellsAt .gen11 .nahor [.begetting, .remaining]
  | .lxxArp330, .lxxShelah330 | .lxxShelah330, .lxxArp330 =>
    cellsAt .gen11 .arpachshad [.remaining] ++
    cellsAt .gen11 .shelah [.remaining]
  | _, _ => []

set_option maxRecDepth 4096 in
/-- All thirty ordered comparisons and all six diagonal comparisons are
kernel-computed; symmetry is explicit in the expected table. -/
theorem divergence_eq_expected (v w : Variant) :
    divergence v w = expectedDivergence v w := by
  cases v <;> cases w <;> decide

/-- Every listed cell differs, and every differing cell is listed. -/
theorem expectedDivergence_complete (v w : Variant) (c : Cell) :
    c ∈ expectedDivergence v w ↔
      cell v c.chapter c.patriarch c.field ≠ cell w c.chapter c.patriarch c.field := by
  rw [← divergence_eq_expected]
  exact divergence_complete v w c

/-- Cardinalities of the explicit lists, retaining missing-versus-stated cells. -/
def expectedDivergenceCount : Variant → Variant → Nat
  | .mt, .sp | .sp, .mt => 32
  | .mt, .lxxSmith | .lxxSmith, .mt => 27
  | .mt, .lxxBrenton | .lxxBrenton, .mt => 30
  | .mt, .lxxArp330 | .lxxArp330, .mt => 27
  | .mt, .lxxShelah330 | .lxxShelah330, .mt => 28
  | .sp, .lxxSmith | .lxxSmith, .sp => 39
  | .sp, .lxxBrenton | .lxxBrenton, .sp => 39
  | .sp, .lxxArp330 | .lxxArp330, .sp => 39
  | .sp, .lxxShelah330 | .lxxShelah330, .sp => 39
  | .lxxSmith, .lxxBrenton | .lxxBrenton, .lxxSmith => 7
  | .lxxSmith, .lxxArp330 | .lxxArp330, .lxxSmith => 1
  | .lxxSmith, .lxxShelah330 | .lxxShelah330, .lxxSmith => 1
  | .lxxBrenton, .lxxArp330 | .lxxArp330, .lxxBrenton => 7
  | .lxxBrenton, .lxxShelah330 | .lxxShelah330, .lxxBrenton => 6
  | .lxxArp330, .lxxShelah330 | .lxxShelah330, .lxxArp330 => 2
  | _, _ => 0

theorem divergence_counts (v w : Variant) :
    (divergence v w).length = expectedDivergenceCount v w := by
  rw [divergence_eq_expected]
  cases v <;> cases w <;> decide

/-- Exactly the six repeated hundred-year shifts in Genesis 5. -/
theorem gen5_lxx_hundred_exact (v : Variant) (p : Patriarch)
    (hv : witnessOf v = .lxx) :
    FieldOffset .mt v .gen5 p .begetting 100 ↔
      p ∈ [.adam, .seth, .enosh, .kenan, .mahalalel, .enoch] := by
  cases v <;> cases p <;> simp_all [witnessOf, FieldOffset, cell, row]

/-- Exactly the same six Genesis 5 shifts preserve begetting plus remainder. -/
theorem gen5_lxx_compensated_hundred_exact (v : Variant) (p : Patriarch)
    (hv : witnessOf v = .lxx) :
    CompensatedOffset .mt v .gen5 p 100 ↔
      p ∈ [.adam, .seth, .enosh, .kenan, .mahalalel, .enoch] := by
  cases v <;> cases p <;>
    simp_all [witnessOf, CompensatedOffset, FieldOffset, cell, row]

/-- Every encoded non-MT profile has exactly these six Genesis 11 +100 cells. -/
theorem gen11_hundred_exact (v : Variant) (p : Patriarch) (hv : v ≠ .mt) :
    FieldOffset .mt v .gen11 p .begetting 100 ↔
      p ∈ [.arpachshad, .shelah, .eber, .peleg, .reu, .serug] := by
  cases v <;> cases p <;> simp_all [FieldOffset, cell, row]

/-- SP compensates five of those six offsets; Eber is deliberately excluded. -/
theorem gen11_sp_compensated_hundred_exact (p : Patriarch) :
    CompensatedOffset .mt .sp .gen11 p 100 ↔
      p ∈ [.arpachshad, .shelah, .peleg, .reu, .serug] := by
  cases p <;> simp [CompensatedOffset, FieldOffset, cell, row]

/-- The encoded LXX Genesis 11 remaining years do not compensate a +100 shift. -/
theorem gen11_lxx_no_hundred_compensation (v : Variant) (p : Patriarch)
    (hv : witnessOf v = .lxx) :
    ¬ CompensatedOffset .mt v .gen11 p 100 := by
  cases v <;> cases p <;>
    simp_all [witnessOf, CompensatedOffset, FieldOffset, cell, row]

/-- Nahor is exactly the SP +50 and -50 exception to the hundred-year pattern. -/
theorem gen11_sp_compensated_fifty_exact (p : Patriarch) :
    CompensatedOffset .mt .sp .gen11 p 50 ↔ p = .nahor := by
  cases p <;> decide

/-- Smith's broad prose claim of SP -100 remainders has this explicit exception:
Eber's begetting increases by 100, but the remaining years decrease by 160. -/
theorem gen11_sp_eber_exception :
    FieldOffset .mt .sp .gen11 .eber .begetting 100 ∧
    FieldOffset .sp .mt .gen11 .eber .remaining 160 ∧
    ¬ CompensatedOffset .mt .sp .gen11 .eber 100 := by decide

/-- The differing Methuselah readings exhibit the separate +20 and -20 pattern. -/
theorem gen5_methuselah_twenty :
    CompensatedOffset .lxxBrenton .lxxSmith .gen5 .methuselah 20 := by decide

/-- Each of these profiles differs from Smith's primary table in one cell. -/
theorem single_cell_lxx_profiles :
    divergence .lxxSmith .lxxArp330 = [⟨.gen11, .arpachshad, .remaining⟩] ∧
    divergence .lxxSmith .lxxShelah330 = [⟨.gen11, .shelah, .remaining⟩] := by decide

end BibleNumbers
