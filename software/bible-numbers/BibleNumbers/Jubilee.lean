import Std

/-!
Leviticus 25:3–4, 8, 10–11; see `JUBILEE-SOURCES.md`.

All arithmetic uses a common epoch and a continuous seven-year sabbatical
rhythm. A *cycle boundary* is an elapsed duration, not necessarily the numbered
jubilee year: the latter starts at year 50 in both readings. Keeping these
coordinates separate prevents the 49-year reading from relabeling year 49 as
the text's fiftieth year.
-/
namespace BibleNumbers.Jubilee

/-- The two readings requested in milestone 1; neither is selected as historical fact. -/
inductive Reading where
  | fortyNine
  | fifty
  deriving DecidableEq, Repr

/-- Period between successive jubilees, not the label of the first jubilee. -/
def period : Reading → Nat
  | .fortyNine => 49
  | .fifty => 50

/-- Positive numbered years divisible by seven. Year zero is only the epoch. -/
def IsSabbatical (year : Nat) : Prop := 0 < year ∧ year % 7 = 0

instance (year : Nat) : Decidable (IsSabbatical year) := inferInstanceAs
  (Decidable (0 < year ∧ year % 7 = 0))

/-- Count actual sabbatical years in the interval `(start, start + span]`.
Each recursion step inspects its newly included year. -/
def sabbaticalCount (start : Nat) : Nat → Nat
  | 0 => 0
  | span + 1 => sabbaticalCount start span +
      if IsSabbatical (start + span + 1) then 1 else 0

/-- A closed formula proved from year-by-year counting, for every span and epoch offset. -/
theorem sabbaticalCount_eq (start span : Nat) :
    sabbaticalCount start span = (start + span) / 7 - start / 7 := by
  induction span with
  | zero => simp [sabbaticalCount]
  | succ span ih =>
    simp only [sabbaticalCount, ih, IsSabbatical]
    have hp : 0 < start + span + 1 := by omega
    by_cases hm : (start + span + 1) % 7 = 0 <;> simp only [hp, hm, and_self, ↓reduceIte, and_false] <;> omega

/-- At the common epoch, every seven completed years contribute one sabbatical year. -/
theorem sabbaticalCount_from_epoch (span : Nat) :
    sabbaticalCount 0 span = span / 7 := by
  simpa using sabbaticalCount_eq 0 span

/-- The elapsed duration of `cycles` completed jubilee periods. -/
def boundary (reading : Reading) (cycles : Nat) : Nat := period reading * cycles

/-- Sabbatical-year counts over any number of whole periods, for either reading. -/
theorem sabbaticalCount_periods (reading : Reading) (cycles : Nat) :
    sabbaticalCount 0 (boundary reading cycles) = period reading * cycles / 7 := by
  exact sabbaticalCount_from_epoch _

theorem sabbaticalCount_fortyNine (cycles : Nat) :
    sabbaticalCount 0 (boundary .fortyNine cycles) = 7 * cycles := by
  rw [sabbaticalCount_periods]
  simp only [period]
  omega

theorem sabbaticalCount_fifty (cycles : Nat) :
    sabbaticalCount 0 (boundary .fifty cycles) = 7 * cycles + cycles / 7 := by
  rw [sabbaticalCount_periods]
  simp only [period]
  omega

/-- Seven sabbaticals in every complete 49-year period, even away from the epoch. -/
theorem sabbaticalCount_fortyNine_span (start cycles : Nat) :
    sabbaticalCount start (49 * cycles) = 7 * cycles := by
  rw [sabbaticalCount_eq]
  omega

/-- Under the continuous seven-year rhythm, a 50-year span has seven or eight
sabbaticals; the extra one occurs precisely when its first year is sabbatical. -/
theorem sabbaticalCount_fifty_span (start : Nat) :
    sabbaticalCount start 50 = 7 + if (start + 1) % 7 = 0 then 1 else 0 := by
  rw [sabbaticalCount_eq]
  split <;> omega

/-- Every 49-year boundary has the same phase in the seven-year rhythm. -/
theorem boundary_fortyNine_phase (cycles : Nat) :
    boundary .fortyNine cycles % 7 = 0 := by
  simp only [boundary, period]
  omega

/-- A full 50-year period moves forward one place in the seven-year rhythm. -/
theorem boundary_fifty_phase (cycles : Nat) :
    boundary .fifty cycles % 7 = cycles % 7 := by
  simp only [boundary, period]
  omega

theorem boundary_fifty_drift (cycles : Nat) :
    boundary .fifty (cycles + 1) % 7 = (boundary .fifty cycles % 7 + 1) % 7 := by
  rw [boundary_fifty_phase, boundary_fifty_phase]
  omega

theorem boundary_fortyNine_sabbatical (cycles : Nat) (h : 0 < cycles) :
    IsSabbatical (boundary .fortyNine cycles) := by
  constructor
  · simp only [boundary, period]; omega
  · exact boundary_fortyNine_phase cycles

theorem boundary_fifty_sabbatical_iff (cycles : Nat) :
    IsSabbatical (boundary .fifty cycles) ↔ 0 < cycles ∧ cycles % 7 = 0 := by
  simp only [IsSabbatical, boundary, period]
  omega

/-- Numbered jubilees: year 50 is common to both readings; `index` counts
additional jubilees after that first one. -/
def jubileeYear (reading : Reading) (index : Nat) : Nat := 50 + period reading * index

theorem first_jubilee (reading : Reading) : jubileeYear reading 0 = 50 := by
  simp [jubileeYear]

/-- In the overlapping reading each jubilee stays immediately after a sabbatical. -/
theorem jubileeYear_fortyNine_phase (index : Nat) :
    jubileeYear .fortyNine index % 7 = 1 := by
  simp only [jubileeYear, period]
  omega

theorem jubileeYear_fortyNine_after_sabbatical (index : Nat) :
    IsSabbatical (jubileeYear .fortyNine index - 1) := by
  simp only [IsSabbatical, jubileeYear, period]
  omega

/-- In the full-period reading the first jubilee has phase one, then drifts by one. -/
theorem jubileeYear_fifty_phase (index : Nat) :
    jubileeYear .fifty index % 7 = (index + 1) % 7 := by
  simp only [jubileeYear, period]
  omega

theorem jubileeYear_fifty_sabbatical_iff (index : Nat) :
    IsSabbatical (jubileeYear .fifty index) ↔ (index + 1) % 7 = 0 := by
  simp only [IsSabbatical, jubileeYear, period]
  omega

/-- Positive elapsed durations comprising a whole number of both period lengths. -/
def Realignment (elapsed : Nat) : Prop := 0 < elapsed ∧ 49 ∣ elapsed ∧ 50 ∣ elapsed

/-- The lcm computation is reduced by the Lean kernel. -/
theorem period_lcm : Nat.lcm 49 50 = 2450 := by decide

theorem period_products : (50 : Nat) * 49 = 2450 ∧ (49 : Nat) * 50 = 2450 := by decide

/-- All common period multiples, not just the first checked example. -/
theorem common_multiple_iff (elapsed : Nat) :
    (49 ∣ elapsed ∧ 50 ∣ elapsed) ↔ 2450 ∣ elapsed := by
  rw [← Nat.lcm_dvd_iff, period_lcm]

theorem realignment_iff (elapsed : Nat) :
    Realignment elapsed ↔ 0 < elapsed ∧ 2450 ∣ elapsed := by
  simp only [Realignment, common_multiple_iff]

theorem realignment_2450 : Realignment 2450 := by
  rw [realignment_iff]
  exact ⟨by decide, Nat.dvd_refl _⟩

/-- No smaller positive duration realigns the two cycles. -/
theorem realignment_minimal (elapsed : Nat) (h : Realignment elapsed) :
    2450 ≤ elapsed := by
  have h' := (realignment_iff elapsed).mp h
  exact Nat.le_of_dvd h'.1 h'.2

theorem no_earlier_realignment (elapsed : Nat) (h : 0 < elapsed) (hlt : elapsed < 2450) :
    ¬ Realignment elapsed := by
  intro hr
  have := realignment_minimal elapsed hr
  omega

/-- At the common duration, 50 short periods equal 49 long periods. -/
theorem boundary_coincidence : boundary .fortyNine 50 = 2450 ∧ boundary .fifty 49 = 2450 := by
  decide

/-- With the actual first jubilee labeled year 50, the next shared label is
2500, a gap of 2450 years; it is not mislabeled year 2450. -/
theorem jubileeYear_next_coincidence :
    jubileeYear .fortyNine 50 = 2500 ∧ jubileeYear .fifty 49 = 2500 := by decide

/-- Every coincidence of jubilee labels after their common first one has at
least the 2450-year gap proved above. -/
theorem jubileeYear_coincidence_minimal (i j : Nat) (hi : 0 < i)
    (h : jubileeYear .fortyNine i = jubileeYear .fifty j) :
    2500 ≤ jubileeYear .fortyNine i := by
  have heq : 49 * i = 50 * j := by simpa [jubileeYear, period] using h
  have hr : Realignment (49 * i) := by
    refine ⟨by omega, ⟨i, rfl⟩, ⟨j, heq⟩⟩
  have := realignment_minimal (49 * i) hr
  simp only [jubileeYear, period]
  omega

end BibleNumbers.Jubilee
