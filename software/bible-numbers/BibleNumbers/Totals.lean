import BibleNumbers.Data

/-!
Elapsed-year sums of the encoded genealogies. These are conditional arithmetic
chronologies: consecutive named begettings are treated as a chain, without gaps.
Neither the continuity assumption nor a historical date is proved here.

Genesis 5 stops at Noah's birth, then adds his sourced age at the Flood (600),
not the 500-year entry introducing his sons. Genesis 11 starts two years after
the Flood at Arpachshad's birth; Shem's 100 years are not counted again.
Terah's printed 70 and the separate inferred 130-year endpoint are parameters.
-/

namespace BibleNumbers

open Chapter Patriarch Field Variant

/-- Fail closed if any requested begetting cell has no verified observation. -/
def begettingSum (v : Variant) (c : Chapter) : List Patriarch → Option Nat
  | [] => some 0
  | p :: ps => do
    let n ← cell v c p .begetting
    let rest ← begettingSum v c ps
    pure (n + rest)

/-- A missing observation anywhere in the requested chain invalidates the
entire sum; the calculation cannot silently discard an unknown age. -/
theorem begettingSum_missing (v : Variant) (c : Chapter) (ps : List Patriarch)
    (p : Patriarch) (hp : p ∈ ps) (missing : cell v c p .begetting = none) :
    begettingSum v c ps = none := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rcases List.mem_cons.mp hp with heq | hmem
    · subst q
      simp [begettingSum, missing]
    · simp [begettingSum, ih hmem]

def preFloodPath : List Patriarch :=
  [.adam, .seth, .enosh, .kenan, .mahalalel, .jared, .enoch,
   .methuselah, .lamech]

/-- The final Terah step is deliberately separate. Kainan is present only in
the named LXX profiles; absent MT/SP entries are never counted as zero ages. -/
def postFloodPath (v : Variant) : List Patriarch :=
  [.arpachshad] ++ (match v with
    | .mt | .sp => []
    | _ => [.kainan]) ++
  [.shelah, .eber, .peleg, .reu, .serug, .nahor]

inductive TerahEndpoint where
  /-- Use the observed Genesis 11:26 age70 as the terminal begetting step. -/
  | listed70
  /-- Conditional age130 scenario discussed by Smith Table4 notes D–F.
  This is inferred chronology, not a replacement for the witness's age70 cell;
  for SP it is explicitly the counterfactual corrected-age scenario. -/
  | inferred130
  deriving DecidableEq, BEq, Repr

def terminalAge (v : Variant) : TerahEndpoint → Option Nat
  | .listed70 => cell v .gen11 .terah .begetting
  | .inferred130 => some 130

def adamToFlood (v : Variant) : Option Nat := do
  let n ← begettingSum v .gen5 preFloodPath
  pure (n + noahFloodAge v)

def floodToAbraham (v : Variant) (endpoint : TerahEndpoint) : Option Nat := do
  let n ← begettingSum v .gen11 (postFloodPath v)
  let t ← terminalAge v endpoint
  pure (floodToArpachshad v + n + t)

def adamToAbraham (v : Variant) (endpoint : TerahEndpoint) : Option Nat := do
  let a ← adamToFlood v
  let b ← floodToAbraham v endpoint
  pure (a + b)

theorem noah_flood_age (v : Variant) : noahFloodAge v = 600 := by
  cases v <;> decide

theorem flood_to_arpachshad (v : Variant) : floodToArpachshad v = 2 := by
  cases v <;> decide

theorem terah_printed_age (v : Variant) : terminalAge v .listed70 = some 70 := by
  cases v <;> decide

/-- Every pre-Flood chain closes on sourced observations. -/
theorem adam_to_flood_totals (v : Variant) : adamToFlood v = some (match v with
    | .mt => 1656
    | .sp => 1307
    | .lxxBrenton => 2242
    | .lxxSmith | .lxxArp330 | .lxxShelah330 => 2262) := by
  cases v <;> decide

theorem flood_to_abraham_listed_totals (v : Variant) :
    floodToAbraham v .listed70 = some (match v with
    | .mt => 292
    | .sp => 942
    | .lxxBrenton => 1172
    | .lxxSmith | .lxxArp330 | .lxxShelah330 => 1072) := by
  cases v <;> decide

theorem flood_to_abraham_inferred_totals (v : Variant) :
    floodToAbraham v .inferred130 = some (match v with
    | .mt => 352
    | .sp => 1002
    | .lxxBrenton => 1232
    | .lxxSmith | .lxxArp330 | .lxxShelah330 => 1132) := by
  cases v <;> decide

theorem endpoint_adds_sixty (v : Variant) :
    floodToAbraham v .inferred130 = (floodToAbraham v .listed70).map (· + 60) := by
  cases v <;> decide

theorem adam_to_abraham_listed_totals (v : Variant) :
    adamToAbraham v .listed70 = some (match v with
    | .mt => 1948
    | .sp => 2249
    | .lxxBrenton => 3414
    | .lxxSmith | .lxxArp330 | .lxxShelah330 => 3334) := by
  cases v <;> decide

theorem adam_to_abraham_inferred_totals (v : Variant) :
    adamToAbraham v .inferred130 = some (match v with
    | .mt => 2008
    | .sp => 2309
    | .lxxBrenton => 3474
    | .lxxSmith | .lxxArp330 | .lxxShelah330 => 3394) := by
  cases v <;> decide

/-- Smith Table1's2256 and Table4's3388 use a different reconstructed Lamech
age182. The encoded Table2 age188 gives a six-year difference. -/
theorem smith_table2_differs_from_reconstruction :
    adamToFlood .lxxSmith = some (2256 + 6) ∧
    adamToAbraham .lxxSmith .inferred130 = some (3388 + 6) := by decide

/-- A structurally absent Kainan is an error if explicitly requested as a
summand, never a silent zero. The MT path instead explicitly omits that row. -/
theorem absent_cell_not_zero :
    begettingSum .mt .gen11 [.kainan] = none ∧
    begettingSum .sp .gen11 [.kainan] = none := by decide

end BibleNumbers
