import Mirath.Model
import Mirath.Settlement

/-!
A settlement ledger can contain a role's fixed share and a separate residue or
return increment. `canonical` aggregates those entries into one total for each
role, including the explicitly modelled public treasury destination.
-/

namespace Mirath

/-- Add every ledger entry assigned to a given role. -/
def allocationShare (r : Role) : Allocation Role → Rat
  | [] => 0
  | (role, q) :: xs => (if role = r then q else 0) + allocationShare r xs

/-- One entry for each role, in `Role.all` order, including zero shares. -/
def canonical (xs : Allocation Role) : Allocation Role :=
  Role.all.map fun r => (r, allocationShare r xs)

/-- Aggregating repeated roles neither creates nor loses any estate. -/
theorem total_canonical (xs : Allocation Role) : total (canonical xs) = total xs := by
  induction xs with
  | nil => simp [canonical, Role.all, allocationShare, total, Rat.zero_add]
  | cons x xs ih =>
      obtain ⟨role, q⟩ := x
      change total (canonical ((role, q) :: xs)) = q + total xs
      rw [← ih]
      cases role <;>
        simp [canonical, Role.all, allocationShare, total,
          Rat.add_assoc, Rat.add_comm, Rat.add_left_comm, Rat.add_zero]

/-- The public role enumeration has no duplicate destinations. -/
theorem role_all_nodup : Role.all.Nodup := by decide

/-- The public role enumeration contains every destination. -/
theorem role_mem_all (r : Role) : r ∈ Role.all := by
  cases r <;> simp [Role.all]

/-- Aggregation preserves each individual role's total. -/
theorem allocationShare_canonical (r : Role) (xs : Allocation Role) :
    allocationShare r (canonical xs) = allocationShare r xs := by
  cases r <;>
    simp [canonical, Role.all, allocationShare, Rat.add_zero, Rat.zero_add]

/-- Every role's total is nonnegative when all ledger entries are nonnegative. -/
theorem allocationShare_nonnegative (r : Role) (xs : Allocation Role)
    (h : Nonnegative xs) : 0 ≤ allocationShare r xs := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
      unfold allocationShare
      apply Rat.add_nonneg
      · split
        · exact h x (by simp)
        · exact Rat.le_refl
      · apply ih
        intro y hy
        exact h y (by simp [hy])

/-- A role with no ledger entries receives zero. -/
theorem allocationShare_zero_of_absent (r : Role) (xs : Allocation Role)
    (h : ∀ entry ∈ xs, entry.1 ≠ r) : allocationShare r xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : x.1 ≠ r := h x (by simp)
      have hxs : ∀ entry ∈ xs, entry.1 ≠ r := by
        intro y hy
        exact h y (by simp [hy])
      simp only [allocationShare, hx, ↓reduceIte, ih hxs, Rat.zero_add]

/-- Canonical aggregation preserves nonnegative allocations. -/
theorem canonical_nonnegative (xs : Allocation Role) (h : Nonnegative xs) :
    Nonnegative (canonical xs) := by
  intro x hx
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hx
  subst x
  exact allocationShare_nonnegative r xs h

end Mirath
