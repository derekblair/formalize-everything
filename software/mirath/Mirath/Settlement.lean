import Init.Data.Rat.Lemmas
import Init.Data.List.Lemmas

/-!
Rational settlement, independent of the kinship schedule. An allocation records
role totals, not per-person shares; repeated roles are additive. `settle` uses
proportional 'awl, residuary weights, then proportional radd. The calling model
supplies the legally eligible weights and checks `SettlementValid`.
-/

namespace Mirath

abbrev Allocation (α : Type) := List (α × Rat)

/-- Sum of all role shares, including repeated-role increments. -/
def total {α : Type} : Allocation α → Rat
  | [] => 0
  | (_, q) :: xs => q + total xs

/-- Distribute `amount` proportionally to the supplied weights. -/
def scale {α : Type} (amount : Rat) (weights : Allocation α) : Allocation α :=
  weights.map fun (role, weight) => (role, (amount / total weights) * weight)

/-- A missing radd recipient is outside the settlement domain, not an invented
beneficiary. This condition inspects the inputs, not the output or its sum. -/
def SettlementValid {α : Type} (fixed residuary returns : Allocation α) : Prop :=
  total fixed < 1 → total residuary = 0 → total returns ≠ 0

/-- Total executable rational settlement. On inputs outside `SettlementValid`,
the function still terminates, but conservation is not promised. -/
def settle {α : Type} (fixed residuary returns : Allocation α) : Allocation α :=
  if 1 < total fixed then scale 1 fixed
  else if total residuary ≠ 0 then fixed ++ scale (1 - total fixed) residuary
  else if total fixed = 1 then fixed
  else fixed ++ scale (1 - total fixed) returns


theorem total_append {α : Type} (xs ys : Allocation α) :
    total (xs ++ ys) = total xs + total ys := by
  induction xs with
  | nil => simp only [List.nil_append, total, Rat.zero_add]
  | cons x xs ih =>
      simp only [List.cons_append, total, ih, Rat.add_assoc]

theorem total_map_mul {α : Type} (xs : Allocation α) (factor : Rat) :
    total (xs.map fun (a, q) => (a, factor * q)) = factor * total xs := by
  induction xs with
  | nil => simp only [List.map_nil, total, Rat.mul_zero]
  | cons x xs ih =>
      simp only [List.map_cons, total, ih, Rat.mul_add]

theorem total_scale {α : Type} (amount : Rat) (weights : Allocation α)
    (h : total weights ≠ 0) : total (scale amount weights) = amount := by
  unfold scale
  rw [total_map_mul, Rat.div_mul_cancel h]

theorem total_settle {α : Type} (fixed residuary returns : Allocation α)
    (h : SettlementValid fixed residuary returns) :
    total (settle fixed residuary returns) = 1 := by
  unfold settle
  split
  next hawl =>
    apply total_scale
    intro hzero
    rw [hzero] at hawl
    exact (by decide : ¬(1 : Rat) < 0) hawl
  next hawl =>
    split
    next hres =>
      rw [total_append, total_scale _ _ hres, Rat.add_comm, Rat.sub_add_cancel]
    next hres =>
      split
      next hfull => exact hfull
      next hfull =>
        have hlt : total fixed < 1 := Rat.lt_of_le_of_ne (Rat.not_lt.mp hawl) hfull
        have hreturns : total returns ≠ 0 := h hlt (by simpa using hres)
        rw [total_append, total_scale _ _ hreturns, Rat.add_comm, Rat.sub_add_cancel]

/-- Every recorded share is nonnegative. -/
def Nonnegative {α : Type} (xs : Allocation α) : Prop :=
  ∀ entry ∈ xs, 0 ≤ entry.2

theorem total_nonnegative {α : Type} {xs : Allocation α}
    (h : Nonnegative xs) : 0 ≤ total xs := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
    apply Rat.add_nonneg
    · exact h x (by simp)
    · apply ih
      intro y hy
      exact h y (by simp [hy])

theorem nonnegative_append {α : Type} {xs ys : Allocation α}
    (hx : Nonnegative xs) (hy : Nonnegative ys) : Nonnegative (xs ++ ys) := by
  intro x h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · exact hy x h

theorem div_nonnegative {a b : Rat} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ a / b := by
  by_cases hz : b = 0
  · subst b
    simp [Rat.div_def]
  · rw [Rat.div_def]
    apply Rat.mul_nonneg ha
    apply Rat.le_of_lt
    apply Rat.inv_pos.mpr
    exact Rat.lt_of_le_of_ne hb (Ne.symm hz)

theorem scale_nonnegative {α : Type} (amount : Rat) (weights : Allocation α)
    (ha : 0 ≤ amount) (hw : Nonnegative weights) :
    Nonnegative (scale amount weights) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
  subst x
  apply Rat.mul_nonneg
  · exact div_nonnegative ha (total_nonnegative hw)
  · exact hw y hy

/-- Nonnegative inputs give a nonnegative distribution, even when no radd
recipient exists. Conservation separately requires `SettlementValid`. -/
theorem settle_nonnegative {α : Type} (fixed residuary returns : Allocation α)
    (hf : Nonnegative fixed) (hr : Nonnegative residuary)
    (ht : Nonnegative returns) : Nonnegative (settle fixed residuary returns) := by
  unfold settle
  split
  next hawl => exact scale_nonnegative 1 fixed (by decide) hf
  next hawl =>
    have hleft : 0 ≤ 1 - total fixed :=
      (Rat.le_iff_sub_nonneg _ _).mp (Rat.not_lt.mp hawl)
    split
    next hres => exact nonnegative_append hf (scale_nonnegative _ _ hleft hr)
    next hres =>
      split
      next hfull => exact hf
      next hfull => exact nonnegative_append hf (scale_nonnegative _ _ hleft ht)

end Mirath
