import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

open Function Equiv

namespace RudinRCA.Chapter13Scratch

universe u v

variable {E : Type u} {V : Type v} [Fintype E]

/-- Counting individual interval indices, rather than their endpoint pairs, preserves multiplicity. -/
theorem balanced_exists_successor [DecidableEq V] (initial terminal : E → V)
    (hbalanced : ∀ v, Fintype.card {e // initial e = v} =
      Fintype.card {e // terminal e = v}) :
    ∃ σ : Equiv.Perm E, ∀ e, terminal e = initial (σ e) := by
  let fibers : ∀ v, {e // terminal e = v} ≃ {e // initial e = v} :=
    fun v => Fintype.equivOfCardEq (hbalanced v).symm
  exact ⟨Equiv.ofFiberEquiv fibers, fun e => (Equiv.ofFiberEquiv_map fibers e).symm⟩

/-- A cyclic successor on a nonempty finite interval of indices. -/
def cycleNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

noncomputable def permutationOrbit (σ : Equiv.Perm E) (e : E) : Finset E := by
  classical
  exact Finset.univ.filter (σ.SameCycle e)

@[simp] theorem mem_permutationOrbit (σ : Equiv.Perm E) (e x : E) :
    x ∈ permutationOrbit σ e ↔ σ.SameCycle e x := by
  classical
  simp [permutationOrbit]

theorem permutationOrbit_nonempty (σ : Equiv.Perm E) (e : E) :
    (permutationOrbit σ e).Nonempty := by
  exact ⟨e, (mem_permutationOrbit σ e e).mpr Equiv.Perm.SameCycle.rfl⟩

theorem permutationOrbit_eq_of_sameCycle (σ : Equiv.Perm E) {e f : E}
    (h : σ.SameCycle e f) : permutationOrbit σ e = permutationOrbit σ f := by
  ext x
  simp only [mem_permutationOrbit]
  exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩

theorem isCycleOn_permutationOrbit (σ : Equiv.Perm E) (e : E) :
    σ.IsCycleOn (permutationOrbit σ e : Set E) := by
  refine ⟨σ.bijOn ?_, ?_⟩
  · intro x
    simp only [Finset.mem_coe, mem_permutationOrbit, Equiv.Perm.sameCycle_apply_right]
  · intro x hx y hy
    exact (mem_permutationOrbit σ e x |>.mp hx).symm.trans
      (mem_permutationOrbit σ e y |>.mp hy)

/-- A finite permutation orbit is explicitly enumerated without repetition, with cyclic successor. -/
theorem enumerate_permutationOrbit (σ : Equiv.Perm E) (a : E) :
    ∃ hpos : 0 < (permutationOrbit σ a).card,
      ∃ edge : Fin (permutationOrbit σ a).card → E,
        Injective edge ∧
        (∀ x, x ∈ permutationOrbit σ a ↔ ∃ i, edge i = x) ∧
        ∀ i, σ (edge i) = edge (cycleNext hpos i) := by
  classical
  let s := permutationOrbit σ a
  have ha : a ∈ s := (mem_permutationOrbit σ a a).mpr Equiv.Perm.SameCycle.rfl
  have hs : σ.IsCycleOn (s : Set E) := isCycleOn_permutationOrbit σ a
  have hp : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  let edge : Fin s.card → E := fun i => (σ ^ (i : ℕ)) a
  refine ⟨hp, edge, ?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hmod := (hs.pow_apply_eq_pow_apply ha).mp hij
    change (i : ℕ) % s.card = (j : ℕ) % s.card at hmod
    rw [Nat.mod_eq_of_lt (show (i : ℕ) < s.card from i.isLt),
      Nat.mod_eq_of_lt (show (j : ℕ) < s.card from j.isLt)] at hmod
    exact hmod
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi, heq⟩ := hs.exists_pow_eq ha hx
      exact ⟨⟨i, hi⟩, heq⟩
    · rintro ⟨i, rfl⟩
      exact hs.1.mapsTo.perm_pow _ ha
  · intro i
    change σ ((σ ^ (i : ℕ)) a) = (σ ^ (((i : ℕ) + 1) % s.card)) a
    have heq : (σ ^ (((i : ℕ) + 1) % s.card)) a = (σ ^ ((i : ℕ) + 1)) a :=
      (hs.pow_apply_eq_pow_apply ha).mpr (Nat.mod_modEq _ _)
    rw [heq, pow_succ', Equiv.Perm.mul_apply]

/-- Rudin RCA 13.4: a balanced finite family of directed intervals decomposes into finitely
many closed polygonal edge sequences. Each supplied index occurs in exactly one component,
and each component's enumeration is injective and covers its support.

Take `V = ℂ` to obtain the printed result for oriented complex line intervals. Distinct indices
may have the same endpoints, so the theorem retains interval multiplicities. -/
theorem balanced_closed_cycle_partition [DecidableEq E] [DecidableEq V]
    (initial terminal : E → V)
    (hbalanced : ∀ v, Fintype.card {e // initial e = v} =
      Fintype.card {e // terminal e = v}) :
    ∃ cycles : Finset (Finset E),
      (∀ e : E, ∃! s : Finset E, s ∈ cycles ∧ e ∈ s) ∧
      ∀ s ∈ cycles, ∃ hpos : 0 < s.card, ∃ edge : Fin s.card → E,
        Injective edge ∧ (∀ e, e ∈ s ↔ ∃ i, edge i = e) ∧
        ∀ i, terminal (edge i) = initial (edge (cycleNext hpos i)) := by
  classical
  obtain ⟨σ, hσ⟩ := balanced_exists_successor initial terminal hbalanced
  let cycles := Finset.univ.image (permutationOrbit σ)
  refine ⟨cycles, ?_, ?_⟩
  · intro e
    refine ⟨permutationOrbit σ e, ⟨?_,
      (mem_permutationOrbit σ e e).mpr Equiv.Perm.SameCycle.rfl⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
    · intro s hs
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs.1
      exact permutationOrbit_eq_of_sameCycle σ ((mem_permutationOrbit σ a e).mp hs.2)
  · intro s hs
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hpos, edge, hinj, hcover, hnext⟩ := enumerate_permutationOrbit σ a
    refine ⟨hpos, edge, hinj, hcover, ?_⟩
    intro i
    rw [hσ, hnext]

#print axioms balanced_exists_successor
#print axioms mem_permutationOrbit
#print axioms permutationOrbit_nonempty
#print axioms permutationOrbit_eq_of_sameCycle
#print axioms isCycleOn_permutationOrbit
#print axioms enumerate_permutationOrbit
#print axioms balanced_closed_cycle_partition

end RudinRCA.Chapter13Scratch
