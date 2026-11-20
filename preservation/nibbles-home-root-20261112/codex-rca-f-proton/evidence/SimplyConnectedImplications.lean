import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Basic

/-!
Scratch development of Rudin RCA 13.11 (a) implies (b).
The hypothesis is an actual homeomorphism onto the open unit disc.
This file does not assert the remaining directions of the equivalence.
-/

open Set Metric

namespace RudinRCA.Chapter13

/-- The open complex unit disc is simply connected, since it is nonempty
and convex and hence contractible. -/
theorem simply_connected_open_unit_disc :
    IsSimplyConnected (Metric.ball (0 : ℂ) 1) := by
  let : ContractibleSpace (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace
      ⟨0, mem_ball_self zero_lt_one⟩
  infer_instance

/-- Rudin 13.11 (a) implies (b): a plane set homeomorphic to the open
unit disc is simply connected. -/
theorem simply_connected_of_homeomorphic_to_unit_disc {Ω : Set ℂ}
    (hhomeo : Nonempty (Ω ≃ₜ Metric.ball (0 : ℂ) 1)) : IsSimplyConnected Ω := by
  obtain ⟨e⟩ := hhomeo
  let : SimplyConnectedSpace (Metric.ball (0 : ℂ) 1) := simply_connected_open_unit_disc
  exact e.toHomotopyEquiv.simplyConnectedSpace

#print axioms simply_connected_open_unit_disc
#print axioms simply_connected_of_homeomorphic_to_unit_disc

end RudinRCA.Chapter13
