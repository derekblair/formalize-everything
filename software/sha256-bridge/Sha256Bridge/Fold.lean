import Hash.Sha256.Fast

/-! Transport between the upstream front-recursive block loop and `Nat.fold`. -/

namespace Sha256Bridge

open Hash.Sha256

theorem hashFrom_succ_last (P : ByteArray) (m : Nat) (H : Fast.St) (off : Nat) :
    Fast.hashFrom P H (m + 1) off =
      Fast.compress (Fast.hashFrom P H m off) (Fast.wordsAt P (off + 64 * m)) := by
  induction m generalizing H off with
  | zero => simp [Fast.hashFrom]
  | succ m ih =>
    change Fast.hashFrom P (Fast.compress H (Fast.wordsAt P off)) (m + 1) (off + 64) = _
    rw [ih]
    change Fast.compress (Fast.hashFrom P H (m + 1) off) _ = _
    congr 2
    omega

theorem hashFrom_eq_fold (P : ByteArray) (m : Nat) (H : Fast.St) (off : Nat) :
    Fast.hashFrom P H m off =
      Nat.fold m (fun i _ st => Fast.compress st (Fast.wordsAt P (off + 64 * i))) H := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [hashFrom_succ_last, Nat.fold_succ, ih]

end Sha256Bridge
