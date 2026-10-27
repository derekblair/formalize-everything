import Sha256Bridge.Upstream

/-!
The schedule prefix invariant aligns the growing source array with the verified
fixed-size vector. A single-round equality then transports the bounded round
fold and its feed-forward addition without changing either implementation.
-/

namespace Sha256Bridge

open Hash.Sha256


theorem kConstants_eq_fast : Upstream.kConstants = Fast.K.toArray := by decide
theorem h0Constants_eq_fast : Upstream.h0Constants = Fast.H0.toArray := by decide

theorem extendSchedule_succ_last (a : Array UInt32) (n : Nat) :
    Upstream.extendSchedule a (n + 1) = Upstream.extendSchedule (Upstream.extendSchedule a n) 1 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change Upstream.extendSchedule (Upstream.extendSchedule a 1) (n + 1) =
      Upstream.extendSchedule (Upstream.extendSchedule (Upstream.extendSchedule a 1) n) 1
    exact ih _

theorem extendSchedule_one (a : Array UInt32) :
    Upstream.extendSchedule a 1 = a.push
      (Fast.σ1 a[a.size - 2]! + a[a.size - 7]! +
       Fast.σ0 a[a.size - 15]! + a[a.size - 16]!) := rfl

theorem extendSchedule_prefix_step (s : Vector UInt32 64) (i : Nat) (hi : i < 48) :
    Upstream.extendSchedule (s.toArray.extract 0 (16 + i)) 1 =
      (Fast.scheduleStep i hi s).toArray.extract 0 (16 + (i + 1)) := by
  have hget (j : Nat) (hj : j < 16 + i) :
      (s.toArray.extract 0 (16 + i))[j]! = s[j]'(by omega) := by
    rw [getElem!_pos _ j (by simp only [Array.size_extract, Vector.size_toArray, Nat.sub_zero]; omega)]
    simp only [Array.getElem_extract, Nat.zero_add, Vector.getElem_toArray]
  rw [extendSchedule_one]
  simp only [Array.size_extract, Vector.size_toArray, Nat.sub_zero]
  rw [Nat.min_eq_left (by omega)]
  simp only [Fast.scheduleStep, Vector.toArray_set]
  apply Array.ext
  · simp only [Array.size_push, Array.size_extract, Array.size_set,
      Vector.size_toArray, Nat.sub_zero]
    omega
  · intro j hj₁ hj₂
    simp only [Array.size_push, Array.size_extract, Vector.size_toArray,
      Nat.sub_zero] at hj₁
    simp only [Array.getElem_push, Array.size_extract, Vector.size_toArray,
      Nat.sub_zero, Array.getElem_extract, Nat.zero_add, Array.getElem_set]
    split
    · split
      · omega
      · simp
    · split
      · rw [hget _ (by omega), hget _ (by omega), hget _ (by omega), hget _ (by omega)]
        simp only [Nat.add_comm 16 i]
      · omega

theorem schedule_prefix (w : Vector UInt32 16) (k : Nat) (hk : k ≤ 48) :
    Upstream.extendSchedule w.toArray k =
      (Nat.fold k (fun i hi => Fast.scheduleStep i (by omega))
        (Fast.scheduleInit w)).toArray.extract 0 (16 + k) := by
  induction k with
  | zero =>
    change w.toArray = (Fast.scheduleInit w).toArray.extract 0 16
    apply Array.ext
    · simp
    · intro j hj₁ hj₂
      simp only [Vector.size_toArray] at hj₁
      simp only [Array.getElem_extract, Nat.zero_add, Vector.getElem_toArray,
        Fast.scheduleInit, Vec.getElem_ofFn, dite_eq_left hj₁]
  | succ k ih =>
    rw [extendSchedule_succ_last, ih (by omega), Nat.fold_succ]
    exact extendSchedule_prefix_step _ k (by omega)

theorem messageSchedule_eq_fast (w : Vector UInt32 16) :
    Upstream.messageSchedule w.toArray = (Fast.schedule w).toArray := by
  change Upstream.extendSchedule w.toArray 48 = (Fast.schedule w).toArray
  have h := schedule_prefix w 48 (by decide)
  have he : (Fast.schedule w).toArray.extract 0 64 = (Fast.schedule w).toArray := by
    simpa only [Vector.size_toArray] using (Array.extract_size (xs := (Fast.schedule w).toArray))
  exact h.trans he

theorem vector_get_bang {n : Nat} (v : Vector UInt32 n) (i : Nat) (hi : i < n) :
    v.toArray[i]! = v[i] := by
  rw [getElem!_pos _ i (by simp only [Vector.size_toArray]; exact hi)]
  rfl

theorem oneRound_eq_fast (sched : Vector UInt32 64) (t : Nat) (ht : t < 64)
    (st : Fast.St) :
    Upstream.oneRound st.toArray sched.toArray[t]! Upstream.kConstants[t]! =
      (Fast.round sched t ht st).toArray := by
  rw [kConstants_eq_fast, vector_get_bang _ _ ht, vector_get_bang _ _ ht]
  change #[
    (st.toArray[7]! + Fast.«Σ1» st.toArray[4]! +
      Fast.Ch st.toArray[4]! st.toArray[5]! st.toArray[6]! + Fast.K[t] + sched[t]) +
      (Fast.«Σ0» st.toArray[0]! + Fast.Maj st.toArray[0]! st.toArray[1]! st.toArray[2]!),
    st.toArray[0]!, st.toArray[1]!, st.toArray[2]!,
    st.toArray[3]! + (st.toArray[7]! + Fast.«Σ1» st.toArray[4]! +
      Fast.Ch st.toArray[4]! st.toArray[5]! st.toArray[6]! + Fast.K[t] + sched[t]),
    st.toArray[4]!, st.toArray[5]!, st.toArray[6]!] = _
  simp only [vector_get_bang st 0 (by decide), vector_get_bang st 1 (by decide),
    vector_get_bang st 2 (by decide), vector_get_bang st 3 (by decide),
    vector_get_bang st 4 (by decide), vector_get_bang st 5 (by decide),
    vector_get_bang st 6 (by decide), vector_get_bang st 7 (by decide)]
  rfl

theorem compressBlock_eq_fast (H : Fast.St) (w : Vector UInt32 16) :
    Upstream.compressBlock H.toArray w.toArray = (Fast.compress H w).toArray := by
  have hfinal : (Nat.fold 64 (Fast.round (Fast.schedule w)) H).toArray =
      Nat.fold 64 (fun t _ st => Upstream.oneRound st
        (Fast.schedule w).toArray[t]! Upstream.kConstants[t]!) H.toArray :=
    Fast.fold_abs (fun s : Fast.St => s.toArray) 64 _ _
      (fun t ht st => (oneRound_eq_fast (Fast.schedule w) t ht st).symm) H
  change Array.ofFn (fun i : Fin 8 => H.toArray[i.val]! +
    (Nat.fold 64 (fun t _ st => Upstream.oneRound st
      (Upstream.messageSchedule w.toArray)[t]! Upstream.kConstants[t]!) H.toArray)[i.val]!) = _
  rw [messageSchedule_eq_fast, ← hfinal]
  apply Array.ext
  · simp only [Array.size_ofFn, Vector.size_toArray]
  · intro i hi₁ hi₂
    have hi : i < 8 := by simpa only [Array.size_ofFn] using hi₁
    rw [Array.getElem_ofFn]
    simp only [vector_get_bang H i hi,
      vector_get_bang (Nat.fold 64 (Fast.round (Fast.schedule w)) H) i hi,
      Vector.getElem_toArray, Fast.compress, Vec.getElem_ofFn]

end Sha256Bridge
