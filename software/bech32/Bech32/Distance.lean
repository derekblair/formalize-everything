import Bech32.GF1024

/-!
# BCH distance of the Bech32/Bech32m checksum (milestone 2, ticket #16)

The `polymod` state update is `GF(32)`-linear.  Writing the 30-bit state as
six `GF(32)` chunks, one step is
`chunk_j (step s v) = chunk_{j-1} s + (v if j = 0) + (top chunk of s) * g_j`,
where `g = [18, 29, 21, 20, 22, 29]` is the low part of the BIP-173 generator
`g(x) = x^6 + 29x^5 + 22x^4 + 20x^3 + 21x^2 + 29x + 18` over `GF(32)`.

The distance proof (dossier Route (c), minor-certificate form): a zero-state
fold of a word stream is the XOR of impulse syndromes `syn d v` (value `v` at
distance `d` from the end).  Scaling by the inverse of the leading value and
reading the top five chunk equations leaves a `GF(32)`-linear relation among
at most `w - 1` syndrome vectors `syn d 1`.  A kernel-checked certificate
(packed-`Nat` tables, `decide` only — never `native_decide`) verifies that
the relevant syndrome vectors are linearly independent in the required
ranges: any 2 for distance `≤ 172`, any 3 for `≤ 88`, any 4 for `≤ 17`, and
the full 5 for `≤ 7`.  This yields minimum distance 5 up to length 89
(sharp: a weight-4 kernel word exists at length 90), distance 4 up to
length 173, distance 6 up to length 18, and distance 7 up to length 8.
-/

namespace Bech32

/-! ## Hamming metrics -/

/-- Number of nonzero symbols in a word stream. -/
def hammingWeight (xs : List Word) : Nat :=
  (xs.filter (· ≠ 0)).length

/-- Number of differing positions between two lists (meaningful on
    equal-length lists). -/
def hammingDist {α : Type} [DecidableEq α] (xs ys : List α) : Nat :=
  ((xs.zip ys).filter (fun p => p.1 ≠ p.2)).length

theorem hammingDist_append {α : Type} [DecidableEq α]
    (a₁ a₂ b₁ b₂ : List α) (h : a₁.length = a₂.length) :
    hammingDist (a₁ ++ b₁) (a₂ ++ b₂) =
      hammingDist a₁ a₂ + hammingDist b₁ b₂ := by
  simp only [hammingDist, List.zip_append h, List.filter_append, List.length_append]

theorem hammingDist_eq_countP {α : Type} [DecidableEq α] (xs ys : List α) :
    hammingDist xs ys = (xs.zip ys).countP (fun p => p.1 ≠ p.2) := by
  simp [hammingDist, List.countP_eq_length_filter]

theorem hammingDist_map_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (xs ys : List α) :
    hammingDist (xs.map f) (ys.map f) ≤ hammingDist xs ys := by
  have mono : ∀ (l : List (α × α)) (q r : α × α → Bool),
      (∀ p, q p = true → r p = true) → l.countP q ≤ l.countP r := by
    intro l q r h
    induction l with
    | nil => simp
    | cons p l ih =>
      by_cases hq : q p = true
      · rw [List.countP_cons_of_pos hq, List.countP_cons_of_pos (h p hq)]
        omega
      · rw [List.countP_cons_of_neg hq]
        by_cases hr : r p = true
        · rw [List.countP_cons_of_pos hr]
          omega
        · rw [List.countP_cons_of_neg hr]
          exact ih
  rw [hammingDist_eq_countP, hammingDist_eq_countP, List.zip_map, List.countP_map]
  apply mono
  intro p hp
  simp only [Function.comp_apply, decide_eq_true_eq] at hp ⊢
  exact fun h => hp (congrArg f h)

/-! ## Chunk decomposition of the 30-bit state -/

/-- The `j`-th five-bit chunk of a state, counting from the low end:
    `chunkW s j = (s >>> (5 * j)) &&& 31`.  Chunk 5 is the top chunk. -/
def chunkW (s : BitVec 30) (j : Nat) : Word := s.extractLsb' (5 * j) 5

theorem chunkW_toNat (s : BitVec 30) (j : Nat) :
    (chunkW s j).toNat = (s.toNat >>> (5 * j)) % 32 := by
  simp [chunkW, BitVec.extractLsb'_toNat]

theorem chunkW_zero (j : Nat) : chunkW 0 j = 0 := by
  simp [chunkW]

/-- Chunks determine the state. -/
theorem chunkW_inj {s t : BitVec 30}
    (h : ∀ j : Nat, j < 6 → chunkW s j = chunkW t j) : s = t := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have hbit : ∀ (z : BitVec 30) (j : Nat) (hj : j < 6) (b : Nat) (hb : b < 5),
      z.getLsbD (5 * j + b) = (chunkW z j).getLsbD b := by
    intro z j hj b hb
    simp only [chunkW, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  have hi5 : i / 5 < 6 := by omega
  have hb : i % 5 < 5 := Nat.mod_lt _ (by decide)
  have hdecomp : 5 * (i / 5) + i % 5 = i := by omega
  rw [← hdecomp, hbit s (i / 5) hi5 (i % 5) hb, hbit t (i / 5) hi5 (i % 5) hb,
    h (i / 5) hi5]

theorem chunkW_xor (s t : BitVec 30) (j : Nat) :
    chunkW (s ^^^ t) j = chunkW s j ^^^ chunkW t j := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, chunkW_toNat, chunkW_toNat, chunkW_toNat,
    BitVec.toNat_xor]
  have e1 : (s.toNat ^^^ t.toNat) >>> (5 * j) =
      (s.toNat >>> (5 * j)) ^^^ (t.toNat >>> (5 * j)) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow, Nat.xor_div_two_pow]
  rw [e1]
  exact Nat.xor_mod_two_pow (n := 5)

theorem chunkW_shiftLeft5 (s : BitVec 30) (j : Nat) (hj : j < 6) :
    chunkW (s <<< 5) j = if j = 0 then 0 else chunkW s (j - 1) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases hj0 : j = 0
  · subst hj0
    simp [chunkW, hi]
  · rw [if_neg hj0]
    have hi30 : 5 * j + i < 30 := by omega
    have hge : ¬ (5 * j + i < 5) := by omega
    have hidx : 5 * j + i - 5 = 5 * (j - 1) + i := by omega
    simp only [chunkW, BitVec.getLsbD_extractLsb', hi, decide_true,
      Bool.true_and]
    have hd1 : decide (5 * j + i < 30) = true := by
      rw [decide_eq_true_eq]; exact hi30
    have hd2 : decide (5 * j + i < 5) = false := by
      rw [decide_eq_false_iff_not]; exact hge
    rw [BitVec.getLsbD_shiftLeft, hd1, hd2, Bool.not_false, Bool.true_and,
      Bool.true_and, hidx]

theorem chunkW_setWidth (v : Word) (j : Nat) :
    chunkW (v.setWidth 30) j = if j = 0 then v else 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases hj : j = 0
  · subst hj
    have hi30 : i < 30 := by omega
    simp [chunkW, hi, hi30]
  · rw [if_neg hj]
    have hge : v.getLsbD (5 * j + i) = false :=
      BitVec.getLsbD_of_ge v (5 * j + i) (by omega)
    simp [chunkW, hi, hge]

theorem chunkW_shiftMul (s : BitVec 30) (k j : Nat) (hj : j < 6) :
    chunkW (s <<< (5 * k)) j = if j < k then 0 else chunkW s (j - k) := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  have hi30 : 5 * j + i < 30 := by omega
  by_cases hjk : j < k
  · rw [if_pos hjk]
    have h1 : (chunkW (s <<< (5 * k)) j).getLsbD i =
        (s <<< (5 * k)).getLsbD (5 * j + i) := by
      simp only [chunkW, BitVec.getLsbD_extractLsb', hi, decide_true,
        Bool.true_and]
    rw [h1, BitVec.getLsbD_shiftLeft]
    have : 5 * j + i < 5 * k := by omega
    simp [this, BitVec.getLsbD_zero]
  · rw [if_neg hjk]
    have h1 : (chunkW (s <<< (5 * k)) j).getLsbD i =
        (s <<< (5 * k)).getLsbD (5 * j + i) := by
      simp only [chunkW, BitVec.getLsbD_extractLsb', hi, decide_true,
        Bool.true_and]
    have h2 : (chunkW s (j - k)).getLsbD i = s.getLsbD (5 * (j - k) + i) := by
      simp only [chunkW, BitVec.getLsbD_extractLsb', hi, decide_true,
        Bool.true_and]
    rw [h1, h2, BitVec.getLsbD_shiftLeft]
    have hge : ¬ (5 * j + i < 5 * k) := by omega
    simp [hge, hi30]
    congr 1
    have : 5 * j + i - 5 * k = 5 * (j - k) + i := by omega
    rw [this]

/-! ## The generator tail and the chunk form of one step -/

/-- Coefficients of `g(x) - x^6` over `GF(32)`, ascending degree:
    `g(x) = x^6 + 29x^5 + 22x^4 + 20x^3 + 21x^2 + 29x + 18`. -/
def genChunk : Nat → Word
  | 0 => 18
  | 1 => 29
  | 2 => 21
  | 3 => 20
  | 4 => 22
  | 5 => 29
  | _ => 0

/-- The conditional generator XOR of `polymodStep`, as a function of the
    state's top chunk. -/
def genXor (t : Word) : BitVec 30 :=
  (if t.getLsbD 0 then 0x3b6a57b2 else 0) ^^^
  (if t.getLsbD 1 then 0x26508e6d else 0) ^^^
  (if t.getLsbD 2 then 0x1ea119fa else 0) ^^^
  (if t.getLsbD 3 then 0x3d4233dd else 0) ^^^
  (if t.getLsbD 4 then 0x2a1462b3 else 0)

theorem genXor_zero : genXor 0 = 0 := by decide

theorem getLsbD_chunkW_top (s : BitVec 30) (i : Nat) (hi : i < 5) :
    (chunkW s 5).getLsbD i = s.getLsbD (25 + i) := by
  have hd : decide (i < 5) = true := by
    rw [decide_eq_true_eq]; exact hi
  rw [show chunkW s 5 = s.extractLsb' (5 * 5) 5 from rfl,
    BitVec.getLsbD_extractLsb', hd, Bool.true_and,
    show (5 : Nat) * 5 = 25 from rfl]

theorem polymodStep_eq (s : BitVec 30) (v : Word) :
    polymodStep s v = (s <<< 5) ^^^ v.setWidth 30 ^^^ genXor (chunkW s 5) := by
  simp only [polymodStep, genXor]
  rw [← getLsbD_chunkW_top s 0 (by decide), ← getLsbD_chunkW_top s 1 (by decide),
    ← getLsbD_chunkW_top s 2 (by decide), ← getLsbD_chunkW_top s 3 (by decide),
    ← getLsbD_chunkW_top s 4 (by decide)]
  grind

/-- The chunks of the generator tail are `GF(32)`-multiples of the top chunk:
    the BIP-173 generator constants are the `alpha^i * g_low` table. -/
theorem chunkW_genXor (t : Word) (j : Nat) (hj : j < 6) :
    chunkW (genXor t) j = gf32Mul t (genChunk j) := by
  have h : ∀ t : Word, ∀ j : Fin 6,
      chunkW (genXor t) j.val = gf32Mul t (genChunk j.val) := by decide
  exact h t ⟨j, hj⟩

theorem polymodStep_chunk (s : BitVec 30) (v : Word) (j : Nat) (hj : j < 6) :
    chunkW (polymodStep s v) j =
      (if j = 0 then 0 else chunkW s (j - 1)) ^^^
      (if j = 0 then v else 0) ^^^
      gf32Mul (chunkW s 5) (genChunk j) := by
  rw [polymodStep_eq, chunkW_xor, chunkW_xor, chunkW_shiftLeft5 _ _ hj,
    chunkW_setWidth, chunkW_genXor _ j hj]

/-! ## `GF(32)`-scaling of a state -/

/-- Scale every chunk of a state by `c : GF(32)`. -/
def scaleState (c : Word) (s : BitVec 30) : BitVec 30 :=
  (gf32Mul c (chunkW s 0)).setWidth 30 ^^^
  ((gf32Mul c (chunkW s 1)).setWidth 30 <<< (5 * 1)) ^^^
  ((gf32Mul c (chunkW s 2)).setWidth 30 <<< (5 * 2)) ^^^
  ((gf32Mul c (chunkW s 3)).setWidth 30 <<< (5 * 3)) ^^^
  ((gf32Mul c (chunkW s 4)).setWidth 30 <<< (5 * 4)) ^^^
  ((gf32Mul c (chunkW s 5)).setWidth 30 <<< (5 * 5))

theorem chunkW_scaleState (c : Word) (s : BitVec 30) (j : Nat) (hj : j < 6) :
    chunkW (scaleState c s) j = gf32Mul c (chunkW s j) := by
  have hterm : ∀ (w : Word) (k j : Nat), j < 6 →
      chunkW ((w.setWidth 30) <<< (5 * k)) j = if j = k then w else 0 := by
    intro w k j hj
    rw [chunkW_shiftMul _ _ _ hj]
    by_cases h : j = k
    · subst h
      simp [chunkW_setWidth]
    · by_cases hjk : j < k
      · rw [if_pos hjk, if_neg h]
      · rw [if_neg hjk, chunkW_setWidth, if_neg (show j - k ≠ 0 by omega),
          if_neg h]
  simp only [scaleState, chunkW_xor]
  have hj0 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj0 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [hterm _ _ _ hj, chunkW_setWidth, BitVec.xor_zero]; try grind)

theorem scaleState_xor (c : Word) (s t : BitVec 30) :
    scaleState c (s ^^^ t) = scaleState c s ^^^ scaleState c t := by
  apply chunkW_inj
  intro j hj
  rw [chunkW_scaleState _ _ _ hj, chunkW_xor, gf32Mul_xor_right,
    ← chunkW_scaleState _ _ _ hj, ← chunkW_scaleState _ _ _ hj, chunkW_xor]

theorem scaleState_zero_state (c : Word) : scaleState c 0 = 0 := by
  apply chunkW_inj
  intro j hj
  rw [chunkW_scaleState _ _ _ hj, chunkW_zero, gf32Mul_zero]

theorem scaleState_zero_coeff (s : BitVec 30) : scaleState 0 s = 0 := by
  apply chunkW_inj
  intro j hj
  rw [chunkW_scaleState _ _ _ hj, gf32Zero_mul]
  exact (chunkW_zero j).symm

/-- `polymodStep` intertwines with `GF(32)`-scaling. -/
theorem polymodStep_scale (c : Word) (s : BitVec 30) (v : Word) :
    polymodStep (scaleState c s) (gf32Mul c v) =
      scaleState c (polymodStep s v) := by
  apply chunkW_inj
  intro j hj
  rw [chunkW_scaleState _ _ _ hj, polymodStep_chunk _ _ j hj,
    polymodStep_chunk _ _ j hj,
    chunkW_scaleState _ _ _ (by decide : (5 : Nat) < 6)]
  by_cases hj0 : j = 0
  · subst hj0
    simp
    rw [gf32Mul_xor_right, gf32Mul_assoc]
  · have hjm : j - 1 < 6 := by omega
    rw [chunkW_scaleState c s (j - 1) hjm]
    simp [hj0, gf32Mul_xor_right, gf32Mul_assoc, chunkW_setWidth]

/-- One zero step is injective on states: the top chunk is recovered from the
    low chunk of the result since `genChunk 0 = 18 ≠ 0`. -/
theorem polymodStep_zero_inj {s : BitVec 30} (h : polymodStep s 0 = 0) : s = 0 := by
  have htop : chunkW s 5 = 0 := by
    have h0 : chunkW (polymodStep s 0) 0 = 0 := by rw [h]; exact chunkW_zero 0
    rw [polymodStep_chunk s 0 0 (by decide)] at h0
    simp only [if_pos rfl, gf32Mul_zero] at h0
    -- h0 : 0 ^^^ 0 ^^^ gf32Mul (chunkW s 5) (genChunk 0) = 0
    have hgen : genChunk 0 = 18 := rfl
    rw [hgen] at h0
    have hdec : ∀ t : Word, gf32Mul t 18 = 0 → t = 0 := by decide
    have : gf32Mul (chunkW s 5) 18 = 0 := by
      simpa using h0
    exact hdec _ this
  apply chunkW_inj
  intro j hj
  rw [chunkW_zero]
  by_cases hj5 : j = 5
  · subst hj5; exact htop
  · have hjm : j + 1 < 6 := by omega
    have h1 : chunkW (s <<< 5) (j + 1) = chunkW s j := by
      rw [chunkW_shiftLeft5 _ _ hjm]
      simp [show j + 1 ≠ 0 by omega, show j + 1 - 1 = j by omega]
    have h2 : polymodStep s 0 = (s <<< 5) ^^^ genXor (chunkW s 5) := by
      rw [polymodStep_eq]
      simp
    rw [htop, genXor_zero] at h2
    rw [h2] at h
    have h3 : (s <<< 5) = 0 := (BitVec.xor_zero).symm.trans h
    rw [← h1, h3]
    exact chunkW_zero _

/-- Scaling commutes with folding a whole stream. -/
theorem foldl_polymodStep_scale (es : List Word) (s : BitVec 30) (c : Word) :
    (es.map (gf32Mul c)).foldl polymodStep (scaleState c s) =
      scaleState c (es.foldl polymodStep s) := by
  induction es generalizing s with
  | nil => rfl
  | cons x es ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [polymodStep_scale]
    exact ih _

/-! ## Impulse syndromes -/

/-- The syndrome of a single impulse: value `v` at distance `d` from the end
    of the stream, i.e. the fold of `v` followed by `d` zeros from state 0. -/
def syn (d : Nat) (v : Word) : BitVec 30 :=
  (List.replicate d 0).foldl polymodStep (v.setWidth 30)

theorem syn_zero (v : Word) : syn 0 v = v.setWidth 30 := rfl

theorem syn_succ (d : Nat) (v : Word) :
    syn (d + 1) v = polymodStep (syn d v) 0 := by
  simp only [syn, List.replicate_succ', List.foldl_append]
  rfl

theorem syn_scale (c : Word) (d : Nat) (v : Word) :
    syn d (gf32Mul c v) = scaleState c (syn d v) := by
  induction d with
  | zero =>
    apply chunkW_inj
    intro j hj
    rw [chunkW_scaleState _ _ _ hj, syn_zero, syn_zero, chunkW_setWidth,
      chunkW_setWidth]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl, if_pos rfl]
    · simp only [if_neg hj0]
      exact (gf32Mul_zero c).symm
  | succ d ih =>
    have h := polymodStep_scale c (syn d v) 0
    rw [gf32Mul_zero] at h
    rw [syn_succ, syn_succ, ih]
    exact h

theorem syn_zero_val (d : Nat) : syn d 0 = 0 := by
  induction d with
  | zero => simp [syn_zero]
  | succ d ih => rw [syn_succ, ih]; exact polymodStep_zero

theorem syn_ne_zero {d : Nat} {v : Word} (hv : v ≠ 0) : syn d v ≠ 0 := by
  induction d with
  | zero =>
    rw [syn_zero]
    intro h
    have : v.toNat = 0 := by
      have h2 := congrArg BitVec.toNat h
      simp [BitVec.toNat_setWidth] at h2
      have hv2 : v.toNat < 32 := v.isLt
      omega
    exact hv (BitVec.eq_of_toNat_eq (by simp [this]))
  | succ d ih =>
    rw [syn_succ]
    intro h
    exact ih (polymodStep_zero_inj h)


/-! ## Packed syndrome table and kernel certificates -/

/-- Packed syndrome table: entry `d` (30 bits at offset `30 * d`) is
    `(syn d 1).toNat` for `d < 173`. -/
def synPacked : Nat :=
194020196991065651154688194566673316729475376522057705062957749702192083776592191213257126881540542554196052441770445122210727406766892644317476492767391097628066992459819212004560077945981014146549563098486058877052374589394012916781302863058813601636076537481967116361171329931928982202017734754564151573029134038602330784693827111864989673993989904309288621076490141836311251838912488260719911810677007295848745462801082511159957369981058824091310022793777003965151288289246414769877510211531203747487425599934073061115559610462955937612354340552470422636340582212527401025923012006226827826569430284358921073176521768754954189732251054442910022492291541287000194309040786356982777438854198487887071908219745426396216676126393557597592783272822634345051430612957475667132025310621314527671821564521072676759886125830427347071811468549856616581203758600528766102275246151223785594992272873409668674955309577049987963586793038081429098734792700624801802354348277987342383267092259317261657587533207711632600411584000015238846331851714161953169327090282429325406182143698635275848122668009633595146138443689745915967127877035217834162653315323190298051136152935964555123608516628809710690598010853728223478290885355515141604406389706372579441741874790347090586113863038226392168839270280821726677866819148384861757968013436672931904766880477109891505411558185003960056503007790176106378996516387037226927148585262142685537188442628591330156269445172729825614079439848700069392536305605956056715498810265666565999548521604984910456750813279824488962406159579348993

/-- Extract the `d`-th syndrome from the packed table. -/
def synEntry (d : Nat) : Nat := (synPacked >>> (30 * d)) &&& 1073741823

set_option maxRecDepth 131072 in
set_option maxHeartbeats 3200000 in
theorem synEntry_eq (d : BitVec 10) (hd : d.toNat < 173) :
    synEntry d.toNat = (syn d.toNat 1).toNat := by
  exact (by decide : ∀ d : BitVec 10, d.toNat < 173 →
    synEntry d.toNat = (syn d.toNat 1).toNat) d hd

/-- `Nat` chunk extraction, mirroring `chunkW`. -/
def chunkNat (s j : Nat) : Nat := (s >>> (5 * j)) % 32

/-- Determinants over `GF(32)` at the `Nat` level (certificate side).
    Coordinates are chunk indices; for syndrome vectors the relevant
    coordinates are `1..5` (the top five chunks). -/
def det2Nat (x y : Nat) (i j : Nat) : Nat :=
  gf32MulNat (chunkNat x i) (chunkNat y j) ^^^
    gf32MulNat (chunkNat x j) (chunkNat y i)

def det3Nat (x y z : Nat) (i j k : Nat) : Nat :=
  gf32MulNat (chunkNat x i) (det2Nat y z j k) ^^^
    gf32MulNat (chunkNat x j) (det2Nat y z i k) ^^^
    gf32MulNat (chunkNat x k) (det2Nat y z i j)

def det4Nat (x y z w : Nat) (i j k l : Nat) : Nat :=
  gf32MulNat (chunkNat x i) (det3Nat y z w j k l) ^^^
    gf32MulNat (chunkNat x j) (det3Nat y z w i k l) ^^^
    gf32MulNat (chunkNat x k) (det3Nat y z w i j l) ^^^
    gf32MulNat (chunkNat x l) (det3Nat y z w i j k)

def det5Nat (x1 x2 x3 x4 x5 : Nat) : Nat :=
  gf32MulNat (chunkNat x1 1) (det4Nat x2 x3 x4 x5 2 3 4 5) ^^^
    gf32MulNat (chunkNat x1 2) (det4Nat x2 x3 x4 x5 1 3 4 5) ^^^
    gf32MulNat (chunkNat x1 3) (det4Nat x2 x3 x4 x5 1 2 4 5) ^^^
    gf32MulNat (chunkNat x1 4) (det4Nat x2 x3 x4 x5 1 2 3 5) ^^^
    gf32MulNat (chunkNat x1 5) (det4Nat x2 x3 x4 x5 1 2 3 4)

def coordPairs : List (Nat × Nat) :=
  [(1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

def coordTriples : List (Nat × Nat × Nat) :=
  [(1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5), (1, 4, 5),
   (2, 3, 4), (2, 3, 5), (2, 4, 5), (3, 4, 5)]

def coordQuads : List (Nat × Nat × Nat × Nat) :=
  [(1, 2, 3, 4), (1, 2, 3, 5), (1, 2, 4, 5), (1, 3, 4, 5), (2, 3, 4, 5)]

def minor2Ok (x y : Nat) : Bool :=
  coordPairs.any (fun p => det2Nat x y p.1 p.2 != 0)

def minor3Ok (x y z : Nat) : Bool :=
  coordTriples.any (fun p => det3Nat x y z p.1 p.2.1 p.2.2 != 0)

def minor4Ok (x y z w : Nat) : Bool :=
  coordQuads.any (fun p => det4Nat x y z w p.1 p.2.1 p.2.2.1 p.2.2.2 != 0)

/-- Certificate: the top syndrome of every distance `1..172` is nonzero. -/
def certTopNe : Bool :=
  (List.range 172).all (fun i => synEntry (i + 1) >>> 5 != 0)

/-- Certificate: any two top syndromes at distances `1 ≤ d2 < d1 ≤ 172` are
    `GF(32)`-linearly independent (some `2×2` minor is nonzero). -/
def cert2 : Bool :=
  (List.range 171).all (fun i =>
    (List.range (i + 1)).all (fun j =>
      minor2Ok (synEntry (i + 2)) (synEntry (j + 1))))

/-- Certificate: any three top syndromes at distances `1 ≤ d3 < d2 < d1 ≤ 88`
    are `GF(32)`-linearly independent (some `3×3` minor is nonzero). -/
def cert3 : Bool :=
  (List.range 86).all (fun i =>
    (List.range (i + 1)).all (fun j =>
      (List.range (j + 1)).all (fun k =>
        minor3Ok (synEntry (i + 3)) (synEntry (j + 2)) (synEntry (k + 1)))))

/-- Certificate: any four top syndromes at distances `1 ≤ d4 < ... < d1 ≤ 17`
    are independent (some `4×4` minor is nonzero). -/
def cert4 : Bool :=
  (List.range 14).all (fun i =>
    (List.range (i + 1)).all (fun j =>
      (List.range (j + 1)).all (fun k =>
        (List.range (k + 1)).all (fun l =>
          minor4Ok (synEntry (i + 4)) (synEntry (j + 3)) (synEntry (k + 2))
            (synEntry (l + 1))))))

/-- Certificate: any five top syndromes at distances `1 ≤ d5 < ... < d1 ≤ 7`
    have nonzero `5×5` determinant. -/
def cert5 : Bool :=
  (List.range 3).all (fun i =>
    (List.range (i + 1)).all (fun j =>
      (List.range (j + 1)).all (fun k =>
        (List.range (k + 1)).all (fun l =>
          (List.range (l + 1)).all (fun m =>
            det5Nat (synEntry (i + 5)) (synEntry (j + 4)) (synEntry (k + 3))
              (synEntry (l + 2)) (synEntry (m + 1)) != 0)))))

set_option maxRecDepth 16384 in
theorem certTopNe_eq : certTopNe = true := by decide
set_option maxRecDepth 16384 in
theorem cert2_eq : cert2 = true := by decide
set_option maxRecDepth 16384 in
theorem cert4_eq : cert4 = true := by decide
set_option maxRecDepth 16384 in
theorem cert5_eq : cert5 = true := by decide

/-! ## Determinants over `GF(32)` (proof side) and Cramer identities -/

/-- `2×2` determinant of two state vectors at chunk coordinates `i, j`. -/
def det2W (x y : BitVec 30) (i j : Nat) : Word :=
  gf32Mul (chunkW x i) (chunkW y j) ^^^ gf32Mul (chunkW x j) (chunkW y i)

/-- `3×3` determinant, cofactor expansion along the first vector. -/
def det3W (x y z : BitVec 30) (i j k : Nat) : Word :=
  gf32Mul (chunkW x i) (det2W y z j k) ^^^
    gf32Mul (chunkW x j) (det2W y z i k) ^^^
    gf32Mul (chunkW x k) (det2W y z i j)

/-- `4×4` determinant, cofactor expansion along the first vector. -/
def det4W (x y z w : BitVec 30) (i j k l : Nat) : Word :=
  gf32Mul (chunkW x i) (det3W y z w j k l) ^^^
    gf32Mul (chunkW x j) (det3W y z w i k l) ^^^
    gf32Mul (chunkW x k) (det3W y z w i j l) ^^^
    gf32Mul (chunkW x l) (det3W y z w i j k)

/-- `5×5` determinant at the top coordinates `1..5`. -/
def det5W (x1 x2 x3 x4 x5 : BitVec 30) : Word :=
  gf32Mul (chunkW x1 1) (det4W x2 x3 x4 x5 2 3 4 5) ^^^
    gf32Mul (chunkW x1 2) (det4W x2 x3 x4 x5 1 3 4 5) ^^^
    gf32Mul (chunkW x1 3) (det4W x2 x3 x4 x5 1 2 4 5) ^^^
    gf32Mul (chunkW x1 4) (det4W x2 x3 x4 x5 1 2 3 5) ^^^
    gf32Mul (chunkW x1 5) (det4W x2 x3 x4 x5 1 2 3 4)

theorem det2W_toNat (x y : BitVec 30) (i j : Nat) :
    (det2W x y i j).toNat = det2Nat x.toNat y.toNat i j := by
  simp only [det2W, det2Nat, chunkW_toNat, chunkNat, gf32Mul_toNat, BitVec.toNat_xor]

theorem det3W_toNat (x y z : BitVec 30) (i j k : Nat) :
    (det3W x y z i j k).toNat = det3Nat x.toNat y.toNat z.toNat i j k := by
  simp only [det3W, det3Nat, det2W_toNat, chunkW_toNat, chunkNat,
    gf32Mul_toNat, BitVec.toNat_xor]

theorem det4W_toNat (x y z w : BitVec 30) (i j k l : Nat) :
    (det4W x y z w i j k l).toNat =
      det4Nat x.toNat y.toNat z.toNat w.toNat i j k l := by
  simp only [det4W, det4Nat, det3W_toNat, chunkW_toNat, chunkNat,
    gf32Mul_toNat, BitVec.toNat_xor]

theorem det5W_toNat (x1 x2 x3 x4 x5 : BitVec 30) :
    (det5W x1 x2 x3 x4 x5).toNat =
      det5Nat x1.toNat x2.toNat x3.toNat x4.toNat x5.toNat := by
  simp only [det5W, det5Nat, det4W_toNat, chunkW_toNat, chunkNat,
    gf32Mul_toNat, BitVec.toNat_xor]

theorem xor_eq_zero_imp {p q : Word} (h : p ^^^ q = 0) : p = q := by
  have h2 := congrArg (· ^^^ q) h
  simpa [BitVec.xor_assoc] using h2

theorem det2W_self (y : BitVec 30) (i j : Nat) : det2W y y i j = 0 := by
  show gf32Mul (chunkW y i) (chunkW y j) ^^^
    gf32Mul (chunkW y j) (chunkW y i) = 0
  rw [gf32Mul_comm (chunkW y j) (chunkW y i)]
  exact BitVec.xor_self

/-- Cramer identity, `2×2`: a relation at coordinates `i, j` annihilates
    `a * det`. -/
theorem cramer2 (x y : BitVec 30) (a b : Word) (i j : Nat)
    (hi : gf32Mul a (chunkW x i) ^^^ gf32Mul b (chunkW y i) = 0)
    (hj : gf32Mul a (chunkW x j) ^^^ gf32Mul b (chunkW y j) = 0) :
    gf32Mul a (det2W x y i j) = 0 := by
  have hai : gf32Mul a (chunkW x i) = gf32Mul b (chunkW y i) := xor_eq_zero_imp hi
  have haj : gf32Mul a (chunkW x j) = gf32Mul b (chunkW y j) := xor_eq_zero_imp hj
  calc gf32Mul a (det2W x y i j)
      = gf32Mul (gf32Mul a (chunkW x i)) (chunkW y j) ^^^
          gf32Mul (gf32Mul a (chunkW x j)) (chunkW y i) := by
        rw [det2W, gf32Mul_xor_right, ← gf32Mul_assoc, ← gf32Mul_assoc]
    _ = gf32Mul (gf32Mul b (chunkW y i)) (chunkW y j) ^^^
          gf32Mul (gf32Mul b (chunkW y j)) (chunkW y i) := by rw [hai, haj]
    _ = gf32Mul b (det2W y y i j) := by
        rw [det2W, gf32Mul_xor_right, gf32Mul_assoc, gf32Mul_assoc]
    _ = 0 := by rw [det2W_self]; exact gf32Mul_zero b

/-- Swap the first two factors of a triple product. -/
theorem gf32Mul_swap_head (a b : Word) (t : Word) :
    gf32Mul a (gf32Mul b t) = gf32Mul b (gf32Mul a t) := by
  rw [← gf32Mul_assoc, gf32Mul_comm a b, gf32Mul_assoc]


/-- Swap the last two factors of a triple product.  (Deterministic
    factor-order normalisation for the cofactor expansions: these
    permutation lemmas are simp-order-guarded, so the expansions'
    closers do not depend on `grind`'s search order.) -/
theorem gf32Mul_swap_tail3 (a b c : Word) :
    gf32Mul a (gf32Mul b c) = gf32Mul a (gf32Mul c b) := by
  rw [gf32Mul_comm b c]

/-- Swap the last two factors of a quadruple product. -/
theorem gf32Mul_swap_tail4 (a b c d : Word) :
    gf32Mul a (gf32Mul b (gf32Mul c d)) =
      gf32Mul a (gf32Mul b (gf32Mul d c)) := by
  rw [gf32Mul_comm c d]

/-- Swap the last two factors of a quintuple product. -/
theorem gf32Mul_swap_tail5 (a b c d e : Word) :
    gf32Mul a (gf32Mul b (gf32Mul c (gf32Mul d e))) =
      gf32Mul a (gf32Mul b (gf32Mul c (gf32Mul e d))) := by
  rw [gf32Mul_comm d e]
/-- Cofactor expansion of `det3W` along the second vector. -/
theorem det3W_expand_mid (x y z : BitVec 30) (i j k : Nat) :
    det3W x y z i j k =
      gf32Mul (chunkW y i) (det2W x z j k) ^^^
        gf32Mul (chunkW y j) (det2W x z i k) ^^^
        gf32Mul (chunkW y k) (det2W x z i j) := by
  simp only [det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right]
  rw [gf32Mul_swap_head (chunkW x i) (chunkW y j) (chunkW z k),
    gf32Mul_swap_head (chunkW x i) (chunkW y k) (chunkW z j),
    gf32Mul_swap_head (chunkW x j) (chunkW y i) (chunkW z k),
    gf32Mul_swap_head (chunkW x j) (chunkW y k) (chunkW z i),
    gf32Mul_swap_head (chunkW x k) (chunkW y i) (chunkW z j),
    gf32Mul_swap_head (chunkW x k) (chunkW y j) (chunkW z i)]
  try simp only [gf32Mul_swap_tail3]
  ac_rfl

/-- Cofactor expansion of `det3W` along the third vector. -/
theorem det3W_expand_third (x y z : BitVec 30) (i j k : Nat) :
    det3W x y z i j k =
      gf32Mul (chunkW z i) (det2W x y j k) ^^^
        gf32Mul (chunkW z j) (det2W x y i k) ^^^
        gf32Mul (chunkW z k) (det2W x y i j) := by
  simp only [det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right]
  rw [gf32Mul_comm (chunkW y j) (chunkW z k),
    gf32Mul_swap_head (chunkW x i) (chunkW z k) (chunkW y j),
    gf32Mul_comm (chunkW y k) (chunkW z j),
    gf32Mul_swap_head (chunkW x i) (chunkW z j) (chunkW y k),
    gf32Mul_comm (chunkW y i) (chunkW z k),
    gf32Mul_swap_head (chunkW x j) (chunkW z k) (chunkW y i),
    gf32Mul_comm (chunkW y k) (chunkW z i),
    gf32Mul_swap_head (chunkW x j) (chunkW z i) (chunkW y k),
    gf32Mul_comm (chunkW y i) (chunkW z j),
    gf32Mul_swap_head (chunkW x k) (chunkW z j) (chunkW y i),
    gf32Mul_comm (chunkW y j) (chunkW z i),
    gf32Mul_swap_head (chunkW x k) (chunkW z i) (chunkW y j)]
  try simp only [gf32Mul_swap_tail3]
  ac_rfl

theorem det3W_rep_fst (y z : BitVec 30) (i j k : Nat) :
    det3W y y z i j k = 0 := by
  rw [det3W_expand_third, det2W_self, det2W_self, det2W_self,
    gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl

theorem det3W_rep_mid (z y : BitVec 30) (i j k : Nat) :
    det3W z y z i j k = 0 := by
  rw [det3W_expand_mid, det2W_self, det2W_self, det2W_self,
    gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl

/-- Cramer identity, `3×3`. -/
theorem cramer3 (x y z : BitVec 30) (a b c : Word) (i j k : Nat)
    (hi : gf32Mul a (chunkW x i) ^^^ gf32Mul b (chunkW y i) ^^^
      gf32Mul c (chunkW z i) = 0)
    (hj : gf32Mul a (chunkW x j) ^^^ gf32Mul b (chunkW y j) ^^^
      gf32Mul c (chunkW z j) = 0)
    (hk : gf32Mul a (chunkW x k) ^^^ gf32Mul b (chunkW y k) ^^^
      gf32Mul c (chunkW z k) = 0) :
    gf32Mul a (det3W x y z i j k) = 0 := by
  have hai : gf32Mul a (chunkW x i) =
      gf32Mul b (chunkW y i) ^^^ gf32Mul c (chunkW z i) := by
    have h := hi
    rw [BitVec.xor_assoc] at h
    exact xor_eq_zero_imp h
  have haj : gf32Mul a (chunkW x j) =
      gf32Mul b (chunkW y j) ^^^ gf32Mul c (chunkW z j) := by
    have h := hj
    rw [BitVec.xor_assoc] at h
    exact xor_eq_zero_imp h
  have hak : gf32Mul a (chunkW x k) =
      gf32Mul b (chunkW y k) ^^^ gf32Mul c (chunkW z k) := by
    have h := hk
    rw [BitVec.xor_assoc] at h
    exact xor_eq_zero_imp h
  calc gf32Mul a (det3W x y z i j k)
      = gf32Mul (gf32Mul a (chunkW x i)) (det2W y z j k) ^^^
          gf32Mul (gf32Mul a (chunkW x j)) (det2W y z i k) ^^^
          gf32Mul (gf32Mul a (chunkW x k)) (det2W y z i j) := by
        simp only [det3W, gf32Mul_xor_right, ← gf32Mul_assoc]
    _ = gf32Mul b (det3W y y z i j k) ^^^ gf32Mul c (det3W z y z i j k) := by
        rw [hai, haj, hak]
        simp only [det3W, gf32Mul_xor_left, gf32Mul_xor_right, gf32Mul_assoc]
        ac_rfl
    _ = 0 := by
        rw [det3W_rep_fst, det3W_rep_mid, gf32Mul_zero, gf32Mul_zero]; rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem cert3_eq : cert3 = true := by decide

/-! ## Higher Cramer identities -/

/-- Cofactor expansion of `det4W` along the second vector. -/
theorem det4W_expand_second (x y z w : BitVec 30) (i j k l : Nat) :
    det4W x y z w i j k l =
      gf32Mul (chunkW y i) (det3W x z w j k l) ^^^
        gf32Mul (chunkW y j) (det3W x z w i k l) ^^^
        gf32Mul (chunkW y k) (det3W x z w i j l) ^^^
        gf32Mul (chunkW y l) (det3W x z w i j k) := by
  simp only [det4W, det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right,
    gf32Mul_swap_head]
  ac_rfl

/-- Cofactor expansion of `det4W` along the fourth vector. -/
theorem det4W_expand_fourth (x y z w : BitVec 30) (i j k l : Nat) :
    det4W x y z w i j k l =
      gf32Mul (chunkW w i) (det3W x y z j k l) ^^^
        gf32Mul (chunkW w j) (det3W x y z i k l) ^^^
        gf32Mul (chunkW w k) (det3W x y z i j l) ^^^
        gf32Mul (chunkW w l) (det3W x y z i j k) := by
  simp only [det4W, det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right,
    gf32Mul_swap_head, gf32Mul_swap_tail4]
  ac_rfl

theorem det4W_rep_fst (y z w : BitVec 30) (i j k l : Nat) :
    det4W y y z w i j k l = 0 := by
  rw [det4W_expand_fourth, det3W_rep_fst, det3W_rep_fst, det3W_rep_fst,
    det3W_rep_fst, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl

theorem det4W_rep_13 (z y w : BitVec 30) (i j k l : Nat) :
    det4W z y z w i j k l = 0 := by
  rw [det4W_expand_second, det3W_rep_fst, det3W_rep_fst, det3W_rep_fst,
    det3W_rep_fst, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl

theorem det4W_rep_14 (w y z : BitVec 30) (i j k l : Nat) :
    det4W w y z w i j k l = 0 := by
  rw [det4W_expand_second, det3W_rep_mid, det3W_rep_mid, det3W_rep_mid,
    det3W_rep_mid, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl

/-- Cramer identity, `4×4`. -/
theorem cramer4 (x y z w : BitVec 30) (a b c d : Word) (i j k l : Nat)
    (hi : gf32Mul a (chunkW x i) ^^^ gf32Mul b (chunkW y i) ^^^
      gf32Mul c (chunkW z i) ^^^ gf32Mul d (chunkW w i) = 0)
    (hj : gf32Mul a (chunkW x j) ^^^ gf32Mul b (chunkW y j) ^^^
      gf32Mul c (chunkW z j) ^^^ gf32Mul d (chunkW w j) = 0)
    (hk : gf32Mul a (chunkW x k) ^^^ gf32Mul b (chunkW y k) ^^^
      gf32Mul c (chunkW z k) ^^^ gf32Mul d (chunkW w k) = 0)
    (hl : gf32Mul a (chunkW x l) ^^^ gf32Mul b (chunkW y l) ^^^
      gf32Mul c (chunkW z l) ^^^ gf32Mul d (chunkW w l) = 0) :
    gf32Mul a (det4W x y z w i j k l) = 0 := by
  have hai : gf32Mul a (chunkW x i) =
      gf32Mul b (chunkW y i) ^^^ gf32Mul c (chunkW z i) ^^^
        gf32Mul d (chunkW w i) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc]; exact hi)
  have haj : gf32Mul a (chunkW x j) =
      gf32Mul b (chunkW y j) ^^^ gf32Mul c (chunkW z j) ^^^
        gf32Mul d (chunkW w j) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc]; exact hj)
  have hak : gf32Mul a (chunkW x k) =
      gf32Mul b (chunkW y k) ^^^ gf32Mul c (chunkW z k) ^^^
        gf32Mul d (chunkW w k) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc]; exact hk)
  have hal : gf32Mul a (chunkW x l) =
      gf32Mul b (chunkW y l) ^^^ gf32Mul c (chunkW z l) ^^^
        gf32Mul d (chunkW w l) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc]; exact hl)
  calc gf32Mul a (det4W x y z w i j k l)
      = gf32Mul (gf32Mul a (chunkW x i)) (det3W y z w j k l) ^^^
          gf32Mul (gf32Mul a (chunkW x j)) (det3W y z w i k l) ^^^
          gf32Mul (gf32Mul a (chunkW x k)) (det3W y z w i j l) ^^^
          gf32Mul (gf32Mul a (chunkW x l)) (det3W y z w i j k) := by
        simp only [det4W, gf32Mul_xor_right, ← gf32Mul_assoc]
    _ = gf32Mul b (det4W y y z w i j k l) ^^^
          gf32Mul c (det4W z y z w i j k l) ^^^
          gf32Mul d (det4W w y z w i j k l) := by
        rw [hai, haj, hak, hal]
        simp only [det4W, gf32Mul_xor_left, gf32Mul_xor_right, gf32Mul_assoc]
        ac_rfl
    _ = 0 := by
        rw [det4W_rep_fst, det4W_rep_13, det4W_rep_14, gf32Mul_zero,
          gf32Mul_zero, gf32Mul_zero]; rfl

/-- Cofactor expansion of `det5W` along the second vector. -/
theorem det5W_expand_second (x1 x2 x3 x4 x5 : BitVec 30) :
    det5W x1 x2 x3 x4 x5 =
      gf32Mul (chunkW x2 1) (det4W x1 x3 x4 x5 2 3 4 5) ^^^
        gf32Mul (chunkW x2 2) (det4W x1 x3 x4 x5 1 3 4 5) ^^^
        gf32Mul (chunkW x2 3) (det4W x1 x3 x4 x5 1 2 4 5) ^^^
        gf32Mul (chunkW x2 4) (det4W x1 x3 x4 x5 1 2 3 5) ^^^
        gf32Mul (chunkW x2 5) (det4W x1 x3 x4 x5 1 2 3 4) := by
  simp only [det5W, det4W, det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right,
    gf32Mul_swap_head, gf32Mul_swap_tail5]
  ac_rfl

/-- Cofactor expansion of `det5W` along the fifth vector. -/
theorem det5W_expand_fifth (x1 x2 x3 x4 x5 : BitVec 30) :
    det5W x1 x2 x3 x4 x5 =
      gf32Mul (chunkW x5 1) (det4W x1 x2 x3 x4 2 3 4 5) ^^^
        gf32Mul (chunkW x5 2) (det4W x1 x2 x3 x4 1 3 4 5) ^^^
        gf32Mul (chunkW x5 3) (det4W x1 x2 x3 x4 1 2 4 5) ^^^
        gf32Mul (chunkW x5 4) (det4W x1 x2 x3 x4 1 2 3 5) ^^^
        gf32Mul (chunkW x5 5) (det4W x1 x2 x3 x4 1 2 3 4) := by
  simp only [det5W, det4W, det3W, det2W, gf32Mul_xor_left, gf32Mul_xor_right,
    gf32Mul_swap_head, gf32Mul_swap_tail5]
  ac_rfl

theorem det5W_rep_fst (y z w u : BitVec 30) :
    det5W y y z w u = 0 := by
  rw [det5W_expand_fifth, det4W_rep_fst, det4W_rep_fst, det4W_rep_fst,
    det4W_rep_fst, det4W_rep_fst, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero,
    gf32Mul_zero, gf32Mul_zero]; rfl

theorem det5W_rep_13 (z y w u : BitVec 30) :
    det5W z y z w u = 0 := by
  rw [det5W_expand_fifth, det4W_rep_13, det4W_rep_13, det4W_rep_13,
    det4W_rep_13, det4W_rep_13, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero,
    gf32Mul_zero, gf32Mul_zero]; rfl

theorem det5W_rep_14 (w y z u : BitVec 30) :
    det5W w y z w u = 0 := by
  rw [det5W_expand_fifth, det4W_rep_14, det4W_rep_14, det4W_rep_14,
    det4W_rep_14, det4W_rep_14, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero,
    gf32Mul_zero, gf32Mul_zero]; rfl

theorem det5W_rep_15 (u y z w : BitVec 30) :
    det5W u y z w u = 0 := by
  rw [det5W_expand_second, det4W_rep_14, det4W_rep_14, det4W_rep_14,
    det4W_rep_14, det4W_rep_14, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero,
    gf32Mul_zero, gf32Mul_zero]; rfl

/-- Cramer identity, `5×5` at the top coordinates. -/
theorem cramer5 (x1 x2 x3 x4 x5 : BitVec 30) (a b c d e : Word)
    (h1 : gf32Mul a (chunkW x1 1) ^^^ gf32Mul b (chunkW x2 1) ^^^
      gf32Mul c (chunkW x3 1) ^^^ gf32Mul d (chunkW x4 1) ^^^
      gf32Mul e (chunkW x5 1) = 0)
    (h2 : gf32Mul a (chunkW x1 2) ^^^ gf32Mul b (chunkW x2 2) ^^^
      gf32Mul c (chunkW x3 2) ^^^ gf32Mul d (chunkW x4 2) ^^^
      gf32Mul e (chunkW x5 2) = 0)
    (h3 : gf32Mul a (chunkW x1 3) ^^^ gf32Mul b (chunkW x2 3) ^^^
      gf32Mul c (chunkW x3 3) ^^^ gf32Mul d (chunkW x4 3) ^^^
      gf32Mul e (chunkW x5 3) = 0)
    (h4 : gf32Mul a (chunkW x1 4) ^^^ gf32Mul b (chunkW x2 4) ^^^
      gf32Mul c (chunkW x3 4) ^^^ gf32Mul d (chunkW x4 4) ^^^
      gf32Mul e (chunkW x5 4) = 0)
    (h5 : gf32Mul a (chunkW x1 5) ^^^ gf32Mul b (chunkW x2 5) ^^^
      gf32Mul c (chunkW x3 5) ^^^ gf32Mul d (chunkW x4 5) ^^^
      gf32Mul e (chunkW x5 5) = 0) :
    gf32Mul a (det5W x1 x2 x3 x4 x5) = 0 := by
  have ha1 : gf32Mul a (chunkW x1 1) =
      gf32Mul b (chunkW x2 1) ^^^ gf32Mul c (chunkW x3 1) ^^^
        gf32Mul d (chunkW x4 1) ^^^ gf32Mul e (chunkW x5 1) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
      exact h1)
  have ha2 : gf32Mul a (chunkW x1 2) =
      gf32Mul b (chunkW x2 2) ^^^ gf32Mul c (chunkW x3 2) ^^^
        gf32Mul d (chunkW x4 2) ^^^ gf32Mul e (chunkW x5 2) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
      exact h2)
  have ha3 : gf32Mul a (chunkW x1 3) =
      gf32Mul b (chunkW x2 3) ^^^ gf32Mul c (chunkW x3 3) ^^^
        gf32Mul d (chunkW x4 3) ^^^ gf32Mul e (chunkW x5 3) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
      exact h3)
  have ha4 : gf32Mul a (chunkW x1 4) =
      gf32Mul b (chunkW x2 4) ^^^ gf32Mul c (chunkW x3 4) ^^^
        gf32Mul d (chunkW x4 4) ^^^ gf32Mul e (chunkW x5 4) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
      exact h4)
  have ha5 : gf32Mul a (chunkW x1 5) =
      gf32Mul b (chunkW x2 5) ^^^ gf32Mul c (chunkW x3 5) ^^^
        gf32Mul d (chunkW x4 5) ^^^ gf32Mul e (chunkW x5 5) := by
    exact xor_eq_zero_imp (by
      rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, ← BitVec.xor_assoc]
      exact h5)
  calc gf32Mul a (det5W x1 x2 x3 x4 x5)
      = gf32Mul (gf32Mul a (chunkW x1 1)) (det4W x2 x3 x4 x5 2 3 4 5) ^^^
          gf32Mul (gf32Mul a (chunkW x1 2)) (det4W x2 x3 x4 x5 1 3 4 5) ^^^
          gf32Mul (gf32Mul a (chunkW x1 3)) (det4W x2 x3 x4 x5 1 2 4 5) ^^^
          gf32Mul (gf32Mul a (chunkW x1 4)) (det4W x2 x3 x4 x5 1 2 3 5) ^^^
          gf32Mul (gf32Mul a (chunkW x1 5)) (det4W x2 x3 x4 x5 1 2 3 4) := by
        simp only [det5W, gf32Mul_xor_right, ← gf32Mul_assoc]
    _ = gf32Mul b (det5W x2 x2 x3 x4 x5) ^^^
          gf32Mul c (det5W x3 x2 x3 x4 x5) ^^^
          gf32Mul d (det5W x4 x2 x3 x4 x5) ^^^
          gf32Mul e (det5W x5 x2 x3 x4 x5) := by
        rw [ha1, ha2, ha3, ha4, ha5]
        simp only [det5W, gf32Mul_xor_left, gf32Mul_xor_right, gf32Mul_assoc]
        ac_rfl
    _ = 0 := by
        rw [det5W_rep_fst, det5W_rep_13, det5W_rep_14, det5W_rep_15,
          gf32Mul_zero, gf32Mul_zero, gf32Mul_zero, gf32Mul_zero]; rfl
/-! ## Certificate extraction -/

theorem synEntry_ofNat (d : Nat) (hd : d < 173) :
    synEntry d = (syn d 1).toNat := by
  have h := synEntry_eq (BitVec.ofNat 10 d) (by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 1024)]
    exact hd)
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 1024)] at h

theorem synTop_ne_zero (d : Nat) (h1 : 1 ≤ d) (h2 : d ≤ 172) :
    ∃ m : Nat, 1 ≤ m ∧ m ≤ 5 ∧ chunkW (syn d 1) m ≠ 0 := by
  refine Classical.byContradiction fun hcon => ?_
  have hcon : ∀ m : Nat, 1 ≤ m → m ≤ 5 → chunkW (syn d 1) m = 0 := by
    intro m hm1 hm2
    by_cases hne : chunkW (syn d 1) m = 0
    · exact hne
    · exact absurd ⟨m, hm1, hm2, hne⟩ hcon
  have hcert : synEntry d >>> 5 ≠ 0 := by
    have hc := certTopNe_eq
    unfold certTopNe at hc
    have h := List.all_eq_true.mp hc (d - 1) (List.mem_range.mpr (by omega))
    have h2 : (synEntry d >>> 5 != 0) = true := by
      have hd1 : d - 1 + 1 = d := by omega
      simpa [hd1] using h
    intro hz
    rw [hz] at h2
    simp at h2
  have hzero : (syn d 1).toNat >>> 5 = 0 := by
    have hx : (syn d 1).toNat < 2 ^ 30 := (syn d 1).isLt
    have hc : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
        ((syn d 1).toNat >>> (5 * m)) % 32 = 0 := by
      intro m hm1 hm2
      have h := hcon m hm1 hm2
      have h2 : (chunkW (syn d 1) m).toNat = 0 := by rw [h]; rfl
      rwa [chunkW_toNat] at h2
    have h1 := hc 1 (by decide) (by decide)
    have h2 := hc 2 (by decide) (by decide)
    have h3 := hc 3 (by decide) (by decide)
    have h4 := hc 4 (by decide) (by decide)
    have h5 := hc 5 (by decide) (by decide)
    omega
  rw [synEntry_ofNat d (by omega)] at hcert
  exact hcert hzero

theorem exists_det2 (d1 d2 : Nat) (h2 : 1 ≤ d2) (h12 : d2 < d1) (h1 : d1 ≤ 172) :
    ∃ i j : Nat, (i, j) ∈ coordPairs ∧ det2W (syn d1 1) (syn d2 1) i j ≠ 0 := by
  have hc := cert2_eq
  unfold cert2 at hc
  have h1' := List.all_eq_true.mp hc (d1 - 2) (List.mem_range.mpr (by omega))
  have h2' := List.all_eq_true.mp h1' (d2 - 1) (List.mem_range.mpr (by omega))
  simp only [show d1 - 2 + 2 = d1 by omega, show d2 - 1 + 1 = d2 by omega] at h2'
  unfold minor2Ok at h2'
  obtain ⟨p, hp_mem, hp_ne⟩ := List.any_eq_true.mp h2'
  have hp_ne : (det2Nat (synEntry d1) (synEntry d2) p.1 p.2 != 0) = true :=
    hp_ne
  refine ⟨p.1, p.2, hp_mem, ?_⟩
  have hne : det2Nat (synEntry d1) (synEntry d2) p.1 p.2 ≠ 0 := by
    intro hz
    rw [hz] at hp_ne
    simp at hp_ne
  intro hzero
  apply hne
  have h3 : (det2W (syn d1 1) (syn d2 1) p.1 p.2).toNat = 0 := by rw [hzero]; rfl
  rw [det2W_toNat, ← synEntry_ofNat d1 (by omega),
    ← synEntry_ofNat d2 (by omega)] at h3
  exact h3

theorem exists_det3 (d1 d2 d3 : Nat) (h3 : 1 ≤ d3) (h32 : d3 < d2)
    (h21 : d2 < d1) (h1 : d1 ≤ 88) :
    ∃ i j k : Nat, (i, j, k) ∈ coordTriples ∧
      det3W (syn d1 1) (syn d2 1) (syn d3 1) i j k ≠ 0 := by
  have hc := cert3_eq
  unfold cert3 at hc
  have h1' := List.all_eq_true.mp hc (d1 - 3) (List.mem_range.mpr (by omega))
  have h2' := List.all_eq_true.mp h1' (d2 - 2) (List.mem_range.mpr (by omega))
  have h3' := List.all_eq_true.mp h2' (d3 - 1) (List.mem_range.mpr (by omega))
  simp only [show d1 - 3 + 3 = d1 by omega, show d2 - 2 + 2 = d2 by omega,
    show d3 - 1 + 1 = d3 by omega] at h3'
  unfold minor3Ok at h3'
  obtain ⟨p, hp_mem, hp_ne⟩ := List.any_eq_true.mp h3'
  have hp_ne : (det3Nat (synEntry d1) (synEntry d2) (synEntry d3)
    p.1 p.2.1 p.2.2 != 0) = true := hp_ne
  refine ⟨p.1, p.2.1, p.2.2, hp_mem, ?_⟩
  have hne : det3Nat (synEntry d1) (synEntry d2) (synEntry d3) p.1 p.2.1 p.2.2 ≠ 0 := by
    intro hz
    rw [hz] at hp_ne
    simp at hp_ne
  intro hzero
  apply hne
  have h4 : (det3W (syn d1 1) (syn d2 1) (syn d3 1) p.1 p.2.1 p.2.2).toNat = 0 := by
    rw [hzero]; rfl
  rw [det3W_toNat, ← synEntry_ofNat d1 (by omega),
    ← synEntry_ofNat d2 (by omega), ← synEntry_ofNat d3 (by omega)] at h4
  exact h4

theorem exists_det4 (d1 d2 d3 d4 : Nat) (h4 : 1 ≤ d4) (h43 : d4 < d3)
    (h32 : d3 < d2) (h21 : d2 < d1) (h1 : d1 ≤ 17) :
    ∃ i j k l : Nat, (i, j, k, l) ∈ coordQuads ∧
      det4W (syn d1 1) (syn d2 1) (syn d3 1) (syn d4 1) i j k l ≠ 0 := by
  have hc := cert4_eq
  unfold cert4 at hc
  have h1' := List.all_eq_true.mp hc (d1 - 4) (List.mem_range.mpr (by omega))
  have h2' := List.all_eq_true.mp h1' (d2 - 3) (List.mem_range.mpr (by omega))
  have h3' := List.all_eq_true.mp h2' (d3 - 2) (List.mem_range.mpr (by omega))
  have h4' := List.all_eq_true.mp h3' (d4 - 1) (List.mem_range.mpr (by omega))
  simp only [show d1 - 4 + 4 = d1 by omega, show d2 - 3 + 3 = d2 by omega,
    show d3 - 2 + 2 = d3 by omega, show d4 - 1 + 1 = d4 by omega] at h4'
  unfold minor4Ok at h4'
  obtain ⟨p, hp_mem, hp_ne⟩ := List.any_eq_true.mp h4'
  have hp_ne : (det4Nat (synEntry d1) (synEntry d2) (synEntry d3)
    (synEntry d4) p.1 p.2.1 p.2.2.1 p.2.2.2 != 0) = true := hp_ne
  refine ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, hp_mem, ?_⟩
  have hne : det4Nat (synEntry d1) (synEntry d2) (synEntry d3) (synEntry d4)
      p.1 p.2.1 p.2.2.1 p.2.2.2 ≠ 0 := by
    intro hz
    rw [hz] at hp_ne
    simp at hp_ne
  intro hzero
  apply hne
  have h5 : (det4W (syn d1 1) (syn d2 1) (syn d3 1) (syn d4 1)
      p.1 p.2.1 p.2.2.1 p.2.2.2).toNat = 0 := by
    rw [hzero]; rfl
  rw [det4W_toNat, ← synEntry_ofNat d1 (by omega),
    ← synEntry_ofNat d2 (by omega), ← synEntry_ofNat d3 (by omega),
    ← synEntry_ofNat d4 (by omega)] at h5
  exact h5

theorem exists_det5 (d1 d2 d3 d4 d5 : Nat) (h5 : 1 ≤ d5) (h54 : d5 < d4)
    (h43 : d4 < d3) (h32 : d3 < d2) (h21 : d2 < d1) (h1 : d1 ≤ 7) :
    det5W (syn d1 1) (syn d2 1) (syn d3 1) (syn d4 1) (syn d5 1) ≠ 0 := by
  have hc := cert5_eq
  unfold cert5 at hc
  have h1' := List.all_eq_true.mp hc (d1 - 5) (List.mem_range.mpr (by omega))
  have h2' := List.all_eq_true.mp h1' (d2 - 4) (List.mem_range.mpr (by omega))
  have h3' := List.all_eq_true.mp h2' (d3 - 3) (List.mem_range.mpr (by omega))
  have h4' := List.all_eq_true.mp h3' (d4 - 2) (List.mem_range.mpr (by omega))
  have h5' := List.all_eq_true.mp h4' (d5 - 1) (List.mem_range.mpr (by omega))
  simp only [show d1 - 5 + 5 = d1 by omega, show d2 - 4 + 4 = d2 by omega,
    show d3 - 3 + 3 = d3 by omega, show d4 - 2 + 2 = d4 by omega,
    show d5 - 1 + 1 = d5 by omega] at h5'
  have hne : det5Nat (synEntry d1) (synEntry d2) (synEntry d3) (synEntry d4)
      (synEntry d5) ≠ 0 := by
    intro hz
    rw [hz] at h5'
    simp at h5'
  intro hzero
  apply hne
  have h6 : (det5W (syn d1 1) (syn d2 1) (syn d3 1) (syn d4 1)
      (syn d5 1)).toNat = 0 := by
    rw [hzero]; rfl
  rw [det5W_toNat, ← synEntry_ofNat d1 (by omega),
    ← synEntry_ofNat d2 (by omega), ← synEntry_ofNat d3 (by omega),
    ← synEntry_ofNat d4 (by omega), ← synEntry_ofNat d5 (by omega)] at h6
  exact h6

/-! ## Impulse decomposition of a zero-state fold -/

/-- The impulse decomposition of a stream: `(distance from end, value)` for
    each nonzero symbol, in decreasing distance order. -/
def decomp : List Word → List (Nat × Word)
  | [] => []
  | a :: es => (if a = 0 then [] else [(es.length, a)]) ++ decomp es

theorem polymodStep_zero_left (v : Word) : polymodStep 0 v = v.setWidth 30 := by
  simp [polymodStep]

theorem foldl_polymodStep_from (xs : List Word) (s t : BitVec 30) :
    xs.foldl polymodStep (s ^^^ t) =
      xs.foldl polymodStep s ^^^
        (List.replicate xs.length 0).foldl polymodStep t := by
  induction xs generalizing s t with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, List.replicate_succ,
      List.foldl_cons]
    have hx : polymodStep (s ^^^ t) x = polymodStep s x ^^^ polymodStep t 0 := by
      have h := polymodStep_xor s t x 0
      simpa using h
    rw [hx, ih]

theorem fold_eq_xorsum (es : List Word) :
    es.foldl polymodStep 0 =
      (decomp es).foldr (fun p acc => syn p.1 p.2 ^^^ acc) 0 := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    have hstep : (a :: es).foldl polymodStep 0 =
        es.foldl polymodStep 0 ^^^ syn es.length a := by
      simp only [List.foldl_cons, polymodStep_zero_left]
      have hz : (0 : BitVec 30) ^^^ a.setWidth 30 = a.setWidth 30 :=
        BitVec.zero_xor
      rw [← hz, foldl_polymodStep_from]
      rfl
    rw [hstep, ih]
    by_cases ha : a = 0
    · subst ha
      rw [show decomp ((0 : Word) :: es) = decomp es by simp [decomp],
        syn_zero_val]
      exact BitVec.xor_zero
    · simp only [decomp, ha, if_false, List.cons_append, List.nil_append]
      show (decomp es).foldr (fun p acc => syn p.1 p.2 ^^^ acc) 0 ^^^
          syn es.length a =
        syn es.length a ^^^
          (decomp es).foldr (fun p acc => syn p.1 p.2 ^^^ acc) 0
      exact BitVec.xor_comm _ _

theorem decomp_length (es : List Word) :
    (decomp es).length = hammingWeight es := by
  induction es with
  | nil => rfl
  | cons a es ih =>
    by_cases ha : a = 0
    · subst ha
      have hd : decomp ((0 : Word) :: es) = decomp es := by simp [decomp]
      have hw : hammingWeight ((0 : Word) :: es) = hammingWeight es := by
        simp [hammingWeight]
      rw [hd, hw, ih]
    · have hd : decomp (a :: es) = (es.length, a) :: decomp es := by
        simp only [decomp, if_neg ha, List.cons_append, List.nil_append]
      have hw : hammingWeight (a :: es) = hammingWeight es + 1 := by
        have hd2 : decide (a ≠ 0) = true := decide_eq_true_eq.mpr ha
        show ((a :: es).filter (· ≠ 0)).length = hammingWeight es + 1
        rw [List.filter_cons]
        simp only [hd2]
        rfl
      rw [hd, hw, List.length_cons, ih]

theorem decomp_snd_ne {p : Nat × Word} : ∀ {es : List Word},
    p ∈ decomp es → p.2 ≠ 0 := by
  intro es
  induction es with
  | nil => intro hp; simp [decomp] at hp
  | cons a es ih =>
    intro hp
    simp only [decomp] at hp
    by_cases ha : a = 0
    · subst ha
      exact ih (by simpa [decomp] using hp)
    · simp only [ha, if_false, List.cons_append, List.nil_append] at hp
      rcases List.mem_cons.mp hp with rfl | h
      · exact ha
      · exact ih h

theorem decomp_fst_lt {p : Nat × Word} : ∀ {es : List Word},
    p ∈ decomp es → p.1 < es.length := by
  intro es
  induction es with
  | nil => intro hp; simp [decomp] at hp
  | cons a es ih =>
    intro hp
    simp only [decomp, List.length_cons] at hp ⊢
    by_cases ha : a = 0
    · subst ha
      have := ih (by simpa [decomp] using hp)
      omega
    · simp only [ha, if_false, List.cons_append, List.nil_append] at hp
      rcases List.mem_cons.mp hp with rfl | h
      · exact Nat.lt_succ_self _
      · have := ih h; omega

theorem decomp_pairwise (es : List Word) :
    (decomp es).Pairwise (fun p q => p.1 > q.1) := by
  induction es with
  | nil => exact List.Pairwise.nil
  | cons a es ih =>
    by_cases ha : a = 0
    · subst ha
      simpa [decomp] using ih
    · have hdecomp : decomp (a :: es) = (es.length, a) :: decomp es := by
        simp only [decomp, if_neg ha, List.cons_append, List.nil_append]
      rw [hdecomp]
      refine List.Pairwise.cons (fun p hp => ?_) ih
      have h := decomp_fst_lt hp
      exact h

theorem decomp_append_singleton (es : List Word) (x : Word) :
    decomp (es ++ [x]) =
      (decomp es).map (fun p => (p.1 + 1, p.2)) ++
        (if x = 0 then [] else [(0, x)]) := by
  induction es with
  | nil => simp [decomp]
  | cons a es ih =>
    simp only [List.cons_append, decomp]
    rw [ih]
    by_cases ha : a = 0
    · subst ha
      simp
    · simp only [ha, if_false, List.cons_append, List.nil_append,
        List.map_append, List.map_cons]
      congr 2
      simp [List.length_append]

theorem scale_foldr_syn (c : Word) (L : List (Nat × Word)) :
    scaleState c (L.foldr (fun p acc => syn p.1 p.2 ^^^ acc) 0) =
      (L.map (fun p => (p.1, gf32Mul c p.2))).foldr
        (fun p acc => syn p.1 p.2 ^^^ acc) 0 := by
  induction L with
  | nil => exact scaleState_zero_state c
  | cons p L ih =>
    simp only [List.foldr_cons, List.map_cons, ← ih, scaleState_xor, syn_scale]

theorem chunkW_foldr_syn (L : List (Nat × Word)) (m : Nat) (hm : m < 6) :
    chunkW (L.foldr (fun p acc => syn p.1 p.2 ^^^ acc) 0) m =
      L.foldr (fun p acc => gf32Mul p.2 (chunkW (syn p.1 1) m) ^^^ acc) 0 := by
  induction L with
  | nil => exact chunkW_zero m
  | cons p L ih =>
    simp only [List.foldr_cons, ← ih, chunkW_xor]
    congr 1
    have h : syn p.1 p.2 = scaleState p.2 (syn p.1 1) := by
      have h2 := syn_scale p.2 p.1 1
      rwa [gf32Mul_one] at h2
    rw [h, chunkW_scaleState _ _ m hm]

theorem coordPairs_bounds {i j : Nat} (h : (i, j) ∈ coordPairs) :
    1 ≤ i ∧ i ≤ 5 ∧ 1 ≤ j ∧ j ≤ 5 := by
  simp only [coordPairs, List.mem_cons, List.mem_singleton, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem coordTriples_bounds {i j k : Nat} (h : (i, j, k) ∈ coordTriples) :
    1 ≤ i ∧ i ≤ 5 ∧ 1 ≤ j ∧ j ≤ 5 ∧ 1 ≤ k ∧ k ≤ 5 := by
  simp only [coordTriples, List.mem_cons, List.mem_singleton, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega

theorem coordQuads_bounds {i j k l : Nat} (h : (i, j, k, l) ∈ coordQuads) :
    1 ≤ i ∧ i ≤ 5 ∧ 1 ≤ j ∧ j ≤ 5 ∧ 1 ≤ k ∧ k ≤ 5 ∧ 1 ≤ l ∧ l ≤ 5 := by
  simp only [coordQuads, List.mem_cons, List.mem_singleton, Prod.mk.injEq,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> omega

/-- The core distance lemma, by induction on a length fuel (for stripping
    trailing zeros).  A zero-state fold of positive weight is impossible in
    each of the four `(weight, length)` regimes certified above. -/
theorem fold_eq_zero_weight (n : Nat) : ∀ (es : List Word),
    es.length ≤ n → es.foldl polymodStep 0 = 0 →
    ((hammingWeight es ≤ 3 ∧ es.length ≤ 173) ∨
     (hammingWeight es ≤ 4 ∧ es.length ≤ 89) ∨
     (hammingWeight es ≤ 5 ∧ es.length ≤ 18) ∨
     (hammingWeight es ≤ 6 ∧ es.length ≤ 8)) →
    hammingWeight es = 0 := by
  induction n with
  | zero =>
    intro es hlen _ _
    have : es = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro es hlen hfold hcase
    by_cases hes : es = []
    · subst hes
      rfl
    · obtain ⟨init, hinit_def⟩ : ∃ l : List Word, l = es.dropLast :=
        ⟨_, rfl⟩
      obtain ⟨last, hlast_def⟩ : ∃ w : Word, w = es.getLast hes :=
        ⟨_, rfl⟩
      have hsplit : init ++ [last] = es := by
        rw [hinit_def, hlast_def]
        exact List.dropLast_concat_getLast hes
      by_cases hlast0 : last = 0
      · -- Strip the trailing zero and recurse.
        have hfold_init : init.foldl polymodStep 0 = 0 := by
          have h1 : es.foldl polymodStep 0 =
              polymodStep (init.foldl polymodStep 0) last := by
            rw [← hsplit, List.foldl_append]; rfl
          have h2 : polymodStep (init.foldl polymodStep 0) last = 0 :=
            h1.symm.trans hfold
          rw [hlast0] at h2
          exact polymodStep_zero_inj h2
        have hweight : hammingWeight init = hammingWeight es := by
          have h3 : hammingWeight (init ++ [last]) = hammingWeight init := by
            simp [hammingWeight, List.filter_append, hlast0]
          rw [hsplit] at h3
          exact h3.symm
        have hlen_init : init.length ≤ n := by
          have h1 : init.length = es.length - 1 := by
            rw [hinit_def]; exact List.length_dropLast
          omega
        have hcase' : (hammingWeight init ≤ 3 ∧ init.length ≤ 173) ∨
            (hammingWeight init ≤ 4 ∧ init.length ≤ 89) ∨
            (hammingWeight init ≤ 5 ∧ init.length ≤ 18) ∨
            (hammingWeight init ≤ 6 ∧ init.length ≤ 8) := by
          have hli : init.length ≤ es.length := by
            have h1 : init.length = es.length - 1 := by
              rw [hinit_def]; exact List.length_dropLast
            omega
          rcases hcase with ⟨hw, hl⟩ | ⟨hw, hl⟩ | ⟨hw, hl⟩ | ⟨hw, hl⟩
          · exact Or.inl ⟨by rw [hweight]; exact hw, by omega⟩
          · exact Or.inr (Or.inl ⟨by rw [hweight]; exact hw, by omega⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨by rw [hweight]; exact hw, by omega⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨by rw [hweight]; exact hw, by omega⟩))
        have hres := ih init hlen_init hfold_init hcase'
        exact hweight.symm.trans hres
      · -- `last ≠ 0`: the impulse decomposition argument.
        have hdecomp_form : decomp es =
            (decomp init).map (fun p => (p.1 + 1, p.2)) ++ [(0, last)] := by
          have h := decomp_append_singleton init last
          rwa [hsplit, if_neg hlast0] at h
        by_cases hr0 : hammingWeight es = 0
        · exact hr0
        by_cases hr1 : hammingWeight es = 1
        · have hlen_decomp : (decomp es).length = 1 := by
            rw [decomp_length]; exact hr1
          have hLd : (decomp init).length = 0 := by
            have h2 := congrArg List.length hdecomp_form
            rw [List.length_append, List.length_map, List.length_singleton] at h2
            omega
          have hLd_nil : decomp init = [] := List.eq_nil_of_length_eq_zero hLd
          have hdecomp1 : decomp es = [(0, last)] := by
            rw [hdecomp_form, hLd_nil]; simp
          rw [fold_eq_xorsum, hdecomp1] at hfold
          simp only [List.foldr_cons, List.foldr_nil] at hfold
          have hxz : syn 0 last ^^^ (0 : BitVec 30) = syn 0 last :=
            BitVec.xor_zero
          rw [hxz] at hfold
          exact (syn_ne_zero hlast0 hfold).elim
        · -- Weight at least 2: normalize and apply the certificates.
          have hr_ge : 2 ≤ hammingWeight es := by omega
          have hr_le : hammingWeight es ≤ 6 := by
            rcases hcase with h | h | h | h <;> omega
          have hlen173 : es.length ≤ 173 := by
            rcases hcase with h | h | h | h <;> omega
          obtain ⟨q, Lq, hq⟩ : ∃ q : Nat × Word,
              ∃ Lq : List (Nat × Word), decomp init = q :: Lq := by
            apply List.exists_cons_of_ne_nil
            intro hnil
            rw [hnil] at hdecomp_form
            have hlen1 : (decomp es).length = 1 := by simp [hdecomp_form]
            rw [decomp_length] at hlen1
            exact hr1 hlen1
          have hdecomp_es : decomp es = (q.1 + 1, q.2) ::
              ((Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)]) := by
            rw [hdecomp_form, hq]
            simp [List.map_cons]
          have hq_mem : q ∈ decomp init := by
            rw [hq]; exact List.mem_cons_self
          have hv1ne : q.2 ≠ 0 := decomp_snd_ne hq_mem
          have hd1 : q.1 + 1 < es.length :=
            decomp_fst_lt (p := (q.1 + 1, q.2))
              (by rw [hdecomp_es]; exact List.mem_cons_self)
          have hpair : (decomp es).Pairwise (fun p q => p.1 > q.1) :=
            decomp_pairwise es
          rw [hdecomp_es] at hpair
          obtain ⟨hhead_rel, hpair_rest⟩ := List.pairwise_cons.mp hpair
          obtain ⟨c, hc_def⟩ : ∃ w : Word, w = gf32Inv q.2 := ⟨_, rfl⟩
          have hhead_val : gf32Mul c q.2 = 1 := by
            rw [hc_def]; exact gf32Inv_mul_cancel hv1ne
          have hchunk : ∀ m : Nat, m < 6 →
              ((decomp es).map (fun p => (p.1, gf32Mul c p.2))).foldr
                (fun p acc => gf32Mul p.2 (chunkW (syn p.1 1) m) ^^^ acc) 0 = 0 := by
            intro m hm
            have h1 : scaleState c (es.foldl polymodStep 0) = 0 := by
              rw [hfold]; exact scaleState_zero_state _
            rw [fold_eq_xorsum] at h1
            rw [scale_foldr_syn] at h1
            have h2 := congrArg (fun z => chunkW z m) h1
            rw [chunkW_foldr_syn _ m hm, chunkW_zero] at h2
            exact h2
          have hLs : (decomp es).map (fun p => (p.1, gf32Mul c p.2)) =
              ((decomp init).map (fun p => (p.1 + 1, gf32Mul c p.2))) ++
                [(0, gf32Mul c last)] := by
            rw [hdecomp_form, List.map_append, List.map_map]
            rfl
          have hprefix : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
              ((decomp init).map (fun p => (p.1 + 1, gf32Mul c p.2))).foldr
                (fun p acc => gf32Mul p.2 (chunkW (syn p.1 1) m) ^^^ acc) 0 = 0 := by
            intro m hm1 hm2
            have h := hchunk m (by omega)
            rw [hLs, List.foldr_append] at h
            have hcw : chunkW (syn 0 1) m = 0 := by
              rw [syn_zero, chunkW_setWidth]
              exact if_neg (by omega : ¬ m = 0)
            simp only [List.foldr_cons, List.foldr_nil, hcw, gf32Mul_zero]
              at h
            have hxz : (0 : Word) ^^^ (0 : Word) = (0 : Word) :=
              BitVec.zero_xor
            rw [hxz] at h
            exact h
          have hprefix_form : (decomp init).map
                (fun p => (p.1 + 1, gf32Mul c p.2)) =
              (q.1 + 1, gf32Mul c q.2) ::
                (Lq.map (fun p => (p.1 + 1, gf32Mul c p.2))) := by
            rw [hq]; rfl
          have hlenLq : Lq.length = hammingWeight es - 2 := by
            have h1 : (decomp init).length = hammingWeight es - 1 := by
              have h2 := congrArg List.length hdecomp_form
              rw [List.length_append, List.length_map, List.length_singleton,
                decomp_length] at h2
              omega
            rw [hq] at h1
            simp at h1
            omega
          -- Case analysis on the weight.
          rcases (show hammingWeight es = 2 ∨ hammingWeight es = 3 ∨
              hammingWeight es = 4 ∨ hammingWeight es = 5 ∨
              hammingWeight es = 6 by omega) with h2 | h3 | h4 | h5 | h6
          · -- weight = 2
            have hLq : Lq = [] :=
              List.eq_nil_of_length_eq_zero (by omega)
            have hcheq : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
                chunkW (syn (q.1 + 1) 1) m = 0 := by
              intro m hm1 hm2
              have h := hprefix m hm1 hm2
              rw [hprefix_form, hLq] at h
              simp only [List.map_nil, List.foldr_cons, List.foldr_nil] at h
              have hxz : gf32Mul (gf32Mul c q.2) (chunkW (syn (q.1 + 1) 1) m)
                  ^^^ (0 : Word) =
                  gf32Mul (gf32Mul c q.2) (chunkW (syn (q.1 + 1) 1) m) :=
                BitVec.xor_zero
              rw [hxz, hhead_val, gf32One_mul] at h
              exact h
            obtain ⟨m, hm1, hm2, hne⟩ := synTop_ne_zero (q.1 + 1) (by omega)
              (by omega)
            exact (hne (hcheq m hm1 hm2)).elim
          · -- weight = 3
            obtain ⟨q2, Lq2, hq2c⟩ : ∃ q2 : Nat × Word,
                ∃ Lq2 : List (Nat × Word), Lq = q2 :: Lq2 := by
              apply List.exists_cons_of_ne_nil
              intro hn
              rw [hn] at hlenLq
              simp only [List.length_nil] at hlenLq
              omega
            have hLq2 : Lq2 = [] := List.eq_nil_of_length_eq_zero (by
              rw [hq2c] at hlenLq
              simp only [List.length_cons] at hlenLq
              omega)
            have hq2 : Lq = [q2] := by rw [hq2c, hLq2]
            have hq2_mem : (q2.1 + 1, q2.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2]
              simp
            have hd12 : q2.1 + 1 < q.1 + 1 := by
              have h := hhead_rel _ hq2_mem
              exact h
            have hcheq : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
                gf32Mul 1 (chunkW (syn (q.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m) = 0 := by
              intro m hm1 hm2
              have h := hprefix m hm1 hm2
              rw [hprefix_form, hq2] at h
              simp only [List.map_cons, List.map_nil, List.foldr_cons,
                List.foldr_nil] at h
              have hxz : gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m)
                  ^^^ (0 : Word) =
                  gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m) :=
                BitVec.xor_zero
              rw [hxz, hhead_val] at h
              exact h
            obtain ⟨i, j, hij_mem, hdet⟩ := exists_det2 (q.1 + 1) (q2.1 + 1)
              (by omega) (by omega) (by omega)
            have hb := coordPairs_bounds hij_mem
            have hcram := cramer2 (syn (q.1 + 1) 1) (syn (q2.1 + 1) 1) 1
              (gf32Mul c q2.2) i j (hcheq i hb.1 hb.2.1) (hcheq j hb.2.2.1 hb.2.2.2)
            rw [gf32One_mul] at hcram
            exact (hdet hcram).elim
          · -- weight = 4
            have hlen89 : es.length ≤ 89 := by
              rcases hcase with h | h | h | h <;> omega
            obtain ⟨q2, Lq2, hq2⟩ : ∃ q2 Lq2, Lq = q2 :: Lq2 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hnil] at hlenLq
                simp only [List.length_nil] at hlenLq
                omega)
            obtain ⟨q3, Lq3, hq3c⟩ : ∃ q3 : Nat × Word,
                ∃ Lq3 : List (Nat × Word), Lq2 = q3 :: Lq3 := by
              apply List.exists_cons_of_ne_nil
              intro hn
              rw [hq2, hn] at hlenLq
              simp only [List.length_cons, List.length_nil] at hlenLq
              omega
            have hLq3 : Lq3 = [] := List.eq_nil_of_length_eq_zero (by
              rw [hq2, hq3c] at hlenLq
              simp only [List.length_cons] at hlenLq
              omega)
            have hq3 : Lq2 = [q3] := by rw [hq3c, hLq3]
            have hq2_mem : (q2.1 + 1, q2.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2]; simp
            have hq3_mem : (q3.1 + 1, q3.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3]; simp
            have hd12 : q2.1 + 1 < q.1 + 1 := hhead_rel _ hq2_mem
            have hd13 : q3.1 + 1 < q.1 + 1 := hhead_rel _ hq3_mem
            have hd23 : q3.1 + 1 < q2.1 + 1 := by
              have hpair2 : ((Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++
                  [(0, last)]).Pairwise (fun p q : Nat × Word => p.1 > q.1) :=
              hpair_rest
              rw [hq2] at hpair2
              simp only [List.map_cons, List.cons_append] at hpair2
              obtain ⟨hrel2, -⟩ := List.pairwise_cons.mp hpair2
              have hmem : (q3.1 + 1, q3.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3]; simp
              exact hrel2 _ hmem
            have hcheq : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
                gf32Mul 1 (chunkW (syn (q.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q3.2) (chunkW (syn (q3.1 + 1) 1) m) = 0 := by
              intro m hm1 hm2
              have h := hprefix m hm1 hm2
              rw [hprefix_form, hq2, hq3] at h
              simp only [List.map_cons, List.map_nil, List.foldr_cons,
                List.foldr_nil] at h
              have hxz : gf32Mul (gf32Mul c q3.2) (chunkW (syn (q3.1 + 1) 1) m)
                  ^^^ (0 : Word) =
                  gf32Mul (gf32Mul c q3.2) (chunkW (syn (q3.1 + 1) 1) m) :=
                BitVec.xor_zero
              rw [hxz, ← BitVec.xor_assoc, hhead_val] at h
              exact h
            obtain ⟨i, j, k, hijk_mem, hdet⟩ := exists_det3 (q.1 + 1)
              (q2.1 + 1) (q3.1 + 1) (by omega) (by omega) (by omega) (by omega)
            have hb := coordTriples_bounds hijk_mem
            have hcram := cramer3 (syn (q.1 + 1) 1) (syn (q2.1 + 1) 1)
              (syn (q3.1 + 1) 1) 1 (gf32Mul c q2.2) (gf32Mul c q3.2) i j k
              (hcheq i hb.1 hb.2.1) (hcheq j hb.2.2.1 hb.2.2.2.1)
              (hcheq k hb.2.2.2.2.1 hb.2.2.2.2.2)
            rw [gf32One_mul] at hcram
            exact (hdet hcram).elim
          · -- weight = 5
            have hlen18 : es.length ≤ 18 := by
              rcases hcase with h | h | h | h <;> omega
            obtain ⟨q2, Lq2, hq2⟩ : ∃ q2 Lq2, Lq = q2 :: Lq2 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hnil] at hlenLq
                simp only [List.length_nil] at hlenLq
                omega)
            obtain ⟨q3, Lq3, hq3⟩ : ∃ q3 Lq3, Lq2 = q3 :: Lq3 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hq2, hnil] at hlenLq
                simp only [List.length_cons, List.length_nil] at hlenLq
                omega)
            obtain ⟨q4, Lq4, hq4c⟩ : ∃ q4 : Nat × Word,
                ∃ Lq4 : List (Nat × Word), Lq3 = q4 :: Lq4 := by
              apply List.exists_cons_of_ne_nil
              intro hn
              rw [hq2, hq3, hn] at hlenLq
              simp only [List.length_cons, List.length_nil] at hlenLq
              omega
            have hLq4 : Lq4 = [] := List.eq_nil_of_length_eq_zero (by
              rw [hq2, hq3, hq4c] at hlenLq
              simp only [List.length_cons] at hlenLq
              omega)
            have hq4 : Lq3 = [q4] := by rw [hq4c, hLq4]
            have hmem2 : (q2.1 + 1, q2.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2]; simp
            have hmem3 : (q3.1 + 1, q3.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3]; simp
            have hmem4 : (q4.1 + 1, q4.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3, hq4]; simp
            have hd12 : q2.1 + 1 < q.1 + 1 := hhead_rel _ hmem2
            have hd13 : q3.1 + 1 < q.1 + 1 := hhead_rel _ hmem3
            have hd14 : q4.1 + 1 < q.1 + 1 := hhead_rel _ hmem4
            have hpair2 : ((Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++
                [(0, last)]).Pairwise (fun p q : Nat × Word => p.1 > q.1) :=
              hpair_rest
            rw [hq2] at hpair2
            simp only [List.map_cons, List.cons_append] at hpair2
            obtain ⟨hrel2, hpair3⟩ := List.pairwise_cons.mp hpair2
            have hd23 : q3.1 + 1 < q2.1 + 1 := by
              have hmem : (q3.1 + 1, q3.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3]; simp
              exact hrel2 _ hmem
            have hd24 : q4.1 + 1 < q2.1 + 1 := by
              have hmem : (q4.1 + 1, q4.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3, hq4]; simp
              exact hrel2 _ hmem
            have hd34 : q4.1 + 1 < q3.1 + 1 := by
              rw [hq3] at hpair3
              simp only [List.map_cons, List.cons_append] at hpair3
              obtain ⟨hrel3, -⟩ := List.pairwise_cons.mp hpair3
              have hmem : (q4.1 + 1, q4.2) ∈
                  (Lq3.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq4]; simp
              exact hrel3 _ hmem
            have hcheq : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
                gf32Mul 1 (chunkW (syn (q.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q3.2) (chunkW (syn (q3.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q4.2) (chunkW (syn (q4.1 + 1) 1) m) = 0 := by
              intro m hm1 hm2
              have h := hprefix m hm1 hm2
              rw [hprefix_form, hq2, hq3, hq4] at h
              simp only [List.map_cons, List.map_nil, List.foldr_cons,
                List.foldr_nil] at h
              have hxz : gf32Mul (gf32Mul c q4.2) (chunkW (syn (q4.1 + 1) 1) m)
                  ^^^ (0 : Word) =
                  gf32Mul (gf32Mul c q4.2) (chunkW (syn (q4.1 + 1) 1) m) :=
                BitVec.xor_zero
              rw [hxz, ← BitVec.xor_assoc, ← BitVec.xor_assoc, hhead_val] at h
              exact h
            obtain ⟨i, j, k, l, hijkl_mem, hdet⟩ := exists_det4 (q.1 + 1)
              (q2.1 + 1) (q3.1 + 1) (q4.1 + 1) (by omega) (by omega)
              (by omega) (by omega) (by omega)
            have hb := coordQuads_bounds hijkl_mem
            have hcram := cramer4 (syn (q.1 + 1) 1) (syn (q2.1 + 1) 1)
              (syn (q3.1 + 1) 1) (syn (q4.1 + 1) 1) 1 (gf32Mul c q2.2)
              (gf32Mul c q3.2) (gf32Mul c q4.2) i j k l
              (hcheq i hb.1 hb.2.1) (hcheq j hb.2.2.1 hb.2.2.2.1)
              (hcheq k hb.2.2.2.2.1 hb.2.2.2.2.2.1)
              (hcheq l hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2)
            rw [gf32One_mul] at hcram
            exact (hdet hcram).elim
          · -- weight = 6
            have hlen8 : es.length ≤ 8 := by
              rcases hcase with h | h | h | h <;> omega
            obtain ⟨q2, Lq2, hq2⟩ : ∃ q2 Lq2, Lq = q2 :: Lq2 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hnil] at hlenLq
                simp only [List.length_nil] at hlenLq
                omega)
            obtain ⟨q3, Lq3, hq3⟩ : ∃ q3 Lq3, Lq2 = q3 :: Lq3 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hq2, hnil] at hlenLq
                simp only [List.length_cons, List.length_nil] at hlenLq
                omega)
            obtain ⟨q4, Lq4, hq4⟩ : ∃ q4 Lq4, Lq3 = q4 :: Lq4 :=
              List.exists_cons_of_ne_nil (by
                intro hnil
                rw [hq2, hq3, hnil] at hlenLq
                simp only [List.length_cons, List.length_nil] at hlenLq
                omega)
            obtain ⟨q5, Lq5, hq5c⟩ : ∃ q5 : Nat × Word,
                ∃ Lq5 : List (Nat × Word), Lq4 = q5 :: Lq5 := by
              apply List.exists_cons_of_ne_nil
              intro hn
              rw [hq2, hq3, hq4, hn] at hlenLq
              simp only [List.length_cons, List.length_nil] at hlenLq
              omega
            have hLq5 : Lq5 = [] := List.eq_nil_of_length_eq_zero (by
              rw [hq2, hq3, hq4, hq5c] at hlenLq
              simp only [List.length_cons] at hlenLq
              omega)
            have hq5 : Lq4 = [q5] := by rw [hq5c, hLq5]
            have hmem2 : (q2.1 + 1, q2.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2]; simp
            have hmem3 : (q3.1 + 1, q3.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3]; simp
            have hmem4 : (q4.1 + 1, q4.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3, hq4]; simp
            have hmem5 : (q5.1 + 1, q5.2) ∈
                (Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++ [(0, last)] := by
              rw [hq2, hq3, hq4, hq5]; simp
            have hd12 : q2.1 + 1 < q.1 + 1 := hhead_rel _ hmem2
            have hd13 : q3.1 + 1 < q.1 + 1 := hhead_rel _ hmem3
            have hd14 : q4.1 + 1 < q.1 + 1 := hhead_rel _ hmem4
            have hd15 : q5.1 + 1 < q.1 + 1 := hhead_rel _ hmem5
            have hpair2 : ((Lq.map (fun p : Nat × Word => (p.1 + 1, p.2))) ++
                [(0, last)]).Pairwise (fun p q : Nat × Word => p.1 > q.1) :=
              hpair_rest
            rw [hq2] at hpair2
            simp only [List.map_cons, List.cons_append] at hpair2
            obtain ⟨hrel2, hpair3⟩ := List.pairwise_cons.mp hpair2
            have hd23 : q3.1 + 1 < q2.1 + 1 := by
              have hmem : (q3.1 + 1, q3.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3]; simp
              exact hrel2 _ hmem
            have hd24 : q4.1 + 1 < q2.1 + 1 := by
              have hmem : (q4.1 + 1, q4.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3, hq4]; simp
              exact hrel2 _ hmem
            have hd25 : q5.1 + 1 < q2.1 + 1 := by
              have hmem : (q5.1 + 1, q5.2) ∈
                  (Lq2.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq3, hq4, hq5]; simp
              exact hrel2 _ hmem
            rw [hq3] at hpair3
            simp only [List.map_cons, List.cons_append] at hpair3
            obtain ⟨hrel3, hpair4⟩ := List.pairwise_cons.mp hpair3
            have hd34 : q4.1 + 1 < q3.1 + 1 := by
              have hmem : (q4.1 + 1, q4.2) ∈
                  (Lq3.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq4]; simp
              exact hrel3 _ hmem
            have hd35 : q5.1 + 1 < q3.1 + 1 := by
              have hmem : (q5.1 + 1, q5.2) ∈
                  (Lq3.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq4, hq5]; simp
              exact hrel3 _ hmem
            rw [hq4] at hpair4
            simp only [List.map_cons, List.cons_append] at hpair4
            obtain ⟨hrel4, -⟩ := List.pairwise_cons.mp hpair4
            have hd45 : q5.1 + 1 < q4.1 + 1 := by
              have hmem : (q5.1 + 1, q5.2) ∈
                  (Lq4.map (fun p => (p.1 + 1, p.2))) ++ [(0, last)] := by
                rw [hq5]; simp
              exact hrel4 _ hmem
            have hcheq : ∀ m : Nat, 1 ≤ m → m ≤ 5 →
                gf32Mul 1 (chunkW (syn (q.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q2.2) (chunkW (syn (q2.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q3.2) (chunkW (syn (q3.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q4.2) (chunkW (syn (q4.1 + 1) 1) m) ^^^
                  gf32Mul (gf32Mul c q5.2) (chunkW (syn (q5.1 + 1) 1) m) = 0 := by
              intro m hm1 hm2
              have h := hprefix m hm1 hm2
              rw [hprefix_form, hq2, hq3, hq4, hq5] at h
              simp only [List.map_cons, List.map_nil, List.foldr_cons,
                List.foldr_nil] at h
              have hxz : gf32Mul (gf32Mul c q5.2) (chunkW (syn (q5.1 + 1) 1) m)
                  ^^^ (0 : Word) =
                  gf32Mul (gf32Mul c q5.2) (chunkW (syn (q5.1 + 1) 1) m) :=
                BitVec.xor_zero
              rw [hxz, ← BitVec.xor_assoc, ← BitVec.xor_assoc,
                ← BitVec.xor_assoc, hhead_val] at h
              exact h
            have hdet := exists_det5 (q.1 + 1) (q2.1 + 1) (q3.1 + 1)
              (q4.1 + 1) (q5.1 + 1) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega)
            have hcram := cramer5 (syn (q.1 + 1) 1) (syn (q2.1 + 1) 1)
              (syn (q3.1 + 1) 1) (syn (q4.1 + 1) 1) (syn (q5.1 + 1) 1) 1
              (gf32Mul c q2.2) (gf32Mul c q3.2) (gf32Mul c q4.2)
              (gf32Mul c q5.2)
              (hcheq 1 (by decide) (by decide))
              (hcheq 2 (by decide) (by decide))
              (hcheq 3 (by decide) (by decide))
              (hcheq 4 (by decide) (by decide))
              (hcheq 5 (by decide) (by decide))
            rw [gf32One_mul] at hcram
            exact (hdet hcram).elim

/-! ## The distance theorems -/

theorem foldl_polymodStep_zero_ne_zero_of_weight_le_three
    (es : List Word) (hlen : es.length ≤ 173)
    (hne : 0 < hammingWeight es) (hwt : hammingWeight es ≤ 3) :
    es.foldl polymodStep 0 ≠ 0 := by
  intro hfold
  have h := fold_eq_zero_weight es.length es (Nat.le_refl _) hfold
    (Or.inl ⟨hwt, hlen⟩)
  omega

theorem foldl_polymodStep_zero_ne_zero_of_weight_le_four
    (es : List Word) (hlen : es.length ≤ 89)
    (hne : 0 < hammingWeight es) (hwt : hammingWeight es ≤ 4) :
    es.foldl polymodStep 0 ≠ 0 := by
  intro hfold
  have h := fold_eq_zero_weight es.length es (Nat.le_refl _) hfold
    (Or.inr (Or.inl ⟨hwt, hlen⟩))
  omega

theorem foldl_polymodStep_zero_ne_zero_of_weight_le_five
    (es : List Word) (hlen : es.length ≤ 18)
    (hne : 0 < hammingWeight es) (hwt : hammingWeight es ≤ 5) :
    es.foldl polymodStep 0 ≠ 0 := by
  intro hfold
  have h := fold_eq_zero_weight es.length es (Nat.le_refl _) hfold
    (Or.inr (Or.inr (Or.inl ⟨hwt, hlen⟩)))
  omega

theorem foldl_polymodStep_zero_ne_zero_of_weight_le_six
    (es : List Word) (hlen : es.length ≤ 8)
    (hne : 0 < hammingWeight es) (hwt : hammingWeight es ≤ 6) :
    es.foldl polymodStep 0 ≠ 0 := by
  intro hfold
  have h := fold_eq_zero_weight es.length es (Nat.le_refl _) hfold
    (Or.inr (Or.inr (Or.inr ⟨hwt, hlen⟩)))
  omega

/-! ## Sharpness witnesses -/

set_option maxRecDepth 8192 in
/-- Sharpness at length 90: `x^89 + 19x^79 + 15x^14 + 29` is a weight-4
    multiple of the generator. -/
theorem exists_weight_four_kernel_length_90 :
    ∃ es : List Word, es.length = 90 ∧ hammingWeight es = 4 ∧
      es.foldl polymodStep 0 = 0 := by
  refine ⟨(List.range 90).map (fun i =>
    if i = 0 then 1 else if i = 10 then 19 else if i = 75 then 15 else
    if i = 89 then 29 else 0), by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Sharpness at length 19: a weight-5 kernel word. -/
theorem exists_weight_five_kernel_length_19 :
    ∃ es : List Word, es.length = 19 ∧ hammingWeight es = 5 ∧
      es.foldl polymodStep 0 = 0 := by
  refine ⟨(List.range 19).map (fun i =>
    if i = 0 then 1 else if i = 4 then 31 else if i = 12 then 7 else
    if i = 15 then 12 else if i = 18 then 30 else 0),
    by decide, by decide, by decide⟩

set_option maxRecDepth 8192 in
/-- Sharpness at length 9: a weight-6 kernel word. -/
theorem exists_weight_six_kernel_length_9 :
    ∃ es : List Word, es.length = 9 ∧ hammingWeight es = 6 ∧
      es.foldl polymodStep 0 = 0 := by
  refine ⟨(List.range 9).map (fun i =>
    if i = 0 then 1 else if i = 1 then 14 else if i = 3 then 10 else
    if i = 5 then 1 else if i = 6 then 22 else if i = 8 then 21 else 0),
    by decide, by decide, by decide⟩

set_option maxRecDepth 65536 in
/-- At the primitive length, distance drops to 2: `x^1023 + 1`. -/
theorem exists_weight_two_kernel_length_1024 :
    ∃ es : List Word, es.length = 1024 ∧ hammingWeight es = 2 ∧
      es.foldl polymodStep 0 = 0 := by
  refine ⟨(List.range 1024).map (fun i =>
    if i = 0 then 1 else if i = 1023 then 1 else 0),
    by decide, by decide, by decide⟩

/-! ## From distance to `polymod` and `verifyChecksum` -/

theorem hammingDist_eq_hammingWeight_xor (xs ys : List Word)
    (h : xs.length = ys.length) :
    hammingDist xs ys = hammingWeight (List.zipWith (· ^^^ ·) xs ys) := by
  show ((xs.zip ys).filter (fun p => p.1 ≠ p.2)).length =
    ((List.zipWith (· ^^^ ·) xs ys).filter (· ≠ 0)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [List.zip_cons_cons, List.zipWith_cons_cons, List.countP_cons,
        List.countP_cons, ih ys h]
      by_cases hxy : x = y
      · subst hxy
        have e1 : decide ((x, x).1 ≠ (x, x).2) = false := by
          show decide (x ≠ x) = false
          exact decide_eq_false_iff_not.mpr (by simp)
        have e2 : decide (x ^^^ x ≠ 0) = false := by
          rw [show x ^^^ x = (0 : Word) from BitVec.xor_self]
          exact decide_eq_false_iff_not.mpr (by simp)
        rw [e1, e2]
      · have e1 : decide ((x, y).1 ≠ (x, y).2) = true := by
          show decide (x ≠ y) = true
          exact decide_eq_true_eq.mpr hxy
        have e2 : decide (x ^^^ y ≠ 0) = true :=
          decide_eq_true_eq.mpr (fun hz => hxy (xor_eq_zero_imp hz))
        rw [e1, e2]

theorem hammingDist_eq_zero_imp {xs ys : List Word}
    (h : hammingDist xs ys = 0) (hlen : xs.length = ys.length) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hxy : x = y := by
        by_cases hxy : x = y
        · exact hxy
        · have hge : 1 ≤ hammingDist (x :: xs) (y :: ys) := by
            simp [hammingDist, hxy]
          omega
      subst hxy
      congr 1
      apply ih _ hlen
      have h2 : hammingDist (x :: xs) (x :: ys) =
          hammingDist xs ys := by
        simp [hammingDist, List.zip_cons_cons]
      omega

theorem polymod_ne_of_hammingDist_le_four
    (pfx xs ys : List Word) (hlen : xs.length = ys.length)
    (hbound : xs.length ≤ 89) (hne : xs ≠ ys)
    (hdist : hammingDist xs ys ≤ 4) :
    polymod (pfx ++ xs) ≠ polymod (pfx ++ ys) := by
  intro heq
  have h1 : xs.foldl polymodStep (pfx.foldl polymodStep 1) =
      ys.foldl polymodStep (pfx.foldl polymodStep 1) := by
    have h := heq
    simp only [polymod, List.foldl_append] at h
    exact h
  have h2 : (List.zipWith (· ^^^ ·) xs ys).foldl polymodStep 0 = 0 := by
    have hx := foldl_polymodStep_xor xs ys (pfx.foldl polymodStep 1)
      (pfx.foldl polymodStep 1) hlen
    rw [BitVec.xor_self, h1, BitVec.xor_self] at hx
    exact hx
  have hw : hammingWeight (List.zipWith (· ^^^ ·) xs ys) =
      hammingDist xs ys := (hammingDist_eq_hammingWeight_xor xs ys hlen).symm
  have hpos : 0 < hammingWeight (List.zipWith (· ^^^ ·) xs ys) := by
    rw [hw]
    by_cases hz : hammingDist xs ys = 0
    · exact absurd (hammingDist_eq_zero_imp hz hlen) hne
    · omega
  have hlen2 : (List.zipWith (· ^^^ ·) xs ys).length ≤ 89 := by
    rw [List.length_zipWith]
    omega
  exact foldl_polymodStep_zero_ne_zero_of_weight_le_four _
    hlen2 hpos (by rw [hw]; exact hdist) h2

theorem verifyChecksum_false_of_data_substitutions_le_four
    (variant : Variant) (hrp : List Char) (data₁ data₂ : List Word)
    (hlen : data₁.length = data₂.length) (hbound : data₁.length ≤ 89)
    (hne : data₁ ≠ data₂) (hdist : hammingDist data₁ data₂ ≤ 4)
    (hvalid : verifyChecksum variant hrp data₁ = true) :
    verifyChecksum variant hrp data₂ = false := by
  by_cases hcon : verifyChecksum variant hrp data₂ = false
  · exact hcon
  · exfalso
    have h2 : verifyChecksum variant hrp data₂ = true := by
      cases h : verifyChecksum variant hrp data₂ with
      | false => exact absurd h hcon
      | true => rfl
    have heq : polymod (hrpExpand hrp ++ data₁) =
        polymod (hrpExpand hrp ++ data₂) := by
      simp only [verifyChecksum, beq_iff_eq] at hvalid h2
      rw [hvalid, h2]
    exact polymod_ne_of_hammingDist_le_four (hrpExpand hrp) data₁ data₂ hlen
      hbound hne hdist heq

/-- The high halves of `hrpExpand` are equal when the character high bits
    are. -/
theorem hrpExpand_hi_eq (hrp₁ hrp₂ : List Char)
    (hhrp_len : hrp₁.length = hrp₂.length)
    (hhi : hrp₁.map (fun c => c.toNat >>> 5) =
      hrp₂.map (fun c => c.toNat >>> 5)) :
    hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) =
      hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) := by
  induction hrp₁ generalizing hrp₂ with
  | nil =>
    cases hrp₂ with
    | nil => rfl
    | cons c cs => simp at hhrp_len
  | cons c₁ cs₁ ih =>
    cases hrp₂ with
    | nil => simp at hhrp_len
    | cons c₂ cs₂ =>
      have hlen' : cs₁.length = cs₂.length := by simpa using hhrp_len
      simp only [List.map_cons, List.cons.injEq] at hhi
      obtain ⟨h1, h2⟩ := hhi
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨congrArg (BitVec.ofNat 5) h1, ih _ hlen' h2⟩

/-- Appending equal-length prefixes is injective in both components. -/
theorem append_inj_of_len {a b c d : List Word} (hlen : a.length = b.length)
    (h : a ++ c = b ++ d) : a = b ∧ c = d := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, h⟩
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxy, hr⟩ := h
      obtain ⟨h1, h2⟩ := ih hlen hr
      exact ⟨by rw [hxy, h1], h2⟩

/-- On the ASCII domain, an HRP is determined by its high bits and its low
    bits. -/
theorem char_list_eq_of_hi_lo (hrp₁ hrp₂ : List Char)
    (hlen : hrp₁.length = hrp₂.length)
    (hhi : hrp₁.map (fun c => c.toNat >>> 5) =
      hrp₂.map (fun c => c.toNat >>> 5))
    (hlo : hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) =
      hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)))
    (ha₁ : ∀ c ∈ hrp₁, c.toNat ≤ 126) (ha₂ : ∀ c ∈ hrp₂, c.toNat ≤ 126) :
    hrp₁ = hrp₂ := by
  induction hrp₁ generalizing hrp₂ with
  | nil =>
    cases hrp₂ with
    | nil => rfl
    | cons c cs => simp at hlen
  | cons c₁ cs₁ ih =>
    cases hrp₂ with
    | nil => simp at hlen
    | cons c₂ cs₂ =>
      have hlen' : cs₁.length = cs₂.length := by simpa using hlen
      simp only [List.map_cons, List.cons.injEq] at hhi hlo
      obtain ⟨hhi1, hhi2⟩ := hhi
      obtain ⟨hlo1, hlo2⟩ := hlo
      have hc : c₁ = c₂ := by
        have ha1 := ha₁ c₁ (List.mem_cons_self)
        have ha2 := ha₂ c₂ (List.mem_cons_self)
        have hmod : c₁.toNat &&& 31 = c₂.toNat &&& 31 := by
          have h5 := congrArg BitVec.toNat hlo1
          simp only [BitVec.toNat_ofNat] at h5
          have hb1 : c₁.toNat &&& 31 < 32 :=
            Nat.lt_succ_of_le Nat.and_le_right
          have hb2 : c₂.toNat &&& 31 < 32 :=
            Nat.lt_succ_of_le Nat.and_le_right
          omega
        have hnat : c₁.toNat = c₂.toNat := by
          have hb1' : c₁.toNat &&& 31 = c₁.toNat % 32 :=
            Nat.and_two_pow_sub_one_eq_mod c₁.toNat 5
          have hb2' : c₂.toNat &&& 31 = c₂.toNat % 32 :=
            Nat.and_two_pow_sub_one_eq_mod c₂.toNat 5
          omega
        exact Char.toNat_inj.mp hnat
      simp only [List.cons.injEq]
      exact ⟨hc, ih _ hlen' hhi2 hlo2
        (fun c hc => ha₁ c (List.mem_cons_of_mem c₁ hc))
        (fun c hc => ha₂ c (List.mem_cons_of_mem c₂ hc))⟩

/-- The joint HRP+data guarantee: with the HRP length fixed, the high bits
    preserved, and at most four substitutions split across HRP and data, a
    valid string cannot verify under a different `(hrp, data)` pair. -/
theorem verifyChecksum_false_of_substitutions_le_four
    (variant : Variant) (hrp₁ hrp₂ : List Char) (data₁ data₂ : List Word)
    (hhrp_len : hrp₁.length = hrp₂.length)
    (hdata_len : data₁.length = data₂.length)
    (hbound : hrp₁.length + data₁.length ≤ 89)
    (hascii₁ : ∀ c ∈ hrp₁, c.toNat ≤ 126)
    (hascii₂ : ∀ c ∈ hrp₂, c.toNat ≤ 126)
    (hhi : hrp₁.map (fun c => c.toNat >>> 5) =
      hrp₂.map (fun c => c.toNat >>> 5))
    (hne : hrp₁ ≠ hrp₂ ∨ data₁ ≠ data₂)
    (hdist : hammingDist hrp₁ hrp₂ + hammingDist data₁ data₂ ≤ 4)
    (hvalid : verifyChecksum variant hrp₁ data₁ = true) :
    verifyChecksum variant hrp₂ data₂ = false := by
  by_cases hcon : verifyChecksum variant hrp₂ data₂ = false
  · exact hcon
  · exfalso
    have h2 : verifyChecksum variant hrp₂ data₂ = true := by
      cases h : verifyChecksum variant hrp₂ data₂ with
      | false => exact absurd h hcon
      | true => rfl
    have heq : polymod (hrpExpand hrp₁ ++ data₁) =
        polymod (hrpExpand hrp₂ ++ data₂) := by
      simp only [verifyChecksum, beq_iff_eq] at hvalid h2
      rw [hvalid, h2]
    have hhiW : hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) =
        hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) :=
      hrpExpand_hi_eq hrp₁ hrp₂ hhrp_len hhi
    have hexp1 : hrpExpand hrp₁ ++ data₁ =
        (hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0]) ++
          (hrp₁.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₁) := by
      simp [hrpExpand, List.append_assoc]
    have hexp2 : hrpExpand hrp₂ ++ data₂ =
        (hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat >>> 5)) ++ [0]) ++
          (hrp₂.map (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) ++ data₂) := by
      simp [hrpExpand, List.append_assoc]
    rw [hexp1, hexp2, hhiW] at heq
    refine polymod_ne_of_hammingDist_le_four _ _ _ ?_ ?_ ?_ ?_ heq
    · simp only [List.length_append, List.length_map, hhrp_len, hdata_len]
    · simp only [List.length_append, List.length_map]
      omega
    · intro hEq
      obtain ⟨hlo, hdata⟩ := append_inj_of_len (by simp [hhrp_len]) hEq
      have hhrp_eq : hrp₁ = hrp₂ :=
        char_list_eq_of_hi_lo hrp₁ hrp₂ hhrp_len hhi hlo hascii₁ hascii₂
      cases hne with
      | inl h => exact h hhrp_eq
      | inr h => exact h hdata
    · rw [hammingDist_append _ _ _ _ (by simp [List.length_map, hhrp_len])]
      have hle := hammingDist_map_le
        (fun c => BitVec.ofNat 5 (c.toNat &&& 31)) hrp₁ hrp₂
      omega

end Bech32
