module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Prod

public section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace RudinRCA.Chapter08

/-- Covering-lemma part of the concrete maximal weak estimate. This is support only:
to apply it to an entire maximal-function level set, uniformly bound witness radii. -/
theorem weak_bound_of_bounded_ball_witnesses {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {s : Set X} {t C : ℝ≥0∞} {R : ℝ}
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r))
    (hwitness : ∀ x ∈ s, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ) :
    t * μ s ≤ C * ∫⁻ x, f x ∂μ := by
  classical
  choose r hrpos hrbound hrint using fun x : s => hwitness x x.property
  obtain ⟨u, hu, hdis, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (univ : Set s) (fun x : s => (x : X)) r R (fun x _ => hrbound x) 5 (by norm_num)
  have huc : u.Countable := hdis.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun x _ => nonempty_ball.mpr (hrpos x))
  letI : Countable u := huc.to_subtype
  have hscover : s ⊆ ⋃ i : u, ball ((i : s) : X) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hinc⟩ := hcover ⟨x, hx⟩ (mem_univ _)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hinc (mem_ball_self (hrpos ⟨x, hx⟩))⟩
  have hmeasure : μ s ≤ C * ∑' i : u, μ (ball ((i : s) : X) (r i)) := by
    calc
      μ s ≤ μ (⋃ i : u, ball ((i : s) : X) (5 * r i)) := measure_mono hscover
      _ ≤ ∑' i : u, μ (ball ((i : s) : X) (5 * r i)) := measure_iUnion_le _
      _ ≤ ∑' i : u, C * μ (ball ((i : s) : X) (r i)) :=
        ENNReal.tsum_le_tsum fun i => hgrowth i (r i) (hrpos i)
      _ = _ := ENNReal.tsum_mul_left
  have hiunion : (∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ) ≤
      ∫⁻ x, f x ∂μ := by
    rw [← lintegral_iUnion (fun _ => measurableSet_ball) (hdis.subtype _ _)]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    t * μ s ≤ t * (C * ∑' i : u, μ (ball ((i : s) : X) (r i))) :=
      mul_le_mul_right hmeasure t
    _ = C * ∑' i : u, t * μ (ball ((i : s) : X) (r i)) := by
      rw [ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ C * ∑' i : u, ∫⁻ x in ball ((i : s) : X) (r i), f x ∂μ :=
      mul_le_mul_right (ENNReal.tsum_le_tsum fun i : u => hrint (i : s)) C
    _ ≤ C * ∫⁻ x, f x ∂μ := mul_le_mul_right hiunion C

/-- The Euclidean ball-growth constant required in the weak estimate. -/
theorem haar_ball_five_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (ball x (5 * r)) = ENNReal.ofReal (5 ^ Module.finrank ℝ E) * μ (ball x r) := by
  rw [μ.addHaar_ball_mul_of_pos x (by norm_num : (0 : ℝ) < 5) r,
    μ.addHaar_ball_center x r]

/-- Centered maximal operator for nonnegative extended-valued functions. -/
noncomputable def centeredMaximal {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ r : ℝ, ⨆ (_ : 0 < r), (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r)

/-- The weak estimate follows by exhausting bounded-radius witnesses. The measure
continuity theorem used here works for arbitrary level sets, before measurability is known. -/
theorem centeredMaximal_weak_bound {X : Type*} [PseudoMetricSpace X]
    [SeparableSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) {t C : ℝ≥0∞}
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (hgrowth : ∀ (x : X) (r : ℝ), 0 < r →
      μ (ball x (5 * r)) ≤ C * μ (ball x r)) :
    t * μ {x | t < centeredMaximal μ f x} ≤ C * ∫⁻ x, f x ∂μ := by
  let S : ℕ → Set X := fun n => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (n : ℝ) ∧
    t * μ (ball x r) ≤ ∫⁻ y in ball x r, f y ∂μ}
  have hSmono : Monotone S := by
    intro m n hmn x hx
    obtain ⟨r, hrpos, hrbound, hrint⟩ := hx
    exact ⟨r, hrpos, hrbound.trans (by exact_mod_cast hmn), hrint⟩
  have hSbound (n : ℕ) : t * μ (S n) ≤ C * ∫⁻ x, f x ∂μ :=
    weak_bound_of_bounded_ball_witnesses μ f hgrowth (fun _ hx => hx)
  have hcover : {x | t < centeredMaximal μ f x} ⊆ ⋃ n : ℕ, S n := by
    intro x hx
    change t < centeredMaximal μ f x at hx
    unfold centeredMaximal at hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.mp hx
    obtain ⟨hrpos, hrmean⟩ := lt_iSup_iff.mp hr
    obtain ⟨n, hn⟩ := exists_nat_ge r
    refine mem_iUnion.mpr ⟨n, r, hrpos, hn, ?_⟩
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl (hballs x r hrpos).1)
      (Or.inl (hballs x r hrpos).2)).mp hrmean).le
  calc
    t * μ {x | t < centeredMaximal μ f x} ≤ t * μ (⋃ n : ℕ, S n) :=
      mul_le_mul_right (measure_mono hcover) t
    _ = ⨆ n : ℕ, t * μ (S n) := by rw [hSmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ C * ∫⁻ x, f x ∂μ := iSup_le hSbound

/-- Concrete weak (1,1) bound for the centered maximal operator on a finite-dimensional
real normed space, with explicit dimension-dependent constant 5^dim. -/
theorem centeredMaximal_weak_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    t * μ {x | t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, f x ∂μ := by
  apply centeredMaximal_weak_bound μ f
  · intro x r hr
    exact ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩
  · intro x r hr
    exact (haar_ball_five_growth μ x r).le

/-- All radii can be replaced by positive rational radii, because open balls are
unions of smaller rational-radius balls. -/
theorem centeredMaximal_eq_rational {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞) (x : X)
    (hballs : ∀ r : ℝ, 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞) :
    centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ)) := by
  let S := ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
    (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball x (q : ℝ))
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply ENNReal.div_le_of_le_mul
    let Q := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < r}
    have hu : ball x r = ⋃ q : Q, ball x ((q : ℚ) : ℝ) := by
      ext y
      constructor
      · intro hy
        change dist y x < r at hy
        obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hy
        exact mem_iUnion.mpr ⟨⟨q, lt_of_le_of_lt dist_nonneg hq₁, hq₂⟩, hq₁⟩
      · intro hy
        obtain ⟨q, hq⟩ := mem_iUnion.mp hy
        exact hq.trans q.property.2
    have hd : Directed (· ⊆ ·) (fun q : Q => ball x ((q : ℚ) : ℝ)) := by
      intro a b
      rcases le_total (a : ℚ) (b : ℚ) with hab | hba
      · exact ⟨b, ball_subset_ball (by exact_mod_cast hab), Subset.rfl⟩
      · exact ⟨a, Subset.rfl, ball_subset_ball (by exact_mod_cast hba)⟩
    have hi : (∫⁻ y in ball x r, f y ∂μ) =
        ⨆ q : Q, ∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ := by
      rw [hu, setLIntegral_iUnion_of_directed f hd]
    rw [hi]
    apply iSup_le
    intro q
    calc
      (∫⁻ y in ball x ((q : ℚ) : ℝ), f y ∂μ) ≤
          S * μ (ball x ((q : ℚ) : ℝ)) := by
        apply (ENNReal.div_le_iff_le_mul (Or.inl (hballs _ q.property.1).1)
          (Or.inl (hballs _ q.property.1).2)).mp
        exact le_iSup_of_le (q : ℚ) (le_iSup_of_le q.property.1 le_rfl)
      _ ≤ S * μ (ball x r) :=
        mul_le_mul_right (measure_mono (ball_subset_ball q.property.2.le)) S
  · apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_iSup_of_le (q : ℝ) (le_iSup_of_le hq le_rfl)

/-- Measurability of the mass of a ball with moving center. -/
theorem measurable_lintegral_ball {X : Type*} [PseudoMetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [SFinite μ] {f : X → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    Measurable (fun x => ∫⁻ y in ball x r, f y ∂μ) := by
  let F : X × X → ℝ≥0∞ :=
    {p : X × X | dist p.2 p.1 < r}.indicator (fun p => f p.2)
  have hF : Measurable F := (hf.comp measurable_snd).indicator
    (measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const)
  have hmeas : Measurable (fun x => ∫⁻ y, F (x, y) ∂μ) := hF.lintegral_prod_right'
  have he : (fun x => ∫⁻ y in ball x r, f y ∂μ) = (fun x => ∫⁻ y, F (x, y) ∂μ) := by
    funext x
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  rw [he]
  exact hmeas

/-- The centered maximal function is measurable for a measurable nonnegative input. -/
theorem centeredMaximal_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f) :
    Measurable (centeredMaximal μ f) := by
  have he (x : E) : centeredMaximal μ f x =
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ)) := by
    rw [centeredMaximal_eq_rational μ f x
      (fun r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩)]
    simp_rw [μ.addHaar_ball_center x]
  have hefun : centeredMaximal μ f = (fun x =>
      ⨆ q : ℚ, ⨆ (_ : 0 < (q : ℝ)),
        (∫⁻ y in ball x (q : ℝ), f y ∂μ) / μ (ball 0 (q : ℝ))) := funext he
  rw [hefun]
  exact Measurable.iSup fun q => Measurable.iSup fun _ =>
    (measurable_lintegral_ball μ hf (q : ℝ)).div measurable_const

/-- Adding a pointwise constant bound adds at most that constant to the maximal average. -/
theorem centeredMaximal_le_add_const {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ x, f x ≤ g x + c)
    (hballs : ∀ (x : X) (r : ℝ), 0 < r → μ (ball x r) ≠ 0 ∧ μ (ball x r) ≠ ∞)
    (x : X) : centeredMaximal μ f x ≤ centeredMaximal μ g x + c := by
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  calc
    (∫⁻ y in ball x r, f y ∂μ) / μ (ball x r) ≤
        (∫⁻ y in ball x r, g y + c ∂μ) / μ (ball x r) :=
      ENNReal.div_le_div_right (lintegral_mono h) _
    _ = (∫⁻ y in ball x r, g y ∂μ) / μ (ball x r) + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const,
        Measure.restrict_apply_univ, ENNReal.add_div,
        ENNReal.mul_div_cancel_right (hballs x r hr).1 (hballs x r hr).2]
    _ ≤ centeredMaximal μ g x + c :=
      add_le_add (le_iSup_of_le r (le_iSup_of_le hr le_rfl)) le_rfl

/-- The truncation-distribution inequality at c=1/2, the main intermediate estimate
in Rudin's proof of 8.18. It is concrete, with no assumed weak-type hypothesis. -/
theorem centeredMaximal_truncation_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t / 2) * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
      ENNReal.ofReal (5 ^ Module.finrank ℝ E) *
        ∫⁻ x in {x | ENNReal.ofReal (t / 2) < f x}, f x ∂μ := by
  let q := ENNReal.ofReal (t / 2)
  let g := {x | q < f x}.indicator f
  have hqsum : q + q = ENNReal.ofReal t := by
    change ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)]
    congr 1
    ring
  have hfg (x : E) : f x ≤ g x + q := by
    by_cases hx : q < f x
    · simp only [g, mem_setOf_eq, hx, indicator_of_mem]
      exact le_add_right le_rfl
    · simp only [g, mem_setOf_eq, hx, not_false_eq_true, indicator_of_notMem, zero_add]
      exact le_of_not_gt hx
  have hM (x : E) : centeredMaximal μ f x ≤ centeredMaximal μ g x + q :=
    centeredMaximal_le_add_const μ hfg
      (fun x r hr => ⟨(measure_ball_pos μ x hr).ne', measure_ball_ne_top⟩) x
  have hs : {x | ENNReal.ofReal t < centeredMaximal μ f x} ⊆
      {x | q < centeredMaximal μ g x} := by
    intro x hx
    by_contra hnot
    have hle := (hM x).trans (add_le_add (le_of_not_gt hnot) le_rfl)
    rw [hqsum] at hle
    exact (not_le_of_gt hx) hle
  calc
    q * μ {x | ENNReal.ofReal t < centeredMaximal μ f x} ≤
        q * μ {x | q < centeredMaximal μ g x} := mul_le_mul_right (measure_mono hs) q
    _ ≤ ENNReal.ofReal (5 ^ Module.finrank ℝ E) * ∫⁻ x, g x ∂μ :=
      centeredMaximal_weak_one μ g q
    _ = _ := by rw [lintegral_indicator (measurableSet_lt measurable_const hf)]

end RudinRCA.Chapter08
