import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Algebra.Algebra.NonUnitalHom

/-! Faithful supporting fragment for Rudin RCA, printed third edition, 18.12–18.17.
General homomorphisms are not assumed to preserve the unit; characters are initially
nonzero multiplicative linear maps, without a continuity hypothesis. -/

noncomputable section

open Set
open scoped Topology

namespace RudinRCA.Chapter18

section AlgebraicIdeals

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- 18.12: the book's homomorphisms preserve addition, scalar multiplication and
multiplication, and may be zero. -/
abbrev RudinHom (A B : Type*) [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] := A →ₙₐ[ℂ] B

/-- 18.12: ideals are also complex linear subspaces. -/
def definition18_12_idealSubspace (I : Ideal A) : Submodule ℂ A :=
  I.restrictScalars ℂ

/-- 18.12: no proper ideal contains an invertible element. -/
theorem definition18_12_no_unit_in_proper_ideal (I : Ideal A) (hI : I ≠ ⊤)
    {x : A} (hx : x ∈ I) : ¬IsUnit x :=
  fun hu => hI (I.eq_top_of_isUnit_mem hx hu)

/-- 18.12: the kernel of a homomorphism, including a zero homomorphism, is an ideal. -/
def definition18_12_kernel (φ : RudinHom A B) : Ideal A where
  carrier := {x | φ x = 0}
  zero_mem' := map_zero φ
  add_mem' := by
    intro x y hx hy
    change φ (x + y) = 0
    simp [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    change φ (a * x) = 0
    simp [map_mul, hx]

@[simp] theorem definition18_12_mem_kernel (φ : RudinHom A B) (x : A) :
    x ∈ definition18_12_kernel φ ↔ φ x = 0 := Iff.rfl

/-- 18.13, algebraic part. -/
theorem theorem18_13_maximal_containment (I : Ideal A) (hI : I ≠ ⊤) :
    ∃ M : Ideal A, M.IsMaximal ∧ I ≤ M :=
  I.exists_le_maximal hI

/-- 18.14: the quotient projection is a surjective algebra homomorphism. -/
theorem theorem18_14_quotient_surjective (I : Ideal A) :
    Function.Surjective (Ideal.Quotient.mkₐ ℂ I) :=
  Ideal.Quotient.mkₐ_surjective ℂ I

/-- 18.14: multiplication and the unit descend to the quotient. -/
theorem theorem18_14_quotient_operations (I : Ideal A) (x y : A) :
    Ideal.Quotient.mkₐ ℂ I (x * y) =
      Ideal.Quotient.mkₐ ℂ I x * Ideal.Quotient.mkₐ ℂ I y ∧
    Ideal.Quotient.mkₐ ℂ I 1 = 1 :=
  ⟨map_mul _ _ _, map_one _⟩

/-- 18.14: every ideal is the kernel of its quotient homomorphism. -/
theorem theorem18_14_quotient_kernel (I : Ideal A) :
    RingHom.ker (Ideal.Quotient.mkₐ ℂ I : A →+* A ⧸ I) = I :=
  Ideal.Quotient.mkₐ_ker ℂ I

/-- 18.14: the quotient is a field exactly when the ideal is maximal. -/
theorem theorem18_14_quotient_isField_iff (I : Ideal A) :
    IsField (A ⧸ I) ↔ I.IsMaximal :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).symm

end AlgebraicIdeals

section VectorSpaceQuotient

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- 18.14: the coset `x + J`, as a subset of the original vector space. -/
def definition18_14_coset (J : Submodule ℂ E) (x : E) : Set E :=
  (fun y => x + y) '' (J : Set E)

theorem theorem18_14_mem_coset (J : Submodule ℂ E) (x z : E) :
    z ∈ definition18_14_coset J x ↔ z - x ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨z - x, hz, by abel⟩

/-- 18.14: equal cosets correspond exactly to a difference in the subspace. -/
theorem theorem18_14_coset_eq_iff (J : Submodule ℂ E) (x y : E) :
    definition18_14_coset J x = definition18_14_coset J y ↔ x - y ∈ J := by
  constructor
  · intro h
    have hx : x ∈ definition18_14_coset J x := ⟨0, J.zero_mem, add_zero x⟩
    rw [h, theorem18_14_mem_coset] at hx
    exact hx
  · intro h
    ext z
    rw [theorem18_14_mem_coset, theorem18_14_mem_coset]
    constructor
    · intro hz
      convert J.add_mem hz h using 1 <;> abel
    · intro hz
      convert J.sub_mem hz h using 1 <;> abel

/-- 18.14: distinct cosets are disjoint. -/
theorem theorem18_14_cosets_disjoint (J : Submodule ℂ E) {x y : E}
    (h : x - y ∉ J) :
    Disjoint (definition18_14_coset J x) (definition18_14_coset J y) := by
  rw [Set.disjoint_left]
  intro z hx hy
  rw [theorem18_14_mem_coset] at hx hy
  apply h
  convert J.sub_mem hy hx using 1 <;> abel

/-- 18.14: the quotient map identifies exactly equal cosets. -/
theorem theorem18_14_quotient_eq_iff (J : Submodule ℂ E) (x y : E) :
    J.mkQ x = J.mkQ y ↔ x - y ∈ J :=
  Submodule.Quotient.eq J

/-- 18.14: the canonical quotient map is linear and surjective. -/
theorem theorem18_14_linear_quotient_surjective (J : Submodule ℂ E) :
    Function.Surjective J.mkQ := J.mkQ_surjective

theorem theorem18_14_linear_quotient_operations (J : Submodule ℂ E)
    (x y : E) (c : ℂ) :
    J.mkQ (x + y) = J.mkQ x + J.mkQ y ∧
    J.mkQ (c • x) = c • J.mkQ x ∧ J.mkQ 0 = 0 :=
  ⟨map_add _ _ _, map_smul _ _ _, map_zero _⟩

theorem theorem18_14_linear_quotient_kernel (J : Submodule ℂ E) :
    LinearMap.ker J.mkQ = J := J.ker_mkQ

end VectorSpaceQuotient

section QuotientNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- 18.15: the quotient norm is the infimum of the norms in the coset. -/
theorem theorem18_15_quotient_norm_inf (J : Submodule ℂ E) (x : E) :
    ‖J.mkQ x‖ = sInf ((fun y => ‖x + y‖) '' (J : Set E)) :=
  quotient_norm_mk_eq J.toAddSubgroup x

/-- 18.15: the same quotient norm is the distance to the subspace. -/
theorem theorem18_15_quotient_norm_distance (J : Submodule ℂ E) (x : E) :
    ‖J.mkQ x‖ = Metric.infDist x (J : Set E) :=
  QuotientAddGroup.norm_mk x

/-- 18.15(a): a quotient by a closed subspace is a normed vector space. -/
def definition18_15_quotientNormedGroup (J : Submodule ℂ E) [IsClosed (J : Set E)] :
    NormedAddCommGroup (E ⧸ J) := inferInstance

def definition18_15_quotientNormedSpace (J : Submodule ℂ E) :
    NormedSpace ℂ (E ⧸ J) := inferInstance

/-- 18.15(b): a quotient of a Banach space by a closed subspace is complete. -/
theorem theorem18_15_quotient_complete (J : Submodule ℂ E) [CompleteSpace E] :
    CompleteSpace (E ⧸ J) := inferInstance

end QuotientNorm

section BanachAlgebraQuotient

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- 18.13, topological part: maximal ideals are closed. -/
theorem theorem18_13_maximal_closed (I : Ideal A) (hI : I.IsMaximal) :
    IsClosed (I : Set A) := by
  letI := hI
  infer_instance

/-- 18.15(c): the quotient by a closed ideal is a normed commutative algebra. -/
def definition18_15_quotientNormedRing (I : Ideal A) [IsClosed (I : Set A)] :
    NormedCommRing (A ⧸ I) := inferInstance

def definition18_15_quotientNormedAlgebra (I : Ideal A) :
    NormedAlgebra ℂ (A ⧸ I) := inferInstance

theorem theorem18_15_ideal_quotient_complete (I : Ideal A) :
    CompleteSpace (A ⧸ I) := inferInstance

theorem theorem18_15_quotient_norm_mul (I : Ideal A) (x y : A ⧸ I) :
    ‖x * y‖ ≤ ‖x‖ * ‖y‖ := norm_mul_le x y

/-- 18.15(c): the unit has norm one in the quotient by a proper closed ideal. -/
theorem theorem18_15_quotient_norm_one [NormOneClass A] (I : Ideal A)
    [IsClosed (I : Set A)] (hI : I ≠ ⊤) : ‖(1 : A ⧸ I)‖ = 1 := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply le_antisymm
  · simpa using Ideal.Quotient.norm_mk_le I (1 : A)
  · exact one_le_norm_one (A ⧸ I)

end BanachAlgebraQuotient

section Characters

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- 18.16: a character is a nonzero multiplicative complex linear functional.
Continuity and preservation of 1 are conclusions below, not assumptions. -/
def RudinCharacter (A : Type*) [CommRing A] [Algebra ℂ A] :=
  {h : RudinHom A ℂ // h ≠ 0}

/-- Every nonzero multiplicative linear functional preserves the unit. -/
theorem definition18_16_character_map_one (h : RudinCharacter A) : h.val 1 = 1 := by
  have hn : ∃ a : A, h.val a ≠ 0 := by
    by_contra! hn
    apply h.property
    ext a
    exact hn a
  obtain ⟨a, ha⟩ := hn
  apply mul_right_cancel₀ ha
  rw [← map_mul, one_mul, one_mul]

/-- The book's initially nonunital character determines a unital algebra homomorphism. -/
def definition18_16_characterAlgHom (h : RudinCharacter A) : A →ₐ[ℂ] ℂ where
  toFun := h.val
  map_zero' := map_zero h.val
  map_add' := map_add h.val
  map_one' := definition18_16_character_map_one h
  map_mul' := map_mul h.val
  commutes' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, definition18_16_character_map_one]
    simp

/-- Conversely, a unital algebra homomorphism to ℂ is a character in Rudin's sense. -/
def definition18_16_algHomCharacter (h : A →ₐ[ℂ] ℂ) : RudinCharacter A :=
  ⟨h.toNonUnitalAlgHom, by
    intro hz
    have hh := DFunLike.congr_fun hz 1
    simpa using hh⟩

/-- 18.16: the equivalent description as homomorphisms onto ℂ. -/
theorem definition18_16_character_surjective (h : RudinCharacter A) :
    Function.Surjective h.val := by
  intro c
  exact ⟨algebraMap ℂ A c, (definition18_16_characterAlgHom h).commutes c⟩

/-- 18.16: a multiplicative linear functional is nonzero exactly when it is onto. -/
theorem definition18_16_nonzero_iff_surjective (h : RudinHom A ℂ) :
    h ≠ 0 ↔ Function.Surjective h := by
  constructor
  · intro hn
    exact definition18_16_character_surjective ⟨h, hn⟩
  · intro hs hz
    obtain ⟨a, ha⟩ := hs 1
    have hzero := DFunLike.congr_fun hz a
    simp [ha] at hzero

end Characters

section BanachCharacters

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- 18.17(a): every maximal ideal is the kernel of a character. -/
theorem theorem18_17_a (I : Ideal A) (hI : I.IsMaximal) :
    ∃ h : RudinCharacter A, definition18_12_kernel h.val = I := by
  letI := hI
  let h : A →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.toAlgHom I.toCharacterSpace
  refine ⟨definition18_16_algHomCharacter h, ?_⟩
  have hle : I ≤ RingHom.ker h := by
    intro a ha
    exact I.toCharacterSpace_apply_eq_zero_of_mem ha
  have heq : I = RingHom.ker h := hI.eq_of_le (RingHom.ker_ne_top h) hle
  exact heq.symm

/-- 18.17(b): the spectrum consists exactly of character values. -/
theorem theorem18_17_b (a : A) (z : ℂ) :
    z ∈ spectrum ℂ a ↔ ∃ h : RudinCharacter A, h.val a = z := by
  constructor
  · intro hz
    obtain ⟨h, hh⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
    exact ⟨definition18_16_algHomCharacter h.toAlgHom, hh⟩
  · rintro ⟨h, rfl⟩
    exact AlgHom.apply_mem_spectrum (definition18_16_characterAlgHom h) a

/-- 18.17(c): invertibility is equivalent to nonvanishing under every character. -/
theorem theorem18_17_c (a : A) :
    IsUnit a ↔ ∀ h : RudinCharacter A, h.val a ≠ 0 := by
  constructor
  · intro ha h hz
    have hu := ha.map (definition18_16_characterAlgHom h).toMonoidHom
    exact not_isUnit_zero (hz ▸ hu)
  · intro h
    by_contra ha
    obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero ha
    exact h (definition18_16_algHomCharacter φ.toAlgHom) hφ

/-- 18.17(d): each character value belongs to the spectrum. -/
theorem theorem18_17_d (h : RudinCharacter A) (a : A) :
    h.val a ∈ spectrum ℂ a :=
  AlgHom.apply_mem_spectrum (definition18_16_characterAlgHom h) a

/-- 18.17(e): character values are bounded by spectral radius, which is bounded by norm. -/
theorem theorem18_17_e [NormOneClass A] (h : RudinCharacter A) (a : A) :
    ‖h.val a‖ ≤ (spectralRadius ℂ a).toReal ∧
      (spectralRadius ℂ a).toReal ≤ ‖a‖ := by
  have hupper : spectralRadius ℂ a ≤ (‖a‖₊ : ℝ≥0∞) := spectralRadius_le_nnnorm a
  have hfinite : spectralRadius ℂ a ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
  have hlower : (‖h.val a‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ a := by
    rw [spectralRadius_eq_of_unital]
    exact le_iSup_of_le (h.val a) (le_iSup_of_le (theorem18_17_d h a) le_rfl)
  constructor
  · simpa using ENNReal.toReal_mono hfinite hlower
  · simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hupper

/-- Following 18.17: continuity of every initially algebraic character is automatic. -/
theorem theorem18_17_character_continuous (h : RudinCharacter A) : Continuous h.val :=
  (definition18_16_characterAlgHom h).toContinuousLinearMap.continuous

/-- Following 18.17: in fact the functional norm is exactly one. -/
theorem theorem18_17_character_norm [NormOneClass A] (h : RudinCharacter A) :
    ‖(definition18_16_characterAlgHom h).toContinuousLinearMap‖ = 1 :=
  AlgHom.toContinuousLinearMap_norm _

end BanachCharacters

end RudinRCA.Chapter18

#print axioms RudinRCA.Chapter18.definition18_12_no_unit_in_proper_ideal
#print axioms RudinRCA.Chapter18.definition18_12_mem_kernel
#print axioms RudinRCA.Chapter18.theorem18_13_maximal_containment
#print axioms RudinRCA.Chapter18.theorem18_13_maximal_closed
#print axioms RudinRCA.Chapter18.theorem18_14_coset_eq_iff
#print axioms RudinRCA.Chapter18.theorem18_14_cosets_disjoint
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_kernel
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_isField_iff
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_inf
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_distance
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_complete
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_one
#print axioms RudinRCA.Chapter18.definition18_16_character_map_one
#print axioms RudinRCA.Chapter18.definition18_16_character_surjective
#print axioms RudinRCA.Chapter18.definition18_16_nonzero_iff_surjective
#print axioms RudinRCA.Chapter18.theorem18_17_a
#print axioms RudinRCA.Chapter18.theorem18_17_b
#print axioms RudinRCA.Chapter18.theorem18_17_c
#print axioms RudinRCA.Chapter18.theorem18_17_d
#print axioms RudinRCA.Chapter18.theorem18_17_e
#print axioms RudinRCA.Chapter18.theorem18_17_character_continuous
#print axioms RudinRCA.Chapter18.theorem18_17_character_norm
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_surjective
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_operations
#print axioms RudinRCA.Chapter18.theorem18_14_mem_coset
#print axioms RudinRCA.Chapter18.theorem18_14_quotient_eq_iff
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_surjective
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_operations
#print axioms RudinRCA.Chapter18.theorem18_14_linear_quotient_kernel
#print axioms RudinRCA.Chapter18.theorem18_15_ideal_quotient_complete
#print axioms RudinRCA.Chapter18.theorem18_15_quotient_norm_mul
