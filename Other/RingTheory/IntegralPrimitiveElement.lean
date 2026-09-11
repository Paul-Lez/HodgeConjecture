module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

namespace Algebra

variable (R K L : Type*) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A finite separable extension of the fraction field admits an integral primitive generator. -/
theorem exists_integral_primitive_element :
    ∃ y : L, IsIntegral R y ∧ Algebra.adjoin K {y} = ⊤ := by
  let b := Field.powerBasisOfFiniteOfSeparable K L
  obtain ⟨m, hm⟩ := (b.isIntegral_gen).exists_multiple_integral_of_isLocalization
    (R := R) (nonZeroDivisors R) b.gen
  refine ⟨m • b.gen, hm, ?_⟩
  apply top_unique
  rw [← b.adjoin_gen_eq_top]
  apply Algebra.adjoin_le
  intro x hx
  obtain rfl : x = b.gen := Set.mem_singleton_iff.mp hx
  have hmem := (Algebra.adjoin K {m • b.gen}).smul_mem
    (Algebra.subset_adjoin (Set.mem_singleton _))
    ((algebraMap R K (m : R))⁻¹)
  have hne : algebraMap R K (m : R) ≠ 0 :=
    by
      rw [← map_zero (algebraMap R K)]
      exact (IsFractionRing.injective R K).ne (nonZeroDivisors.ne_zero m.property)
  have hy : m • b.gen = (algebraMap R K (m : R)) • b.gen := by
    rw [Submonoid.smul_def]
    exact (IsScalarTower.algebraMap_smul K (m : R) b.gen).symm
  rw [hy] at hmem ⊢
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at hmem
  exact hmem

/-- Finitely many elements admit a common denominator into an order whose generator is
primitive over the fraction field. -/
theorem exists_common_denominator_of_adjoin_eq_top (y : L)
    (hy : Algebra.adjoin K {y} = ⊤) (s : Finset L) :
    ∃ r : nonZeroDivisors R, ∀ x ∈ s, r • x ∈ Algebra.adjoin R {y} := by
  classical
  induction s using Finset.induction with
  | empty =>
      exact ⟨1, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨ra, hra⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
        (nonZeroDivisors R) K {y} a (by rw [hy]; trivial)
      obtain ⟨rs, hrs⟩ := ih
      refine ⟨ra * rs, fun x hx ↦ ?_⟩
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · rw [Submonoid.smul_def, Submonoid.coe_mul, mul_comm, mul_smul]
        apply (Algebra.adjoin R {y}).smul_mem
        simpa only [Submonoid.smul_def] using hra
      · rw [Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
        apply (Algebra.adjoin R {y}).smul_mem
        simpa only [Submonoid.smul_def] using hrs x hx


/-- The integral primitive generator can be chosen so that every element of the extension
can be cleared into the order it generates over the base domain. -/
theorem exists_integral_primitive_element_and_denominators :
    ∃ y : L, IsIntegral R y ∧ Algebra.adjoin K {y} = ⊤ ∧
      ∀ x : L, ∃ r : nonZeroDivisors R, r • x ∈ Algebra.adjoin R {y} := by
  obtain ⟨y, hy_int, hy⟩ := exists_integral_primitive_element R K L
  refine ⟨y, hy_int, hy, fun x ↦ ?_⟩
  apply multiple_mem_adjoin_of_mem_localization_adjoin (nonZeroDivisors R) K {y} x
  rw [hy]
  trivial

end Algebra
