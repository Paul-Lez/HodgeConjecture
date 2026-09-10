/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExponentialClassHodge
public import Other.AlgebraicGeometry.FirstHodgeObstruction

/-!
# The image of the holomorphic exponential class

An integral cohomology class has rational image in the first Hodge filtration precisely when
it comes from the actual holomorphic exponential resolution. This identifies the cohomological
obstruction without assuming a line-bundle or algebraic cycle comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ) [Smooth s]

/-- The quotient of the exponential resolution by its units term, expressed through the
constructed comparison to holomorphic functions. -/
def exponentialResolutionToFunctions :
    holomorphicExponentialResolutionInt s ⟶ holomorphicFunctionComplexInt s :=
  holomorphicExponentialResolutionToDeRhamInt s ≫ deRhamToHolomorphicFunctions s

@[reassoc (attr := simp)]
theorem unitsToExponentialResolution_comp_functions :
    holomorphicUnitsToExponentialResolutionInt s ≫ exponentialResolutionToFunctions s = 0 := by
  unfold exponentialResolutionToFunctions
  rw [← Category.assoc, holomorphicUnitsToExponentialResolutionInt_comp_deRham,
    ← holomorphicDlogFilteredComplexInt_comp_inclusion, Category.assoc,
    hodgeFilteredDeRhamInclusion_comp_functions, comp_zero]

/-- Units in degree one, the exponential resolution, and functions in degree zero. -/
def exponentialClassSequence : ShortComplex (CochainComplex (AnalyticAdditiveSheaf s) ℤ) :=
  ShortComplex.mk (holomorphicUnitsToExponentialResolutionInt s)
    (exponentialResolutionToFunctions s) (unitsToExponentialResolution_comp_functions s)

private theorem exponentialResolutionToFunctions_f_zero_isIso :
    IsIso ((exponentialResolutionToFunctions s).f 0) := by
  have h₀ : IsIso ((holomorphicExponentialResolutionToDeRham s (dim X)).f 0) := by
    change IsIso (holomorphicFunctionToZeroFormSheaf s (dim X))
    exact holomorphicFunctionToZeroFormSheaf_isIso s (dim X)
  have h₁ : IsIso ((holomorphicExponentialResolutionToDeRhamInt s).f 0) := by
    change IsIso ((HomologicalComplex.extendMap
      (holomorphicExponentialResolutionToDeRham s (dim X)) ComplexShape.embeddingUpNat).f (0 : ℤ))
    rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
    infer_instance
  have h₂ : IsIso ((deRhamToHolomorphicFunctions s).f 0) := by
    unfold deRhamToHolomorphicFunctions
    rw [HomologicalComplex.comp_f, CochainComplex.toDegreeZero_f_zero]
    infer_instance
  change IsIso ((holomorphicExponentialResolutionToDeRhamInt s).f 0 ≫
    (deRhamToHolomorphicFunctions s).f 0)
  infer_instance

private theorem unitsToExponentialResolution_f_one_isIso :
    IsIso ((holomorphicUnitsToExponentialResolutionInt s).f 1) := by
  have h₀ : IsIso ((holomorphicUnitsToExponentialResolution s (dim X)).f 1) := by
    simp only [holomorphicUnitsToExponentialResolution, HomologicalComplex.mkHomFromSingle_f,
      Category.comp_id]
    infer_instance
  have h₁ : IsIso ((HomologicalComplex.extendMap
      (holomorphicUnitsToExponentialResolution s (dim X)) ComplexShape.embeddingUpNat).f 1) := by
    rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl]
    infer_instance
  unfold holomorphicUnitsToExponentialResolutionInt
  rw [HomologicalComplex.comp_f]
  infer_instance

/-- This is a short exact sequence of actual sheaf complexes. -/
theorem exponentialClassSequence_shortExact : (exponentialClassSequence s).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h₀ : i = 0
  · subst i
    have hf := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
      (holomorphicUnitsSheaf s (dim X)) 0 (by omega)
    have hg := exponentialResolutionToFunctions_f_zero_isIso s
    refine ShortComplex.ShortExact.mk' ?_ (hf.mono _) ?_
    · apply (ShortComplex.exact_iff_mono _ (hf.eq_of_src _ _)).2
      change Mono ((exponentialResolutionToFunctions s).f 0)
      infer_instance
    · change Epi ((exponentialResolutionToFunctions s).f 0)
      infer_instance
  · have hg := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (holomorphicAdditiveFunctionSheaf s (dim X)) i h₀
    by_cases h₁ : i = 1
    · subst i
      have hf := unitsToExponentialResolution_f_one_isIso s
      refine ShortComplex.ShortExact.mk' ?_ ?_ (hg.epi _)
      · apply (ShortComplex.exact_iff_epi _ (hg.eq_of_tgt _ _)).2
        change Epi ((holomorphicUnitsToExponentialResolutionInt s).f 1)
        infer_instance
      · change Mono ((holomorphicUnitsToExponentialResolutionInt s).f 1)
        infer_instance
    · have hf := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
        (holomorphicUnitsSheaf s (dim X)) i h₁
      have hm : IsZero ((holomorphicExponentialResolutionInt s).X i) := by
        by_cases hi : 0 ≤ i
        · let j := i.toNat
          have hj : ComplexShape.embeddingUpNat.f j = i := by simp [j, hi]
          apply IsZero.of_iso _
            ((holomorphicExponentialResolution s (dim X)).extendXIso
              ComplexShape.embeddingUpNat hj)
          have hj₂ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
          obtain ⟨k, hk⟩ := hj₂
          rw [hk]
          exact isZero_zero _
        · exact (holomorphicExponentialResolution s (dim X)).isZero_extend_X
            ComplexShape.embeddingUpNat i (by intro j; simp; omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hm)
        (hf.mono _) (hg.epi _)

/-- An integral class comes from holomorphic units exactly when its image under the normalized
exponential-to-de Rham comparison belongs to the first filtration. -/
theorem integralExponentialClass_range_iff (n : ℤ)
    (γ : Hypercohomology s (constantIntegerSheafComplexInt s) n) :
    (∃ α, integralExponentialClass s n α = γ) ↔
      hypercohomologyMap s (holomorphicExponentialResolutionToDeRhamInt s) n
        (hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n γ) ∈
          hodgeFiltration s 1 n := by
  rw [mem_firstHodgeFiltration_iff]
  change (∃ α, integralExponentialClass s n α = γ) ↔
    hypercohomologyMap s (deRhamToHolomorphicFunctions s) n
      (hypercohomologyMap s (holomorphicExponentialResolutionToDeRhamInt s) n
        (hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n γ)) = 0
  rw [← hypercohomologyMap_comp_apply]
  change (∃ α, integralExponentialClass s n α = γ) ↔
    hypercohomologyMap s (exponentialClassSequence s).g n
      (hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n γ) = 0
  rw [← hypercohomologyMap_exact s (exponentialClassSequence s)
    (exponentialClassSequence_shortExact s)]
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨α, (augmentation_integralExponentialClass s n α).symm⟩
  · rintro ⟨α, hα⟩
    refine ⟨α, (exponentialResolutionCohomologyEquiv s n).injective ?_⟩
    exact (augmentation_integralExponentialClass s n α).trans hα

/-- The normalized comparison of any integral class has the same `2πi` factor as the
previously constructed exponential classes. -/
theorem integralClass_scaled_deRham (n : ℤ)
    (γ : Hypercohomology s (constantIntegerSheafComplexInt s) n) :
    (2 * (Real.pi : ℂ) * Complex.I) •
      fieldToDeRhamCohomology ℚ s n
        (hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) n γ) =
      hypercohomologyMap s (holomorphicExponentialResolutionToDeRhamInt s) n
        (hypercohomologyMap s (holomorphicExponentialResolutionIntι s) n γ) := by
  rw [deRham_complex_smul_eq]
  change hypercohomologyMap s (scalarHolomorphicDeRhamComplexInt s _) n
    (hypercohomologyMap s (fieldToHolomorphicDeRhamComplexInt ℚ s) n
      (hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) n γ)) = _
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    integerToField_comp_deRhamScalar, ← holomorphicExponentialResolutionIntι_comp_deRham,
    hypercohomologyMap_comp_apply]

/-- The rational image of an actual integral degree-two class is Hodge precisely when that
integral class lies in the image of the holomorphic exponential class map. -/
theorem integralClass_isHodge_iff_exponential
    (γ : Hypercohomology s (constantIntegerSheafComplexInt s) 2) :
    IsHodgeClass ℚ s 1
        (hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) 2 γ) ↔
      ∃ α, integralExponentialClass s 2 α = γ := by
  constructor
  · intro hγ
    apply (integralExponentialClass_range_iff s 2 γ).2
    rw [← integralClass_scaled_deRham]
    exact hodgeFiltration_complex_smul_mem s 1 2 (2 * (Real.pi : ℂ) * Complex.I) hγ
  · rintro ⟨α, rfl⟩
    exact rationalExponentialClass_isHodge s α

end AlgebraicGeometry.ComplexPoint
