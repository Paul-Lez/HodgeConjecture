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

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- The quotient of the exponential resolution by its units term, expressed through the
constructed comparison to holomorphic functions. -/
def exponentialResolutionToFunctions :
    holomorphicExponentialResolutionInt X ⟶ holomorphicFunctionComplexInt X :=
  holomorphicExponentialResolutionToDeRhamInt X ≫ deRhamToHolomorphicFunctions X

@[reassoc (attr := simp)]
theorem unitsToExponentialResolution_comp_functions :
    holomorphicUnitsToExponentialResolutionInt X ≫ exponentialResolutionToFunctions X = 0 := by
  unfold exponentialResolutionToFunctions
  rw [← Category.assoc, holomorphicUnitsToExponentialResolutionInt_comp_deRham,
    ← holomorphicDlogFilteredComplexInt_comp_inclusion, Category.assoc,
    hodgeFilteredDeRhamInclusion_comp_functions, comp_zero]

/-- Units in degree one, the exponential resolution, and functions in degree zero. -/
def exponentialClassSequence : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  ShortComplex.mk (holomorphicUnitsToExponentialResolutionInt X)
    (exponentialResolutionToFunctions X) (unitsToExponentialResolution_comp_functions X)

private theorem exponentialResolutionToFunctions_f_zero_isIso :
    IsIso ((exponentialResolutionToFunctions X).f 0) := by
  have h₀ : IsIso ((holomorphicExponentialResolutionToDeRham X (dim X.left)).f 0) := by
    change IsIso (holomorphicFunctionToZeroFormSheaf X (dim X.left))
    exact holomorphicFunctionToZeroFormSheaf_isIso X (dim X.left)
  have h₁ : IsIso ((holomorphicExponentialResolutionToDeRhamInt X).f 0) := by
    change IsIso ((HomologicalComplex.extendMap
      (holomorphicExponentialResolutionToDeRham X (dim X.left)) ComplexShape.embeddingUpNat).f (0 : ℤ))
    rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
    infer_instance
  have h₂ : IsIso ((deRhamToHolomorphicFunctions X).f 0) := by
    unfold deRhamToHolomorphicFunctions
    rw [HomologicalComplex.comp_f, CochainComplex.toDegreeZero_f_zero]
    infer_instance
  change IsIso ((holomorphicExponentialResolutionToDeRhamInt X).f 0 ≫
    (deRhamToHolomorphicFunctions X).f 0)
  infer_instance

private theorem unitsToExponentialResolution_f_one_isIso :
    IsIso ((holomorphicUnitsToExponentialResolutionInt X).f 1) := by
  have h₀ : IsIso ((holomorphicUnitsToExponentialResolution X (dim X.left)).f 1) := by
    simp only [holomorphicUnitsToExponentialResolution, HomologicalComplex.mkHomFromSingle_f,
      Category.comp_id]
    infer_instance
  have h₁ : IsIso ((HomologicalComplex.extendMap
      (holomorphicUnitsToExponentialResolution X (dim X.left)) ComplexShape.embeddingUpNat).f 1) := by
    rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl]
    infer_instance
  unfold holomorphicUnitsToExponentialResolutionInt
  rw [HomologicalComplex.comp_f]
  infer_instance

/-- This is a short exact sequence of actual sheaf complexes. -/
theorem exponentialClassSequence_shortExact : (exponentialClassSequence X).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h₀ : i = 0
  · subst i
    have hf := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
      (holomorphicUnitsSheaf X (dim X.left)) 0 (by omega)
    have hg := exponentialResolutionToFunctions_f_zero_isIso X
    refine ShortComplex.ShortExact.mk' ?_ (hf.mono _) ?_
    · apply (ShortComplex.exact_iff_mono _ (hf.eq_of_src _ _)).2
      change Mono ((exponentialResolutionToFunctions X).f 0)
      infer_instance
    · change Epi ((exponentialResolutionToFunctions X).f 0)
      infer_instance
  · have hg := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (holomorphicAdditiveFunctionSheaf X (dim X.left)) i h₀
    by_cases h₁ : i = 1
    · subst i
      have hf := unitsToExponentialResolution_f_one_isIso X
      refine ShortComplex.ShortExact.mk' ?_ ?_ (hg.epi _)
      · apply (ShortComplex.exact_iff_epi _ (hg.eq_of_tgt _ _)).2
        change Epi ((holomorphicUnitsToExponentialResolutionInt X).f 1)
        infer_instance
      · change Mono ((holomorphicUnitsToExponentialResolutionInt X).f 1)
        infer_instance
    · have hf := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 1
        (holomorphicUnitsSheaf X (dim X.left)) i h₁
      have hm : IsZero ((holomorphicExponentialResolutionInt X).X i) := by
        by_cases hi : 0 ≤ i
        · let j := i.toNat
          have hj : ComplexShape.embeddingUpNat.f j = i := by simp [j, hi]
          apply IsZero.of_iso _
            ((holomorphicExponentialResolution X (dim X.left)).extendXIso
              ComplexShape.embeddingUpNat hj)
          have hj₂ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
          obtain ⟨k, hk⟩ := hj₂
          rw [hk]
          exact isZero_zero _
        · exact (holomorphicExponentialResolution X (dim X.left)).isZero_extend_X
            ComplexShape.embeddingUpNat i (by intro j; simp; omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hm)
        (hf.mono _) (hg.epi _)

/-- An integral class comes from holomorphic units exactly when its image under the normalized
exponential-to-de Rham comparison belongs to the first filtration. -/
theorem integralExponentialClass_range_iff (n : ℤ)
    (γ : Hypercohomology X (constantIntegerSheafComplexInt X) n) :
    (∃ α, integralExponentialClass X n α = γ) ↔
      hypercohomologyMap X (holomorphicExponentialResolutionToDeRhamInt X) n
        (hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n γ) ∈
          hodgeFiltration X 1 n := by
  rw [mem_firstHodgeFiltration_iff]
  change (∃ α, integralExponentialClass X n α = γ) ↔
    hypercohomologyMap X (deRhamToHolomorphicFunctions X) n
      (hypercohomologyMap X (holomorphicExponentialResolutionToDeRhamInt X) n
        (hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n γ)) = 0
  rw [← hypercohomologyMap_comp_apply]
  change (∃ α, integralExponentialClass X n α = γ) ↔
    hypercohomologyMap X (exponentialClassSequence X).g n
      (hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n γ) = 0
  rw [← hypercohomologyMap_exact X (exponentialClassSequence X)
    (exponentialClassSequence_shortExact X)]
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨α, (augmentation_integralExponentialClass X n α).symm⟩
  · rintro ⟨α, hα⟩
    refine ⟨α, (exponentialResolutionCohomologyEquiv X n).injective ?_⟩
    exact (augmentation_integralExponentialClass X n α).trans hα

/-- The normalized comparison of any integral class has the same `2πi` factor as the
previously constructed exponential classes. -/
theorem integralClass_scaled_deRham (n : ℤ)
    (γ : Hypercohomology X (constantIntegerSheafComplexInt X) n) :
    (2 * (Real.pi : ℂ) * Complex.I) •
      fieldToDeRhamCohomology ℚ X n
        (hypercohomologyMap X (integerToFieldConstantSheafComplexInt ℚ X 1) n γ) =
      hypercohomologyMap X (holomorphicExponentialResolutionToDeRhamInt X) n
        (hypercohomologyMap X (holomorphicExponentialResolutionIntι X) n γ) := by
  rw [deRham_complex_smul_eq]
  change hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X _) n
    (hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt ℚ X) n
      (hypercohomologyMap X (integerToFieldConstantSheafComplexInt ℚ X 1) n γ)) = _
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    integerToField_comp_deRhamScalar, ← holomorphicExponentialResolutionIntι_comp_deRham,
    hypercohomologyMap_comp_apply]

/-- The rational image of an actual integral degree-two class is Hodge precisely when that
integral class lies in the image of the holomorphic exponential class map. -/
theorem integralClass_isHodge_iff_exponential
    (γ : Hypercohomology X (constantIntegerSheafComplexInt X) 2) :
    IsHodgeClass ℚ X 1
        (hypercohomologyMap X (integerToFieldConstantSheafComplexInt ℚ X 1) 2 γ) ↔
      ∃ α, integralExponentialClass X 2 α = γ := by
  constructor
  · intro hγ
    apply (integralExponentialClass_range_iff X 2 γ).2
    rw [← integralClass_scaled_deRham]
    exact hodgeFiltration_complex_smul_mem X 1 2 (2 * (Real.pi : ℂ) * Complex.I) hγ
  · rintro ⟨α, rfl⟩
    exact rationalExponentialClass_isHodge X α

end AlgebraicGeometry.ComplexPoint
