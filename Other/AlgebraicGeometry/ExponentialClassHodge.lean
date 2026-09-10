/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialResolution

/-!
# Normalization of exponential classes in the Hodge filtration

The integral-period augmentation of the exponential resolution is compared to the repository's
constant-to-de Rham map, retaining the factor `2πi` explicitly. Consequently the rational
degree-two exponential classes are Hodge classes for the actual variety. The separate comparison
with the repository's topologically constructed algebraic cycle classes is not asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ) [SmoothOfRelativeDimension d s]

/-- The integral-period map to zero-forms agrees with the canonical map of constant sheaves. -/
theorem holomorphicIntegerPeriodSheaf_comp_zeroForm :
    holomorphicIntegerPeriodSheaf s d ≫ holomorphicFunctionToZeroFormSheaf s d =
      integerToFieldConstantSheaf ℂ s (2 * Real.pi * Complex.I) ≫
        constantsToHolomorphicDeRhamZeroSheaf s d := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))
  let τ : ℂ := 2 * Real.pi * Complex.I
  let f : integerPeriodSourcePresheaf s ⟶ constantComplexAddCommGrpPresheaf s :=
    (Functor.const _).map (AddCommGrpCat.ofHom (integerMultipleAddHom ℂ τ))
  have h : holomorphicIntegerPeriodPresheaf s d ≫ holomorphicFunctionToZeroFormPresheaf s d =
      f ≫ constantsToHolomorphicDeRhamZero s d := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro n
    rfl
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext J _ _ (holomorphicDeRhamSheaf s d 0).property
  change toSheafify J (integerPeriodSourcePresheaf s) ≫
      (holomorphicIntegerPeriodSheaf s d).hom ≫ holomorphicFunctionToZeroFormPresheaf s d ≫
        toSheafify J (holomorphicDeRhamPresheaf s d 0) =
    toSheafify J (integerPeriodSourcePresheaf s) ≫ sheafifyMap J f ≫
      sheafifyMap J (constantsToHolomorphicDeRhamZero s d)
  rw [toSheafify_comp_holomorphicIntegerPeriodSheaf_assoc,
    ← toSheafify_naturality_assoc, ← toSheafify_naturality, ← Category.assoc,
    ← Category.assoc, h]

/-- The augmentation followed by the resolution comparison is the normalized constant-to-de
Rham map, as an equality of actual cochain maps. -/
theorem holomorphicExponentialResolutionι_comp_deRham :
    holomorphicExponentialResolutionι s d ≫ holomorphicExponentialResolutionToDeRham s d =
      (CochainComplex.single₀ (AnalyticAdditiveSheaf s)).map
          (integerToFieldConstantSheaf ℂ s (2 * Real.pi * Complex.I)) ≫
        constantsToHolomorphicDeRhamComplex s d := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, holomorphicExponentialResolutionι,
    ShortComplex.rightResolutionι, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero,
    holomorphicExponentialResolutionToDeRham, ShortComplex.fromRightResolution_f_zero,
    CochainComplex.single₀_map_f_zero, constantsToHolomorphicDeRhamComplex]
  exact holomorphicIntegerPeriodSheaf_comp_zeroForm s d

/-- Rationalizing an integer and then multiplying its complex image by `c` gives the constant
integer-multiple map with coefficient `c`. -/
@[reassoc]
theorem integerToField_comp_complexScalarSheaf (c : ℂ) :
    integerToFieldConstantSheaf ℚ s 1 ≫ fieldToComplexConstantSheaf ℚ s ≫
        complexScalarSheaf s c = integerToFieldConstantSheaf ℂ s c := by
  let F := constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))) AddCommGrpCat
  change F.map (AddCommGrpCat.ofHom (integerMultipleAddHom ℚ 1)) ≫
      F.map (AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom) ≫
        F.map (AddCommGrpCat.ofHom (complexScalarAddHom c)) =
    F.map (AddCommGrpCat.ofHom (integerMultipleAddHom ℂ c))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change ℤ at n
  simp [integerMultipleAddHom, complexScalarAddHom, mul_comm]

/-- Integer-indexed version of the coefficient normalization. -/
@[reassoc]
theorem integerToField_comp_complexScalarComplexInt (c : ℂ) :
    integerToFieldConstantSheafComplexInt ℚ s 1 ≫ fieldToComplexConstantSheafComplexInt ℚ s ≫
        complexScalarComplexInt s c = integerToFieldConstantSheafComplexInt ℂ s c := by
  unfold integerToFieldConstantSheafComplexInt fieldToComplexConstantSheafComplexInt
    complexScalarComplexInt complexScalarComplex
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    ← Functor.map_comp, ← Functor.map_comp, integerToField_comp_complexScalarSheaf]

variable [IsIntegral X] [Smooth s]

/-- Scalar multiplication can be moved from the de Rham comparison to the integral coefficient. -/
theorem integerToField_comp_deRhamScalar (c : ℂ) :
    integerToFieldConstantSheafComplexInt ℚ s 1 ≫ fieldToHolomorphicDeRhamComplexInt ℚ s ≫
        scalarHolomorphicDeRhamComplexInt s c =
      integerToFieldConstantSheafComplexInt ℂ s c ≫ constantsToHolomorphicDeRhamComplexInt s := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_scalar,
    integerToField_comp_complexScalarComplexInt_assoc]

/-- Integer-indexed form of the normalized exponential comparison. -/
theorem holomorphicExponentialResolutionIntι_comp_deRham :
    holomorphicExponentialResolutionIntι s ≫ holomorphicExponentialResolutionToDeRhamInt s =
      integerToFieldConstantSheafComplexInt ℂ s (2 * Real.pi * Complex.I) ≫
        constantsToHolomorphicDeRhamComplexInt s := by
  unfold holomorphicExponentialResolutionIntι holomorphicExponentialResolutionToDeRhamInt
    integerToFieldConstantSheafComplexInt constantsToHolomorphicDeRhamComplexInt
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    holomorphicExponentialResolutionι_comp_deRham]

/-- The de Rham image of the rational exponential class is the logarithmic class divided by
the proved integral period `2πi`. -/
theorem rationalExponentialClass_scaled_deRham (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    (2 * (Real.pi : ℂ) * Complex.I) •
        fieldToDeRhamCohomology ℚ s n (rationalExponentialClass s n α) =
      logarithmicClass s n α := by
  rw [deRham_complex_smul_eq]
  change hypercohomologyMap s (scalarHolomorphicDeRhamComplexInt s _) n
    (hypercohomologyMap s (fieldToHolomorphicDeRhamComplexInt ℚ s) n
      (hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) n
        (integralExponentialClass s n α))) = _
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    integerToField_comp_deRhamScalar, ← holomorphicExponentialResolutionIntι_comp_deRham]
  exact integralExponentialClass_logarithmic_comparison s n α

/-- Every rational exponential class has de Rham image in the actual first Hodge filtration. -/
theorem rationalExponentialClass_mem_hodgeFiltration (n : ℤ)
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) n) :
    fieldToDeRhamCohomology ℚ s n (rationalExponentialClass s n α) ∈ hodgeFiltration s 1 n := by
  have h := logarithmicClass_mem_hodgeFiltration s n α
  rw [← rationalExponentialClass_scaled_deRham] at h
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have h' := hodgeFiltration_complex_smul_mem s 1 n
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ h
  simpa only [smul_smul, inv_mul_cancel₀ hperiod, one_smul] using h'

/-- The rational degree-two classes constructed from the actual holomorphic exponential sequence
are Hodge classes, without an assumed filtered lift or an assumed comparison theorem. -/
theorem rationalExponentialClass_isHodge
    (α : Hypercohomology s (holomorphicUnitsComplexInt s) 2) :
    IsHodgeClass ℚ s 1 (rationalExponentialClass s 2 α) :=
  rationalExponentialClass_mem_hodgeFiltration s 2 α

end AlgebraicGeometry.ComplexPoint
