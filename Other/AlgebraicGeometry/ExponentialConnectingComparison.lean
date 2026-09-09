/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.ShortExactComparisonExt
public import Other.AlgebraicGeometry.ExponentialClassHodge
public import Other.AlgebraicGeometry.SheafExtHypercohomology

/-!
# The connecting class of the holomorphic exponential sequence

The actual exponential sequence and the actual holomorphic de Rham complex satisfy
the connecting-class comparison. The comparison retains the minus sign forced by
the mapping-cone triangle convention and the integral period `2πi`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

local instance exponentialComparisonHasExt : HasExt.{1} (AnalyticAdditiveSheaf X) := analyticHasExt X

/-- Holomorphic functions as degree-zero terms of the integer-indexed de Rham complex. -/
def exponentialComparisonZero :
    (holomorphicExponentialSequence X (dim X.left)).X₂ ⟶
      (holomorphicDeRhamComplexInt X).X 0 :=
  holomorphicFunctionToZeroFormSheaf X (dim X.left) ≫
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv

/-- The logarithmic derivative as a degree-one term of the integer-indexed complex. -/
def exponentialComparisonOne :
    (holomorphicExponentialSequence X (dim X.left)).X₃ ⟶
      (holomorphicDeRhamComplexInt X).X 1 :=
  holomorphicDlogSheaf X (dim X.left) ≫
    ((holomorphicDeRhamComplex X (dim X.left)).extendXIso
      ComplexShape.embeddingUpNat (i := 1) rfl).inv

/-- The analytic chain rule supplies the compatibility needed for the connecting comparison. -/
theorem exponentialComparison_differential :
    exponentialComparisonZero X ≫ (holomorphicDeRhamComplexInt X).d 0 1 =
      (holomorphicExponentialSequence X (dim X.left)).g ≫ exponentialComparisonOne X := by
  unfold exponentialComparisonZero exponentialComparisonOne holomorphicDeRhamComplexInt
  rw [HomologicalComplex.extend_d_eq (holomorphicDeRhamComplex X (dim X.left))
    ComplexShape.embeddingUpNat (i' := 0) (j' := 1) (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, holomorphicDeRhamComplex_d]
  rw [← holomorphicExpSheaf_comp_dlog_assoc]
  rfl

/-- The logarithmic derivative is closed in the actual analytic de Rham complex. -/
theorem exponentialComparison_closed :
    exponentialComparisonOne X ≫ (holomorphicDeRhamComplexInt X).d 1 2 = 0 := by
  unfold exponentialComparisonOne holomorphicDeRhamComplexInt
  rw [HomologicalComplex.extend_d_eq (holomorphicDeRhamComplex X (dim X.left))
    ComplexShape.embeddingUpNat (i' := 1) (j' := 2) (i := 1) (j := 2) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, holomorphicDeRhamComplex_d]
  rw [← Category.assoc, holomorphicDlogSheaf_comp_differential, zero_comp]

/-- The comparison of the actual integral-period kernel with the de Rham complex. -/
def exponentialComparisonKernel :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj (constantIntegerSheaf X) ⟶
      holomorphicDeRhamComplexInt X :=
  (holomorphicExponentialSequence X (dim X.left)).comparisonKernelMap
    (holomorphicDeRhamComplexInt X) (exponentialComparisonZero X) (exponentialComparisonOne X)
      (exponentialComparison_differential X)

/-- The closed degree-one logarithmic cocycle, with its source in degree zero. -/
def exponentialComparisonCocycle :
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (holomorphicUnitsSheaf X (dim X.left)) ⟶ (holomorphicDeRhamComplexInt X)⟦(1 : ℤ)⟧ :=
  Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk (exponentialComparisonOne X) (show 0 + 1 = 1 from rfl)
      2 rfl (exponentialComparison_closed X))

/-- The kernel comparison is the canonical constant-to-de Rham map with the proved
integral period `2πi`, using the actual constant integer complex. -/
theorem exponentialComparisonKernel_normalization :
    exponentialComparisonKernel X =
      (constantIntegerComplexIsoSingle X).inv ≫
        integerToFieldConstantSheafComplexInt ℂ X (2 * Real.pi * Complex.I) ≫
          constantsToHolomorphicDeRhamComplexInt X := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [exponentialComparisonKernel, ShortComplex.comparisonKernelMap, Cocycle.homOf_f,
    Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v,
    HomologicalComplex.comp_f, constantIntegerComplexIsoSingle,
    HomologicalComplex.extendSingleIso_inv_f,
    integerToFieldConstantSheafComplexInt, constantsToHolomorphicDeRhamComplexInt,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc,
    CochainComplex.single₀_map_f_zero, constantsToHolomorphicDeRhamComplex,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp only [exponentialComparisonZero, holomorphicExponentialSequence]
  rw [reassoc_of% (holomorphicIntegerPeriodSheaf_comp_zeroForm X (dim X.left))]
  simp [constantFieldSheaf, constantComplexSheaf, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

/-- The actual exponential Ext class followed by the integral-period comparison is the
negative logarithmic cocycle in the repository's small-localization model. -/
theorem exponentialConnectingClass_comparison :
    Localization.SmallShiftedHom.comp.{1}
      (holomorphicExponentialSequence_shortExact X (dim X.left)).extClass
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (exponentialComparisonKernel X)) (show 0 + 1 = 1 from rfl) =
      Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (-exponentialComparisonCocycle X) :=
  (holomorphicExponentialSequence X (dim X.left)).comparisonExt.{1} (holomorphicDeRhamComplexInt X)
    (holomorphicExponentialSequence_shortExact X (dim X.left)) (exponentialComparisonZero X)
      (exponentialComparisonOne X) (exponentialComparison_differential X)
        (exponentialComparison_closed X)

local instance exponentialComparisonDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- In placement degree zero, the existing Ext/hypercohomology equivalence is
precomposition with the canonical identification of the constant integer complex. -/
theorem sheafExtHypercohomologyEquiv_zeroDegree (F : AnalyticAdditiveSheaf X) (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X) F n) :
    sheafExtHypercohomologyEquiv X F 0 n α =
      Localization.SmallShiftedHom.comp
        (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (constantIntegerComplexIsoSingle X).hom) α (by simp) := by
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
    ShiftedHom.mk₀_comp]
  have hshift : sheafSingleShiftIso X F 0 n = Iso.refl _ := by
    unfold sheafSingleShiftIso
    exact Iso.self_symm_id _
  change Localization.SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      ((Localization.SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).symm
        (DerivedCategory.Q.map (constantIntegerComplexIsoSingle X).hom ≫
          Localization.SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q α ≫
            DerivedCategory.Q.map (sheafSingleShiftIso X F 0 n).hom)) ≫
      (DerivedCategory.Q.commShiftIso ((n : ℤ) + 0)).hom.app
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj F) = _
  rw [Equiv.apply_symm_apply, hshift]
  simp only [Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id, Category.assoc]
  rfl

/-- The connecting comparison after transport from sheaf Ext to the actual analytic
hypercohomology model, in every nonnegative sheaf-cohomology degree. -/
theorem exponentialConnectingClass_hypercohomology (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) n) :
    hypercohomologyMap X (exponentialComparisonKernel X) ((n : ℤ) + 1)
      (sheafExtHypercohomologyEquiv X (constantIntegerSheaf X) 0 (n + 1)
        (α.comp (holomorphicExponentialSequence_shortExact X (dim X.left)).extClass rfl)) =
      Localization.SmallShiftedHom.comp
        (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 0 n α)
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (-exponentialComparisonCocycle X)) (by omega) := by
  rw [sheafExtHypercohomologyEquiv_zeroDegree, sheafExtHypercohomologyEquiv_zeroDegree]
  change Localization.SmallShiftedHom.comp
    (Localization.SmallShiftedHom.comp _ (Localization.SmallShiftedHom.comp _ _ _) _)
    _ _ = _
  rw [Localization.SmallShiftedHom.comp_assoc,
    Localization.SmallShiftedHom.comp_assoc, exponentialConnectingClass_comparison,
    Localization.SmallShiftedHom.comp_assoc]
  all_goals first | exact ((n : ℤ) + 1) | omega

/-- Rationalization of the actual exponential connecting class, using the existing
Ext/hypercohomology equivalence and the actual constant-sheaf coefficient map. -/
def rationalExponentialConnectingClass (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) n) : FieldCohomology ℚ X ((n : ℤ) + 1) :=
  hypercohomologyMap X
    ((constantIntegerComplexIsoSingle X).inv ≫ integerToFieldConstantSheafComplexInt ℚ X 1)
    ((n : ℤ) + 1)
    (sheafExtHypercohomologyEquiv X (constantIntegerSheaf X) 0 (n + 1)
      (α.comp (holomorphicExponentialSequence_shortExact X (dim X.left)).extClass rfl))

/-- The rational connecting class has de Rham image equal to the negative logarithmic
cocycle divided by `2πi`. Both the sign and period come from the constructed sequence. -/
theorem rationalExponentialConnectingClass_scaled_deRham (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) n) :
    (2 * (Real.pi : ℂ) * Complex.I) •
        fieldToDeRhamCohomology ℚ X ((n : ℤ) + 1)
          (rationalExponentialConnectingClass X n α) =
      Localization.SmallShiftedHom.comp
        (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 0 n α)
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (-exponentialComparisonCocycle X)) (by omega) := by
  rw [deRham_complex_smul_eq]
  change hypercohomologyMap X (scalarHolomorphicDeRhamComplexInt X _) _
    (hypercohomologyMap X (fieldToHolomorphicDeRhamComplexInt ℚ X) _
      (hypercohomologyMap X _ _ _)) = _
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  simp only [Category.assoc]
  rw [integerToField_comp_deRhamScalar,
    ← exponentialComparisonKernel_normalization]
  exact exponentialConnectingClass_hypercohomology X n α

end AlgebraicGeometry.ComplexPoint
