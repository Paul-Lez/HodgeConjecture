/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExponentialConnectingComparison

/-!
# Comparing connecting classes with exponential resolution classes

The shift convention used by sheaf Ext is compared with the placement of units in
degree one in the existing exponential resolution.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 5000

open CategoryTheory Limits TopologicalSpace CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

open Localization

local instance exponentialResolutionComparisonDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance exponentialResolutionComparisonSmallHom
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ) :
    HasSmallLocalizedHom.{1} (analyticQuasiIsomorphisms X) K L :=
  hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀
    (analyticQuasiIsomorphisms X) ℤ K L

private theorem smallShiftedHom_comp_mk
    {K L M : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {a b c : ℤ}
    (α : SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) K L a)
    (f : L ⟶ M⟦b⟧) (h : b + a = c) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f) h =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X)
        (f⟦a⟧' ≫ (CategoryTheory.shiftFunctorAdd' _ b a c h).inv.app M)) := by
  simp only [SmallShiftedHom.comp, SmallShiftedHom.shift, SmallShiftedHom.mk,
    SmallHom.shift, LocalizerMorphism.smallHomMap_mk, SmallHom.mk_comp_mk]

private theorem hypercohomologyMap_smallHom
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : K ⟶ L) (n : ℤ)
    (α : Hypercohomology X K n) :
    hypercohomologyMap X f n α =
      SmallHom.comp α (SmallHom.mk (analyticQuasiIsomorphisms X) (f⟦n⟧')) := by
  change SmallShiftedHom.comp α
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (ShiftedHom.mk₀ 0 rfl f)) _ = _
  rw [smallShiftedHom_comp_mk]
  congr 2
  simp only [ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorAdd'_zero_add_inv_app, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.id_obj, Category.comp_id]

/-- The existing Ext/hypercohomology equivalence written directly in small localized homs. -/
theorem sheafExtHypercohomologyEquiv_smallHom (F : AnalyticAdditiveSheaf X) (j : ℤ) (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X) F n) :
    sheafExtHypercohomologyEquiv X F j n α =
      (SmallHom.mk (analyticQuasiIsomorphisms X) (constantIntegerComplexIsoSingle X).hom).comp
        (SmallHom.comp α
          (SmallHom.mk (analyticQuasiIsomorphisms X) (sheafSingleShiftIso X F j n).hom)) := by
  apply (SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  change SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
    ((SmallHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).symm _) = _
  rw [Equiv.apply_symm_apply]
  simp only [SmallHom.equiv_comp, SmallHom.equiv_mk]
  rfl

/-- The placement-degree-one identification is compatible with further shifts. -/
theorem sheafSingleShiftIso_one_hom (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    (sheafSingleShiftIso X F 1 n).hom =
      (((CochainComplex.singleFunctors (AnalyticAdditiveSheaf X)).shiftIso
        1 0 1 (by omega)).inv.app F)⟦(n : ℤ)⟧' ≫
        (CategoryTheory.shiftFunctorAdd' (CochainComplex (AnalyticAdditiveSheaf X) ℤ)
          1 (n : ℤ) ((n : ℤ) + 1) (by omega)).inv.app
            ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 1).obj F) := by
  simp only [sheafSingleShiftIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [(CochainComplex.singleFunctors (AnalyticAdditiveSheaf X)).shiftIso_add'_inv_app
    (n : ℤ) 1 ((n : ℤ) + 1) (by omega) (-(n : ℤ)) 0 1 (by omega) (by omega) F]
  simp only [Iso.hom_inv_id_app_assoc]

/-- Placement degree zero does not change the shifted single complex. -/
theorem sheafSingleShiftIso_zero (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    sheafSingleShiftIso X F 0 n = Iso.refl _ := by
  unfold sheafSingleShiftIso
  exact Iso.self_symm_id _

variable [IsIntegral X.left] [Smooth X.hom]

/-- The comparison cocycle is the actual logarithmic derivative after the canonical
identification of units in degree zero with units in degree one shifted once. -/
theorem exponentialComparisonCocycle_eq_dlog :
    exponentialComparisonCocycle X =
      ((CochainComplex.singleFunctors (AnalyticAdditiveSheaf X)).shiftIso
        1 0 1 (by omega)).inv.app (holomorphicUnitsSheaf X (dim X.left)) ≫
          (holomorphicDlogComplexInt X)⟦(1 : ℤ)⟧' := by
  apply HomologicalComplex.from_single_hom_ext
  simp [exponentialComparisonCocycle, Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cochain.rightShift_v, Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v,
    holomorphicDlogComplexInt, CochainComplex.singleFunctors, exponentialComparisonOne,
    holomorphicDlogComplex,
    HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 1) (i' := 1) rfl,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.id_comp, Category.id_comp]

/-- The degree-one logarithmic cocycle gives the already constructed logarithmic
class after the existing Ext/hypercohomology change of placement degree. -/
theorem logarithmicClass_sheafExtHypercohomologyEquiv (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) n) :
    logarithmicClass X ((n : ℤ) + 1)
      (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 1 n α) =
      SmallShiftedHom.comp
        (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 0 n α)
        (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (exponentialComparisonCocycle X))
        (by omega) := by
  unfold logarithmicClass
  rw [hypercohomologyMap_smallHom, sheafExtHypercohomologyEquiv_smallHom,
    sheafExtHypercohomologyEquiv_smallHom, smallShiftedHom_comp_mk,
    sheafSingleShiftIso_zero]
  simp only [Iso.refl_hom, SmallHom.comp_mk_id]
  rw [SmallHom.comp_assoc, SmallHom.comp_assoc, SmallHom.mk_comp_mk,
    SmallHom.comp_assoc]
  congr 3
  rw [sheafSingleShiftIso_one_hom, exponentialComparisonCocycle_eq_dlog,
    CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (fun f =>
    (((CochainComplex.singleFunctors (AnalyticAdditiveSheaf X)).shiftIso
      1 0 1 (by omega)).inv.app (holomorphicUnitsSheaf X (dim X.left)))⟦(n : ℤ)⟧' ≫ f)
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex (AnalyticAdditiveSheaf X) ℤ)
      1 (n : ℤ) ((n : ℤ) + 1) (by omega)).inv.naturality (holomorphicDlogComplexInt X)).symm

private theorem logarithmicCocycleClass_neg (n : ℕ)
    (α : Hypercohomology X
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
        (holomorphicUnitsSheaf X (dim X.left))) (n : ℤ)) :
    α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (-exponentialComparisonCocycle X)) (show 1 + (n : ℤ) = (n : ℤ) + 1 by omega) =
    -α.comp (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (exponentialComparisonCocycle X)) (show 1 + (n : ℤ) = (n : ℤ) + 1 by omega) := by
  let E : DeRhamHypercohomology X ((n : ℤ) + 1) ≃+
      ShiftedHom (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (holomorphicDeRhamComplexInt X)) ((n : ℤ) + 1) :=
    { toEquiv := SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
      map_add' := hypercohomologyEquiv_add X (holomorphicDeRhamComplexInt X) ((n : ℤ) + 1) }
  apply E.injective
  rw [E.map_neg]
  change SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q _ =
    -SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, ShiftedHom.map,
    CategoryTheory.Functor.map_neg, Preadditive.neg_comp, ShiftedHom.comp_neg]

/-- The rational class of the actual Ext connecting morphism is the negative of the
existing exponential-resolution class. The sign is forced by the mapping-cone convention. -/
theorem rationalExponentialConnectingClass_eq_neg (n : ℕ)
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) n) :
    rationalExponentialConnectingClass X n α =
      -rationalExponentialClass X ((n : ℤ) + 1)
        (sheafExtHypercohomologyEquiv X (holomorphicUnitsSheaf X (dim X.left)) 1 n α) := by
  apply fieldToDeRhamCohomology_injective ℚ X ((n : ℤ) + 1)
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have h : (2 * (Real.pi : ℂ) * Complex.I) •
        fieldToDeRhamCohomology ℚ X ((n : ℤ) + 1)
          (rationalExponentialConnectingClass X n α) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        fieldToDeRhamCohomology ℚ X ((n : ℤ) + 1)
          (-rationalExponentialClass X ((n : ℤ) + 1)
            (sheafExtHypercohomologyEquiv X
              (holomorphicUnitsSheaf X (dim X.left)) 1 n α)) := by
    rw [rationalExponentialConnectingClass_scaled_deRham, logarithmicCocycleClass_neg,
      ← logarithmicClass_sheafExtHypercohomologyEquiv, map_neg, smul_neg,
      rationalExponentialClass_scaled_deRham]
  have h' := congrArg (fun β : DeRhamHypercohomology X ((n : ℤ) + 1) =>
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • β) h
  simpa only [smul_smul, inv_mul_cancel₀ hperiod, one_smul] using h'

/-- The degree-two rational class of the actual exponential Ext boundary is Hodge. -/
theorem rationalExponentialConnectingClass_isHodge
    (α : Abelian.Ext.{1} (constantIntegerSheaf X)
      (holomorphicUnitsSheaf X (dim X.left)) 1) :
    IsHodgeClass ℚ X 1 (rationalExponentialConnectingClass X 1 α) := by
  rw [rationalExponentialConnectingClass_eq_neg]
  change fieldToDeRhamCohomology ℚ X 2 (-rationalExponentialClass X 2 _) ∈
    hodgeFiltration X 1 2
  rw [map_neg]
  exact (hodgeFiltration X 1 2).neg_mem (rationalExponentialClass_isHodge X _)

end AlgebraicGeometry.ComplexPoint
