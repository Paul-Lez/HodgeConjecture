/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import Other.AlgebraicGeometry.OrdinaryExtAmbientComparison
public import Other.AlgebraicTopology.SupportedExtForget
public import Other.AlgebraicTopology.SupportedExtComparisonEvaluation

@[expose] public noncomputable section

open CategoryTheory Limits Abelian TopologicalSpace Opposite

/-- The inverse Hom-complex comparison also commutes with precomposition. -/
lemma CochainComplex.HomComplex.homologyAddEquiv_symm_precompClass
    {C : Type*} [Category* C] [Abelian C]
    {K K' : CochainComplex C ℤ} (g : K' ⟶ K) (L : CochainComplex C ℤ)
    (n : ℤ) (c : CochainComplex.HomComplex.CohomologyClass K L n) :
    (CochainComplex.HomComplex.homologyAddEquiv K' L n).symm
        (CochainComplex.HomComplex.precompClass g L n c) =
      HomologicalComplex.homologyMap (CochainComplex.HomComplex.precompMap g L) n
        ((CochainComplex.HomComplex.homologyAddEquiv K L n).symm c) := by
  apply (CochainComplex.HomComplex.homologyAddEquiv K' L n).injective
  rw [CochainComplex.HomComplex.homologyAddEquiv_precompMap,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

attribute [local instance] rationalConeForgetSheafDerivedCategory
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

local instance supportedExtSiteHasDerivedCategory :
    HasDerivedCategory (CategoryTheory.Sheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat) :=
  HasDerivedCategory.standard _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Evaluation of the Ext-to-supported-sections comparison. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_apply
    (Z : Closeds (ComplexPoint X)) (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    rationalSupportAddEquivSupportedInjectiveHomology X Z n α =
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections (TopCat.of (ComplexPoint X))
          Z.compl ⊤ Z.compl (top_inf_eq _) (ambientRationalInjectiveComplex X)) n).addCommGroupIsoToAddEquiv
        ((CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
            (TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)))
          (ambientRationalInjectiveComplex X) n).symm
          (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ (ambientRationalInjectiveComplex X) n
            (isoHomCongrAddEquiv (Iso.refl _)
              ((shiftFunctor _ (n : ℤ)).mapIso
                (asIso (DerivedCategory.Q.map (ambientRationalInjectiveSingleAugmentation X))))
              (Ext.homAddEquiv α)))) := by
  exact @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_apply
    (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) (analyticHasExt X) _
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n α

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting support in the Ext presentation is the actual inclusion of supported sections
of the chosen ambient injective resolution. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
    (Z : Closeds (ComplexPoint X)) (n : ℕ) (α : H_[Z]^n(X; ℚ)) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n (forgetSupport ℚ X Z n α) =
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) Z.compl ⊤ (ambientRationalInjectiveComplex X)).f n
        (rationalSupportAddEquivSupportedInjectiveHomology X Z n α) := by
  let I := ambientRationalInjectiveComplex X
  let A : AnalyticAdditiveSheaf X := TopCat.Sheaf.pairSheaf' (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _)
  let B : CochainComplex (AnalyticAdditiveSheaf X) ℤ := TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))
  let g : (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℤ) ⟶ A :=
    (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map (show AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) from
          (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom) ≫
      (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
        (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (T := (⊤ : Opens (TopCat.of (ComplexPoint X)))) isTerminalTop).inv ≫
      cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
        (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map (homOfLE (le_top : Z.compl ≤ ⊤)))
  let g₀ : B ⟶ (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A :=
    (CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map g
  let y := isoHomCongrAddEquiv (Iso.refl (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A)))
    ((shiftFunctor _ (n : ℤ)).mapIso
      (asIso (DerivedCategory.Q.map (ambientRationalInjectiveSingleAugmentation X))))
        (Ext.homAddEquiv α)
  have hE := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ))
    (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections_forget (TopCat.of (ComplexPoint X)) Z.compl I)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hE
  have hF (z : (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A) I).homology n) :
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
          (TopCat.of (ComplexPoint X)) I).hom n).hom
        ((HomologicalComplex.homologyMap (CochainComplex.HomComplex.precompMap g₀ I) n).hom z) =
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) Z.compl ⊤ I).f n).hom
        ((HomologicalComplex.homologyMap
          (TopCat.Sheaf.homComplexPairSheafIsoSupportedSections
            (TopCat.of (ComplexPoint X)) Z.compl ⊤ Z.compl (top_inf_eq _) I).hom n).hom z) := by
    have h := congrArg AddCommGrpCat.Hom.hom hE.symm
    rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at h
    exact DFunLike.congr_fun h z
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_eq_extModel]
  have hA :
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map (show AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) from
          (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom))) ≫
        Ext.hom (forgetSupport ℚ X Z n α) ≫
        (shiftFunctor _ (n : ℤ)).map (DerivedCategory.Q.map
          (ambientRationalInjectiveSingleAugmentation X)) =
      DerivedCategory.Q.map g₀ ≫ y := by
    change DerivedCategory.Q.map
        ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).map
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
            (show AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) from
              (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom))) ≫
      Ext.hom ((Ext.mk₀
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
          (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
          (T := (⊤ : Opens (TopCat.of (ComplexPoint X)))) isTerminalTop).inv).comp
        ((Ext.mk₀ (cokernel.π ((CategoryTheory.Sheaf.freeAbelianSheaf
          (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))).map
            (homOfLE (le_top : Z.compl ≤ ⊤))))).comp α (zero_add n)) (zero_add n)) ≫
      (shiftFunctor _ (n : ℤ)).map
        (DerivedCategory.Q.map (ambientRationalInjectiveSingleAugmentation X)) = _
    simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
    dsimp only [g₀, g, y, Ext.homAddEquiv_apply, isoHomCongrAddEquiv_apply,
      Iso.refl_inv, Category.id_comp, Functor.mapIso_hom, asIso_hom]
    simp only [Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
    rfl
  rw [hA, CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_precomp,
    CochainComplex.HomComplex.homologyAddEquiv_symm_precompClass]
  rw [rationalSupportAddEquivSupportedInjectiveHomology_apply]
  simpa only [Iso.addCommGroupIsoToAddEquiv_apply, HomologicalComplex.homologyMapIso_hom]
    using hF ((CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0).obj A) I n).symm
      (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ I n y))

end AlgebraicGeometry.ComplexPoint
