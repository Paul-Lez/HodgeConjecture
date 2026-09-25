/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalDerivedBoundary
public import Other.AlgebraicGeometry.RelativeChernOriginalFrameFactorisation
public import Other.AlgebraicGeometry.HolomorphicExponentialSingularRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
open CategoryTheory.Localization

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 4000000

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsIntegral X.left] [Smooth X.hom]
variable (E : HolomorphicUnitExtension X d)
  (Ω U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (ℓΩ : E.middle.obj.obj (op Ω))
  (hℓΩ : E.projection.hom.app (op Ω) ℓΩ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (cmp : RelativeChernComparison X d Ω)
  (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω)))
  (hw : E.inclusion.hom.app (op (U ⊓ Ω)) w =
      E.middle.obj.map (homOfLE (inf_le_right : U ⊓ Ω ≤ Ω)).op ℓΩ -
      E.middle.obj.map (homOfLE (inf_le_left : U ⊓ Ω ≤ U)).op ℓU)
local instance targetAmbient : HasDerivedCategory (AnalyticAdditiveSheaf X) := HasDerivedCategory.standard _
local instance targetOpen : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) := HasDerivedCategory.standard _

include hℓU hw in
/-- The original relative Chern class restricts to the boundary of the negative frame difference. -/
lemma restrict_original_relativeChernClass_derived_boundary :
  let C := rationalCohomologyWithSupportComplex X ((Ω : Set (ComplexPoint X))ᶜ)
  let F := restrictToOpen X U
  let D := F.mapDerivedCategory
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  let α := E.relativeChernClass Ω ℓΩ hℓΩ cmp
  let βΩ := Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)
  D.map (
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
      SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q α ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
    F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) =
  F.mapDerivedCategoryFactors.hom.app
      ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) ≫
    DerivedCategory.Q.map
      (I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
        J.map (restrictedOverlapUnitHom X d Ω U (-w)) ≫
        I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) ≫
        H.map (βΩ ≫
          (CochainComplex.mappingCone.inr
            (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧')) := by
  dsimp only
  let C := rationalCohomologyWithSupportComplex X ((Ω : Set (ComplexPoint X))ᶜ)
  let F := restrictToOpen X U
  let D := F.mapDerivedCategory
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  let α := E.relativeChernClass Ω ℓΩ hℓΩ cmp
  let βΩ := Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)
  have hcmp := congrArg
    (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
    (cmp.boundary_eq_singular X d)
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
    SmallShiftedHom.equiv_mk, ShiftedHom.mk₀_comp] at hcmp
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality] at hcmp
  have hcmp' :
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.inr
            ((analyticSingleFunctor X).map (restrictionUnit Ω
              (holomorphicUnitSheaf X d)))) ≫
        (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q cmp.hom) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C =
      DerivedCategory.Q.map
        (βΩ ≫
          (shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) 1).map
            (CochainComplex.mappingCone.inr
              (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))) := by
    have hcmp2 := congrArg
      (fun f => f ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) hcmp
    simp only [Category.assoc, ← Functor.commShiftIso_hom_naturality] at hcmp2
    rw [Iso.hom_inv_id_app] at hcmp2
    simpa [βΩ] using hcmp2
  rw [E.relativeChernClass_equiv X Ω ℓΩ hℓΩ cmp]
  simp only [Functor.map_comp]
  have hR := F.mapDerivedCategoryFactors_hom_naturality
    (E.relativeConeMap Ω ℓΩ hℓΩ)
  have hinv := restrict_coneToInteger_inv_comp_factors_eq_restrictedConeSection
    X d E U ℓU hℓU
  have hchain := congrArg DerivedCategory.Q.map
    (restrictedConeSection_comp_relativeConeMap_eq_overlapUnitHom
      X d E Ω U ℓU ℓΩ hℓΩ hℓU w hw)
  let f := CochainComplex.mappingCone.inr
    ((analyticSingleFunctor X).map (restrictionUnit Ω
      (holomorphicUnitSheaf X d)))
  let b := βΩ ≫
    (shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) 1).map
      (CochainComplex.mappingCone.inr
        (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))
  have hInr := F.mapDerivedCategoryFactors_hom_naturality f
  have hβfac := F.mapDerivedCategoryFactors_hom_naturality b
  have hInrInv :
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
          F.mapDerivedCategoryFactors.inv.app (relativeUnitCone X d Ω) =
        F.mapDerivedCategoryFactors.inv.app
            ((analyticSingleFunctor X).obj
              ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
          F.mapDerivedCategory.map (DerivedCategory.Q.map f) := by
    apply (cancel_mono
      (F.mapDerivedCategoryFactors.hom.app (relativeUnitCone X d Ω))).1
    simp only [Category.assoc,
      F.mapDerivedCategoryFactors.inv_hom_id_app]
    rw [hInr]
    simp only [F.mapDerivedCategoryFactors.inv_hom_id_app_assoc]
    exact Category.comp_id _
  have hcmpD := congrArg D.map hcmp'
  simp only [Functor.map_comp] at hcmpD
  have hcmpD_tr := congrArg
    (fun z => z ≫ F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧)) hcmpD
  simp only [Category.assoc] at hcmpD_tr
  have htail :
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
          F.mapDerivedCategoryFactors.inv.app (relativeUnitCone X d Ω) ≫
          D.map ((SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
            DerivedCategory.Q) cmp.hom) ≫
          D.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
          F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) =
        DerivedCategory.Q.map (H.map b) := by
    have ht1 := congrArg
      (fun z => z ≫ D.map ((SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms X) DerivedCategory.Q) cmp.hom) ≫
        D.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
        F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧)) hInrInv
    have ht2 := congrArg
      (fun z => F.mapDerivedCategoryFactors.inv.app
        ((analyticSingleFunctor X).obj
          ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫ z)
      hcmpD_tr
    have ht3 := congrArg
      (fun z => F.mapDerivedCategoryFactors.inv.app
        ((analyticSingleFunctor X).obj
          ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫ z)
      hβfac
    simp only [Category.assoc] at ht1 ht2 ht3
    calc
      _ = F.mapDerivedCategoryFactors.inv.app
            ((analyticSingleFunctor X).obj
              ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
          D.map (DerivedCategory.Q.map f) ≫
          D.map ((SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
            DerivedCategory.Q) cmp.hom) ≫
          D.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
          F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) := ht1
      _ = F.mapDerivedCategoryFactors.inv.app
            ((analyticSingleFunctor X).obj
              ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
          D.map (DerivedCategory.Q.map b) ≫
          F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) := by
            simpa only [f, b, Functor.map_comp, Category.assoc] using ht2
      _ = F.mapDerivedCategoryFactors.inv.app
            ((analyticSingleFunctor X).obj
              ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
          F.mapDerivedCategoryFactors.hom.app
            ((analyticSingleFunctor X).obj
              ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
          DerivedCategory.Q.map (H.map b) := ht3
      _ = DerivedCategory.Q.map (H.map b) := by
        simp only [F.mapDerivedCategoryFactors.inv_hom_id_app_assoc]
  have hconst :
      D.map (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv) ≫
        D.map (DerivedCategory.Q.map
          (analyticSheafComplexIntIsoSingle X
            (𝓒(↧(ComplexPoint X); ℤ))).hom) =
        𝟙 _ := by
    change D.map (DerivedCategory.Q.map
        (constantIntegerSheafComplexIntIsoSingle X).inv) ≫
      D.map (DerivedCategory.Q.map
        (constantIntegerSheafComplexIntIsoSingle X).hom) = _
    rw [← D.map_comp, ← CategoryTheory.Functor.map_comp]
    simp
  have hfactor :
      D.map (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv) ≫
        D.map (DerivedCategory.Q.map
          (analyticSheafComplexIntIsoSingle X
            (𝓒(↧(ComplexPoint X); ℤ))).hom) ≫
        D.map (Localization.isoOfHom DerivedCategory.Q
          (analyticQuasiIsomorphisms X) E.coneToInteger
          (by change QuasiIso _; exact E.quasiIso_coneToInteger)).inv ≫
        D.map (DerivedCategory.Q.map (E.relativeConeMap Ω ℓΩ hℓΩ)) ≫
        D.map ((SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
          DerivedCategory.Q) cmp.hom) ≫
        D.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
        F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) =
      (D.map (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv) ≫
        D.map (DerivedCategory.Q.map
          (analyticSheafComplexIntIsoSingle X
            (𝓒(↧(ComplexPoint X); ℤ))).hom) ≫
        D.map (Localization.isoOfHom DerivedCategory.Q
          (analyticQuasiIsomorphisms X) E.coneToInteger
          (by change QuasiIso _; exact E.quasiIso_coneToInteger)).inv ≫
        F.mapDerivedCategoryFactors.hom.app E.inclusionCone) ≫
        (F.mapDerivedCategoryFactors.inv.app E.inclusionCone ≫
          D.map (DerivedCategory.Q.map (E.relativeConeMap Ω ℓΩ hℓΩ)) ≫
          F.mapDerivedCategoryFactors.hom.app (relativeUnitCone X d Ω) ≫
          F.mapDerivedCategoryFactors.inv.app (relativeUnitCone X d Ω) ≫
          D.map ((SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
            DerivedCategory.Q) cmp.hom) ≫
          D.map ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
          F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧)) := by
    simp only [Category.assoc,
      F.mapDerivedCategoryFactors.hom_inv_id_app_assoc]
  simp only [Category.assoc] at hfactor ⊢
  refine hfactor.trans ?_
  rw [reassoc_of% hinv]
  rw [reassoc_of% hR]
  simp only [F.mapDerivedCategoryFactors.inv_hom_id_app_assoc]
  simp only [Functor.map_comp] at hchain
  rw [reassoc_of% hchain]
  rw [htail]
  rw [reassoc_of% hconst]
  simp only [F, H, b, βΩ, Functor.map_comp]

end AlgebraicGeometry.ComplexPoint
