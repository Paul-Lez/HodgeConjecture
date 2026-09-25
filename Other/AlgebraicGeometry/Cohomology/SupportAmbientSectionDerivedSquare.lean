/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeLocalVanishing
public import Other.AlgebraicTopology.Sheaf.CohomologySectionDerivedTransport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CategoryTheory.Localization
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace AlgebraicGeometry.ComplexPoint

local instance supportAmbientDerivedTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance supportAmbientSheafDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _

/-- An actual derived restriction square determines the local section of the ambient class. -/
lemma supportAmbientSection_restrict_eq_of_derived_square
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)
    (α : RationalCohomologyWithSupport X Z 2)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (gU : ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ⟶
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))⟦(1 : ℤ)⟧))
    (hα :
      let Y := TopCat.of (ComplexPoint X)
      let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
      let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ 2
      let eTop := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y C 1
      let x := eTop.symm (e α)
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
          (x ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
        (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
          (C⟦(1 : ℤ)⟧) =
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
          (TopCat.Sheaf.integerConstantSingleComplex Y) ≫ DerivedCategory.Q.map gU)
    (W : Opens (TopCat.of U)) :
    let Y := TopCat.of (ComplexPoint X)
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ 2
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt Y
        (TopCat.Sheaf.integerConstantSingleComplex Y)).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection Y
        (TopCat.Sheaf.integerConstantSingleComplex Y) 0
        (Cocycle.ofHom (𝟙 (TopCat.Sheaf.integerConstantSingleComplex Y))))
    let t :=
      ((((TopCat.Sheaf.integerConstantSingleComplex Y).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app (op W)
        (((TopCat.Sheaf.integerConstantSingleComplex Y).homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y
            (TopCat.Sheaf.integerConstantSingleComplex Y) 0 ⊤ a₀))
    (C.homology 1).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 ⊤ (e α)) =
      (TopCat.Sheaf.sectionCohomologySheafShiftMap Y C 1 0 1 (by omega)).hom.app
        (op (U.isOpenEmbedding.functor.obj W))
        t := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ 2
  let eTop := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y C 1
  let x := eTop.symm (e α)
  let E := CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
    (TopCat.Sheaf.integerConstantSingleComplex Y) C 1
  obtain ⟨z, hz⟩ := (E x).mk_surjective
  have hx : eTop x = e α := by
    exact eTop.apply_symm_apply (e α)
  have hzx : x = ShiftedHom.map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
      DerivedCategory.Q := by
    apply E.injective
    rw [← hz,
      ← CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
      AddEquiv.apply_symm_apply]
  let g := CochainComplex.HomComplex.Cocycle.equivHomShift.symm z
  have hzx' : DerivedCategory.Q.map g =
      x ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C := by
    rw [hzx]
    simp only [ShiftedHom.map, Category.assoc, Iso.hom_inv_id_app]
    change DerivedCategory.Q.map g = DerivedCategory.Q.map g ≫ 𝟙 _
    exact (Category.comp_id _).symm
  have hα' := hα
  dsimp only at hα'
  rw [← hzx'] at hα'
  have hfg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
        (DerivedCategory.Q.map g) ≫
          (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
            (C⟦(1 : ℤ)⟧) =
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
          (TopCat.Sheaf.integerConstantSingleComplex Y) ≫ DerivedCategory.Q.map gU := by
    exact hα'
  have hderived := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective_cocycle
    Y C 1 z
  have hright := TopCat.Sheaf.globalSections_homology_cocycle_rightUnshift Y C 1 z
  have hclass : e α =
      ShortComplex.homologyMap
        (TopCat.Sheaf.globalSectionsShiftShortComplex Y C 1 0 1 (by omega))
        ((TopCat.Sheaf.globalSectionsComplexInt Y (C⟦(1 : ℤ)⟧)).homologyπ 0
          (TopCat.Sheaf.integerCocycleGlobalSection Y (C⟦(1 : ℤ)⟧) 0
            (Cocycle.ofHom g))) := by
    have he : eTop (ShiftedHom.map g DerivedCategory.Q) = e α := by
      rw [← hzx]
      exact hx
    dsimp only [eTop] at he
    rw [hderived] at he
    exact he.symm.trans hright
  have hmain := TopCat.Sheaf.sectionCohomology_integerCocycleGlobalSection_ofHom_derived_square
    Y U C g gU hfg W
  dsimp only at hmain
  rw [← hclass] at hmain
  exact hmain

end AlgebraicGeometry.ComplexPoint
