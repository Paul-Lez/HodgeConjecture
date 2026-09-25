/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportAmbientSectionDerivedSquare
public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWinding
public import Other.AlgebraicGeometry.RelativeChernOriginalDerivedBoundarySquare

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CategoryTheory.Localization
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint
local instance originalAmbientBoundaryTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance originalAmbientBoundaryDerived (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

lemma supportAmbientDerivedSquare_of_rationalLocalSquare
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)
    (α : RationalCohomologyWithSupport X Z 2)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (g : ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ⟶
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          ((rationalCohomologyWithSupportComplex X Z)⟦(1 : ℤ)⟧))
    (gU : ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ⟶
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj
          ((CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))⟦(1 : ℤ)⟧))
    (hlocal :
      let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
      let Cr := rationalCohomologyWithSupportComplex X Z
      let D := F.mapDerivedCategory
      D.map
          (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
            hypercohomologyAddEquivDerived X Cr 1 α ≫
            (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app Cr) ≫
        F.mapDerivedCategoryFactors.hom.app (Cr⟦(1 : ℤ)⟧) =
      F.mapDerivedCategoryFactors.hom.app
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ≫
        DerivedCategory.Q.map g)
    (hgU :
      g ≫ ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).map
        ((shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) 1).map
          (rationalSupportConeToAmbientInjectiveCone X Z hZ)) = gU) :
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
          (TopCat.Sheaf.integerConstantSingleComplex Y) ≫ DerivedCategory.Q.map gU := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let Cr := rationalCohomologyWithSupportComplex X Z
  let Ca := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let R := rationalSupportConeToAmbientInjectiveCone X Z hZ
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let D := F.mapDerivedCategory
  let H := F.mapHomologicalComplex (.up ℤ)
  let x := (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y Ca 1).symm
    (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ 2 α)
  have htop := supportAmbientDerivedClass_topDerivedHom X Z hZ 2 α
  dsimp only at htop
  have hnat := hypercohomologyAddEquivDerived_naturality X R 1 α
  have hshift := Functor.commShiftIso_inv_naturality DerivedCategory.Q R (1 : ℤ)
  have hpre :
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
          hypercohomologyAddEquivDerived X Ca 1 (hypercohomologyMap X R 1 α) ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app Ca =
        DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
          hypercohomologyAddEquivDerived X Cr 1 α ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app Cr ≫
          DerivedCategory.Q.map ((shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) 1).map R) := by
    rw [hnat]
    simp only [Category.assoc]
    rw [hshift]
  let Rshift := (shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) (1 : ℤ)).map R
  have hfac := F.mapDerivedCategoryFactors_hom_naturality Rshift
  have htop1 :
      (TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y Ca 1).symm
          (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ 2 α) =
        DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
          hypercohomologyAddEquivDerived X Ca 1 (hypercohomologyMap X R 1 α) := by
    exact htop
  rw [htop1]
  dsimp only [Cr, Ca, R, F, D, H] at hpre hfac hlocal hgU ⊢
  simp only [Category.assoc]
  rw [hpre]
  simp only [Functor.map_comp, Category.assoc]
  rw [hfac]
  simp only [Functor.map_comp, Category.assoc] at hlocal
  rw [reassoc_of% hlocal]
  rw [← DerivedCategory.Q.map_comp, hgU]

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

include ℓU hℓU hw in
/-- The original Chern class restricts to the actual local boundary in the ambient cone. -/
theorem restrict_original_relativeChernClass_ambient_derived_boundary :
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z
      Ω.isOpen.isClosed_compl)
    let F := restrictToOpen X U
    let α := E.relativeChernClass Ω ℓΩ hℓΩ cmp
    let gU := originalLocalBoundaryMap X d Ω U w
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z
      Ω.isOpen.isClosed_compl 2
    let eTop := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective
      (TopCat.of (ComplexPoint X)) C 1
    let x := eTop.symm (e α)
    F.mapDerivedCategory.map (x ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app C) ≫
        F.mapDerivedCategoryFactors.hom.app (C⟦(1 : ℤ)⟧) =
      F.mapDerivedCategoryFactors.hom.app
          (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) ≫
        DerivedCategory.Q.map gU := by
  dsimp only
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z
    Ω.isOpen.isClosed_compl)
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  let α := E.relativeChernClass Ω ℓΩ hℓΩ cmp
  let βΩ := CochainComplex.HomComplex.Cocycle.equivHomShift.symm
    (restrictedSingularOneCocycle X d Ω)
  let g := I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
    J.map (restrictedOverlapUnitHom X d Ω U (-w)) ≫
    I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) ≫
    H.map (βΩ ≫
      (CochainComplex.mappingCone.inr
        (rationalRestrictionComplexInt X Z))⟦(1 : ℤ)⟧')
  let gU := originalLocalBoundaryMap X d Ω U w
  have hlocal := restrict_original_relativeChernClass_derived_boundary
    X d E Ω U ℓU ℓΩ hℓΩ hℓU cmp w hw
  have hgU : g ≫ H.map
      ((shiftFunctor (CochainComplex (AnalyticAdditiveSheaf X) ℤ) 1).map
        (rationalSupportConeToAmbientInjectiveCone X Z Ω.isOpen.isClosed_compl)) = gU := by
    dsimp [g, gU, βΩ, Z]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  exact supportAmbientDerivedSquare_of_rationalLocalSquare
    X Z Ω.isOpen.isClosed_compl α U g gU hlocal hgU

include ℓU hℓU hw in
/-- The original ambient section is the shifted cohomology image of the actual local boundary. -/
theorem restrict_original_relativeChernClass_ambient_section
    (W : Opens (TopCat.of U)) :
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z
      Ω.isOpen.isClosed_compl)
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z
      Ω.isOpen.isClosed_compl 2
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let α := E.relativeChernClass Ω ℓΩ hℓΩ cmp
    let gU := originalLocalBoundaryMap X d Ω U w
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0
        (Cocycle.ofHom (𝟙 (TopCat.Sheaf.integerConstantSingleComplex
          (TopCat.of (ComplexPoint X))))))
    let t :=
      ((((TopCat.Sheaf.integerConstantSingleComplex
          (TopCat.of (ComplexPoint X))).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app (op W)
        (((TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))).homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
          (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0 ⊤ a₀))
    (C.homology 1).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X)) C 1 ⊤ (e α)) =
      (TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of (ComplexPoint X)) C 1 0 1
        (by omega)).hom.app
        (op (U.isOpenEmbedding.functor.obj W)) t := by
  dsimp only
  apply supportAmbientSection_restrict_eq_of_derived_square
    X ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl
    (E.relativeChernClass Ω ℓΩ hℓΩ cmp) U (originalLocalBoundaryMap X d Ω U w)
  exact restrict_original_relativeChernClass_ambient_derived_boundary
    X d E Ω U ℓU ℓΩ hℓΩ hℓU cmp w hw

end AlgebraicGeometry.ComplexPoint
