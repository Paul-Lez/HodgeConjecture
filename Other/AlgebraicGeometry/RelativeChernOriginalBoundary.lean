/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalFrameFactorisation

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (E : HolomorphicUnitExtension X d)
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (ℓΩ : E.middle.obj.obj (op Ω))
  (hℓΩ : E.projection.hom.app (op Ω) ℓΩ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

include hℓU in
lemma restrictedConeSection_comp_relativeConeMap_eq_overlapUnitHom
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω)))
    (hw : E.inclusion.hom.app (op (U ⊓ Ω)) w =
      E.middle.obj.map (homOfLE (inf_le_right : U ⊓ Ω ≤ Ω)).op ℓΩ -
      E.middle.obj.map (homOfLE (inf_le_left : U ⊓ Ω ≤ U)).op ℓU) :
    restrictedConeSection X d E U ℓU ≫
        ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map
          (E.relativeConeMap Ω ℓΩ hℓΩ) =
      ((HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).hom.app
          (𝓒(↧(ComplexPoint X); ℤ))) ≫
      ((CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
        (restrictedOverlapUnitHom X d Ω U (-w))) ≫
      ((HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).inv.app
        ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) ≫
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr
          ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))) := by
  dsimp only
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  have hbase := restrictedConeSection_comp_relativeConeMap X d E U ℓU Ω ℓΩ hℓΩ
  dsimp only at hbase ⊢
  rw [hbase]
  have hn := I.inv.naturality (E.restrictionFactorisation Ω ℓΩ hℓΩ)
  dsimp at hn
  have hn' := hn
  change (J.map (F.map (E.restrictionFactorisation Ω ℓΩ hℓΩ)) ≫
      I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d))) =
    I.inv.app E.middle ≫ H.map ((analyticSingleFunctor X).map
      (E.restrictionFactorisation Ω ℓΩ hℓΩ)) at hn'
  have hp := congrArg (fun q =>
    I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
      J.map (E.restrictedSection U ℓU) ≫ q ≫
      H.map (CochainComplex.mappingCone.inr
        ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))))) hn'.symm
  have hold :
      I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
          J.map (E.restrictedSection U ℓU) ≫ I.inv.app E.middle ≫
            H.map ((analyticSingleFunctor X).map
              (E.restrictionFactorisation Ω ℓΩ hℓΩ)) ≫
              H.map (CochainComplex.mappingCone.inr
                ((analyticSingleFunctor X).map
                  (restrictionUnit Ω (holomorphicUnitSheaf X d)))) =
        I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
          J.map (E.restrictedSection U ℓU) ≫
            (J.map (F.map (E.restrictionFactorisation Ω ℓΩ hℓΩ)) ≫
              I.inv.app ((openRestrictionFunctor Ω).obj
                (holomorphicUnitSheaf X d))) ≫
            H.map (CochainComplex.mappingCone.inr
              ((analyticSingleFunctor X).map
                (restrictionUnit Ω (holomorphicUnitSheaf X d)))) := by
    simpa only [Category.assoc] using hp
  have hj := J.map_comp (E.restrictedSection U ℓU)
    (F.map (E.restrictionFactorisation Ω ℓΩ hℓΩ))
  have hj' := congrArg (fun q =>
    I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ q ≫
      I.inv.app ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) ≫
      H.map (CochainComplex.mappingCone.inr
        ((analyticSingleFunctor X).map
          (restrictionUnit Ω (holomorphicUnitSheaf X d))))) hj
  calc
    _ = _ := hold
    _ = I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
        J.map (restrictedOverlapUnitHom X d Ω U (-w)) ≫
          I.inv.app ((openRestrictionFunctor Ω).obj
            (holomorphicUnitSheaf X d)) ≫
          H.map (CochainComplex.mappingCone.inr
            ((analyticSingleFunctor X).map
              (restrictionUnit Ω (holomorphicUnitSheaf X d)))) := by
      rw [← restrictedFrameFactorisation_eq_overlapUnitHom X d E Ω U ℓU ℓΩ hℓΩ hℓU w hw]
      simpa only [restrictedFrameFactorisation, Category.assoc] using hj'.symm

end AlgebraicGeometry.ComplexPoint
