/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernFrameRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance originalRestrictionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)
  (U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

/-- The map from the restricted constant complex into the restricted inclusion cone induced by a
local lift of `1`.  The mapping-cone isomorphism is retained explicitly because restriction does
not commute definitionally with the cone construction. -/
def restrictedConeSection :
    ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).obj
        ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) ⟶
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).obj E.inclusionCone :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).hom.app
      (𝓒(↧(ComplexPoint X); ℤ)) ≫
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
      (E.restrictedSection U ℓU) ≫
  (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).inv.app
      E.middle ≫
    CochainComplex.mappingCone.inr
      (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map E.singleShortComplex.f) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f
      (restrictToOpen X U)).inv

include hℓU in
lemma restrictedConeSection_comp_coneToInteger :
    restrictedConeSection X d E U ℓU ≫
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map E.coneToInteger =
      𝟙 _ := by
  unfold restrictedConeSection
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let C := CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f F
  let D := CochainComplex.mappingCone.descShortComplex (E.singleShortComplex.map H)
  have hCD : C.hom ≫ D = H.map E.coneToInteger := by
    exact CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex
      (F := F) E.singleShortComplex
  have hcone : C.inv ≫ H.map E.coneToInteger = D := by
    rw [← hCD, Iso.inv_hom_id_assoc]
  have hD : CochainComplex.mappingCone.inr (H.map E.singleShortComplex.f) ≫ D =
      H.map E.singleShortComplex.g := by
    exact CochainComplex.mappingCone.inr_descShortComplex (E.singleShortComplex.map H)
  change I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
        (E.restrictedSection U ℓU) ≫
      I.inv.app E.middle ≫ CochainComplex.mappingCone.inr (H.map E.singleShortComplex.f) ≫
      C.inv ≫ H.map E.coneToInteger = 𝟙 _
  rw [hcone]
  rw [hD]
  have hnat := I.inv.naturality E.projection
  have hproj : I.inv.app E.middle ≫ H.map E.singleShortComplex.g =
      (F ⋙ HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
        (.up ℤ) 0).map E.projection ≫ I.inv.app (𝓒(↧(ComplexPoint X); ℤ)) := by
    exact hnat.symm
  have hsingle :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (F.map E.projection) =
        (F ⋙ HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map E.projection := by
    rfl
  rw [hproj, ← hsingle]
  simp only [Functor.comp_obj]
  have hj :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (E.restrictedSection U ℓU) =
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (E.restrictedSection U ℓU) := by
    rfl
  rw [hj]
  have hj2 :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (F.map E.projection) =
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (F.map E.projection) := by
    rfl
  rw [hj2]
  have hmap2 := (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
    (.up ℤ) 0).map_comp (E.restrictedSection U ℓU) (F.map E.projection)
  have hmap2' := congrArg (fun k ↦
      I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ k ≫
        I.inv.app (𝓒(↧(ComplexPoint X); ℤ))) hmap2
  calc
    _ = I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (E.restrictedSection U ℓU ≫ F.map E.projection) ≫
          I.inv.app (𝓒(↧(ComplexPoint X); ℤ)) := by
      simpa only [Category.assoc] using hmap2'.symm
    _ = _ := by
      rw [E.restrictedSection_comp_projection U ℓU hℓU]
      rw [CategoryTheory.Functor.map_id]
      exact (congrArg
        (fun f ↦ I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ f)
        (Category.id_comp (I.inv.app (𝓒(↧(ComplexPoint X); ℤ))))).trans
        (I.hom_inv_id_app (𝓒(↧(ComplexPoint X); ℤ)))

end AlgebraicGeometry.ComplexPoint
