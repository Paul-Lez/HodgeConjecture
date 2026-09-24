/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernAmbientSectionShift
public import Other.AlgebraicTopology.Sheaf.CohomologyOpenRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalChernAmbientRawSectionTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance originalChernAmbientRawSectionDerived (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- The actual ambient boundary section is the ambient image of the raw winding class. -/
lemma originalLocalBoundaryMap_ambient_section_eq_raw_winding
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let C := CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z Ω.isOpen.isClosed_compl)
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let S := TopCat.Sheaf.integerConstantSingleComplex Y
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection Y S 0
        (CochainComplex.HomComplex.Cocycle.ofHom (𝟙 S)))
    let f :=
      (((S.sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap (originalLocalBoundaryMap X d Ω U w) 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app
        (op (⊤ : Opens (TopCat.of U)))
    let b := f
      (((S.homology 0).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀))
    let ambient :=
      (TopCat.Sheaf.sectionCohomologySheafShiftMap Y C 1 0 1 (by omega)).hom.app
        (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))) b
    let r := originalLocalRawToAmbientCone X Ω U
    let zraw := ChernWinding.openRawRationalWindingClass Y (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
    ambient = TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1
      (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))
      (HomologicalComplex.homologyMap r 1 zraw) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let C := CochainComplex.mappingCone
    (ambientRationalInjectiveRestriction X Z Ω.isOpen.isClosed_compl)
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let r := originalLocalRawToAmbientCone X Ω U
  let zraw := ChernWinding.openRawRationalWindingClass Y (U ⊓ Ω)
    (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
  have hshift := originalLocalBoundaryMap_ambient_section_eq_restricted_shift X d Ω U w
  dsimp only at hshift
  let e := ((C.sc 1).mapHomologyIso F).hom.hom.app (op (⊤ : Opens (TopCat.of U)))
  have hraw := congrArg e (originalLocalBoundaryMap_section_eq_raw_winding X d Ω U w)
  dsimp only at hraw
  have hopen := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_openRestriction Y U C 1 ⊤)
    (HomologicalComplex.homologyMap r 1 zraw)
  simp only [ConcreteCategory.comp_apply] at hopen
  exact hshift.trans (hraw.trans hopen)

end AlgebraicGeometry.ComplexPoint
