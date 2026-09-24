/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalAmbientDerivedBoundary
public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeSectionTransport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CategoryTheory.Localization

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalSupportSectionTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance originalSupportSectionDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

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
/-- The original supported section is the negative normalized image of its local boundary. -/
theorem restrict_original_relativeChernClass_support_section
    (W : Opens (TopCat.of U)) :
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z
      Ω.isOpen.isClosed_compl)
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
      (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let m := supportSheafToAmbientInjectiveCone X Z Ω.isOpen.isClosed_compl
    let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app
        (op (U.isOpenEmbedding.functor.obj W))) := by
      have : IsIso (HomologicalComplex.homologyMap m 1) :=
        (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
      infer_instance
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let gU := originalLocalBoundaryMap X d Ω U w
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X)))).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0
        (CochainComplex.HomComplex.Cocycle.ofHom
          (𝟙 (TopCat.Sheaf.integerConstantSingleComplex
            (TopCat.of (ComplexPoint X))))))
    let b :=
      ((((TopCat.Sheaf.integerConstantSingleComplex
          (TopCat.of (ComplexPoint X))).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app (op W)
        (((TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))).homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
          (TopCat.Sheaf.sectionCohomologyToSheafSection
            (TopCat.of (ComplexPoint X))
            (TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint X))) 0 ⊤ a₀))
    let t :=
      (TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of (ComplexPoint X)) C
        1 0 1 (by omega)).hom.app (op (U.isOpenEmbedding.functor.obj W)) b
    (K.homology 2).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X)) K 2 ⊤
        (coneSupportAddEquivSupportedInjectiveHomology X Z Ω.isOpen.isClosed_compl 2
          (E.relativeChernClass Ω ℓΩ hℓΩ cmp))) =
      -(TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of (ComplexPoint X)) K
        1 1 2 (by omega)).hom.app (op (U.isOpenEmbedding.functor.obj W))
        (inv ((HomologicalComplex.homologyMap m 1).hom.app
          (op (U.isOpenEmbedding.functor.obj W))) t) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let C := CochainComplex.mappingCone
    (ambientRationalInjectiveRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
      Ω.isOpen.isClosed_compl)
  let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y
    ⟨((Ω : Set (ComplexPoint X))ᶜ)ᶜ, Ω.isOpen.isClosed_compl.isOpen_compl⟩
    (ambientRationalInjectiveComplex X)).X₁
  let m := supportSheafToAmbientInjectiveCone X ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl
  let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app
      (op (U.isOpenEmbedding.functor.obj W))) := by
    have : IsIso (HomologicalComplex.homologyMap m 1) :=
      (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
    infer_instance
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let a₀ := (TopCat.Sheaf.globalSectionsComplexInt Y
      (TopCat.Sheaf.integerConstantSingleComplex Y)).homologyπ 0
    (TopCat.Sheaf.integerCocycleGlobalSection Y
      (TopCat.Sheaf.integerConstantSingleComplex Y) 0
      (CochainComplex.HomComplex.Cocycle.ofHom
        (𝟙 (TopCat.Sheaf.integerConstantSingleComplex Y))))
  let gU := originalLocalBoundaryMap X d Ω U w
  let b :=
    ((((TopCat.Sheaf.integerConstantSingleComplex Y).sc 0).mapHomologyIso F).inv ≫
      HomologicalComplex.homologyMap gU 0 ≫
        (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app (op W)
      (((TopCat.Sheaf.integerConstantSingleComplex Y).homology 0).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y
          (TopCat.Sheaf.integerConstantSingleComplex Y) 0 ⊤ a₀))
  let t :=
    (TopCat.Sheaf.sectionCohomologySheafShiftMap Y C 1 0 1 (by omega)).hom.app
      (op (U.isOpenEmbedding.functor.obj W)) b
  have ht := restrict_original_relativeChernClass_ambient_section
    X d E Ω U ℓU ℓΩ hℓΩ hℓU cmp w hw W
  dsimp only at ht
  have htransport := coneSupportSection_restrict_eq_neg_inv_shift_local_section
    X ((Ω : Set (ComplexPoint X))ᶜ) Ω.isOpen.isClosed_compl 2
    (E.relativeChernClass Ω ℓΩ hℓΩ cmp)
    (U.isOpenEmbedding.functor.obj W) t ht
  dsimp only [Y, C, K, m, b, t] at htransport ⊢
  exact htransport

end AlgebraicGeometry.ComplexPoint
