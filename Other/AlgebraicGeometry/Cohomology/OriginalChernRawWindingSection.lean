/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingClassMap
public import Other.AlgebraicTopology.Sheaf.CohomologyIntegerOpenRestriction
public import Other.AlgebraicTopology.Sheaf.CohomologySectionDerivedTransport

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalChernRawSectionTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance originalChernRawSectionDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- The original boundary section on the restricted space is the raw winding class. -/
lemma originalLocalBoundaryMap_section_eq_raw_winding
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
    let YU := TopCat.of U
    let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
    let C := CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z Ω.isOpen.isClosed_compl)
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let B := H.obj C
    let S := TopCat.Sheaf.integerConstantSingleComplex Y
    let a₀ := (TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection Y S 0
        (CochainComplex.HomComplex.Cocycle.ofHom (𝟙 S)))
    let t := (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
      (op (⊤ : Opens (TopCat.of U)))
      (((((S.sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap
            (originalLocalBoundaryMap X d Ω U w ≫ (H.commShiftIso (1 : ℤ)).hom.app C) 0).hom.app
        (op (⊤ : Opens (TopCat.of U))))
        (((S.homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀)))
    let r := originalLocalRawToAmbientCone X Ω U
    let zraw := ChernWinding.openRawRationalWindingClass Y (U ⊓ Ω)
      (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
      (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
    t = TopCat.Sheaf.sectionCohomologyToSheafSection YU B 1 ⊤
      (HomologicalComplex.homologyMap r 1 zraw) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let YU := TopCat.of U
  let Z : Set (ComplexPoint X) := (Ω : Set (ComplexPoint X))ᶜ
  let C := CochainComplex.mappingCone
    (ambientRationalInjectiveRestriction X Z Ω.isOpen.isClosed_compl)
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let B := H.obj C
  let S := TopCat.Sheaf.integerConstantSingleComplex Y
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat YU) 0
  let q : TopCat.Sheaf.integerConstantSingleComplex YU ⟶ H.obj
      ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) :=
    J.map (TopCat.Sheaf.constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)) ≫
      I.inv.app ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ))
  let gshift := originalLocalBoundaryMap X d Ω U w ≫
    (H.commShiftIso (1 : ℤ)).hom.app C
  let c := q ≫ gshift
  have hsource := TopCat.Sheaf.integerConstant_h0_restriction Y U
  dsimp only at hsource
  let aLocal := (TopCat.Sheaf.globalSectionsComplexInt YU (H.obj S)).homologyπ 0
    (TopCat.Sheaf.integerCocycleGlobalSection YU (H.obj S) 0
      (CochainComplex.HomComplex.Cocycle.ofHom q))
  let aC := (TopCat.Sheaf.globalSectionsComplexInt YU (B⟦(1 : ℤ)⟧)).homologyπ 0
    (TopCat.Sheaf.integerCocycleGlobalSection YU (B⟦(1 : ℤ)⟧) 0
      (CochainComplex.HomComplex.Cocycle.ofHom c))
  let s := TopCat.Sheaf.globalSectionsShiftShortComplex YU B 1 0 1 (by omega)
  let r := originalLocalRawToAmbientCone X Ω U
  let zraw := ChernWinding.openRawRationalWindingClass Y (U ⊓ Ω)
    (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
  let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor YU).mapHomologicalComplex
    (.up ℤ)
  have hpost : aC = HomologicalComplex.homologyMap (Γ.map gshift) 0 aLocal := by
    have he : (CochainComplex.HomComplex.Cocycle.ofHom q).postcomp gshift =
        CochainComplex.HomComplex.Cocycle.ofHom c := by
      apply Subtype.ext
      simpa only [CochainComplex.HomComplex.Cocycle.postcomp_coe,
        CochainComplex.HomComplex.Cocycle.ofHom_coe, c] using
        (CochainComplex.HomComplex.Cochain.ofHom_comp q gshift).symm
    have h := TopCat.Sheaf.homologyπ_integerCocycleGlobalSection_postcomp
      YU gshift 0 (CochainComplex.HomComplex.Cocycle.ofHom q)
    rw [he] at h
    exact h
  have hsource' := hsource
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality YU gshift 0 ⊤) aLocal
  simp only [ConcreteCategory.comp_apply] at hnat
  have hinner :
      (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
        (op (⊤ : Opens (TopCat.of U)))
        (((((S.sc 0).mapHomologyIso F).inv ≫
          HomologicalComplex.homologyMap gshift 0).hom.app (op ⊤))
          (((S.homology 0).obj.map
            (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
            (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤
              ((TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 0
                (TopCat.Sheaf.integerCocycleGlobalSection Y S 0
                  (CochainComplex.HomComplex.Cocycle.ofHom (𝟙 S))))))) =
        (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
          (op (⊤ : Opens (TopCat.of U)))
          (TopCat.Sheaf.sectionCohomologyToSheafSection YU (B⟦(1 : ℤ)⟧) 0 ⊤ aC) := by
    dsimp only at hsource' hnat ⊢
    have hpost' := congrArg
      (fun y => TopCat.Sheaf.sectionCohomologyToSheafSection YU (B⟦(1 : ℤ)⟧) 0 ⊤ y)
      hpost
    have hnat' := hnat.symm.trans hpost'.symm
    have hs :
        (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
            (op (⊤ : Opens (TopCat.of U)))
          (((HomologicalComplex.homologyMap gshift 0).hom.app (op ⊤))
            (((S.sc 0).mapHomologyIso F).inv.hom.app (op ⊤)
              (((S.homology 0).obj.map
                (homOfLE (le_top : U.isOpenEmbedding.functor.obj
                  (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
                (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤
                  ((TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 0
                    (TopCat.Sheaf.integerCocycleGlobalSection Y S 0
                      (CochainComplex.HomComplex.Cocycle.ofHom (𝟙 S)))))))) =
        (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
          (op (⊤ : Opens (TopCat.of U)))
          (((HomologicalComplex.homologyMap gshift 0).hom.app (op ⊤))
            (TopCat.Sheaf.sectionCohomologyToSheafSection YU (H.obj S) 0 ⊤ aLocal)) := by
      simpa only [ConcreteCategory.comp_apply] using congrArg (fun y =>
        (TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
          (op (⊤ : Opens (TopCat.of U)))
          ((HomologicalComplex.homologyMap gshift 0).hom.app (op ⊤) y)) hsource'
    exact hs.trans (congrArg
      ((TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
        (op (⊤ : Opens (TopCat.of U)))) hnat')
  have hshift := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_shift_naturality
      YU B 1 0 1 (by omega) ⊤) aC
  have hshiftTop := TopCat.Sheaf.sectionCohomologyPresheafShiftShortComplex_top_homology
    YU B 1 0 1 (by omega)
  rw [hshiftTop] at hshift
  simp only [ConcreteCategory.comp_apply] at hshift
  let zChern := TopCat.Sheaf.integerCocycleGlobalSection YU (B⟦(1 : ℤ)⟧) 0
    (CochainComplex.HomComplex.Cocycle.ofHom c)
  let zrawCocycle := ChernWinding.openRawRationalWindingCocycle Y (U ⊓ Ω)
    (holomorphicUnitFunction X d (U ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X d (U ⊓ Ω) (-w))
  have hs := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality s) zChern
  have hr := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality r 1) zrawCocycle
  simp only [ConcreteCategory.comp_apply] at hs hr
  have hc := originalLocalBoundaryMap_shift_cyclesMap_raw_winding X d Ω U w
  have hclass :
      ShortComplex.homologyMap s aC =
        HomologicalComplex.homologyMap r 1 zraw := by
    dsimp only [zChern, zrawCocycle] at hs hr
    rw [ChernWinding.homologyπ_openRawRationalWindingCocycle] at hr
    dsimp only at hc
    exact hs.trans ((congrArg
      ((TopCat.Sheaf.globalSectionsComplexInt YU B).homologyπ 1) hc).trans hr.symm)
  dsimp only [aC, s, r, zraw] at hshift hclass ⊢
  exact hinner.trans (hshift.symm.trans (congrArg
    (fun y => TopCat.Sheaf.sectionCohomologyToSheafSection YU B 1 ⊤ y) hclass))

end AlgebraicGeometry.ComplexPoint
