/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingSection
public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeSectionTransport
public import Other.AlgebraicTopology.Sheaf.CohomologyOpenRestriction
public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftOpenOne

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

local instance originalChernAmbientSectionShiftTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance originalChernAmbientSectionShiftDerived (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))

/-- The original ambient degree-one boundary section is the open-restricted shift. -/
lemma originalLocalBoundaryMap_ambient_section_eq_restricted_shift
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    let Y := TopCat.of (ComplexPoint X)
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
    let localT :=
      (TopCat.Sheaf.sectionCohomologySheafShiftMap (TopCat.of U) B 1 0 1 (by omega)).hom.app
        (op (⊤ : Opens (TopCat.of U)))
        (((((S.sc 0).mapHomologyIso F).inv ≫
          HomologicalComplex.homologyMap
            (originalLocalBoundaryMap X d Ω U w ≫ (H.commShiftIso (1 : ℤ)).hom.app C) 0).hom.app
          (op (⊤ : Opens (TopCat.of U))))
          (((S.homology 0).obj.map
            (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
            (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀)))
    ambient =
      ((C.sc 1).mapHomologyIso F).hom.hom.app (op (⊤ : Opens (TopCat.of U))) localT := by
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
  let a₀Y := (TopCat.Sheaf.globalSectionsComplexInt Y S).homologyπ 0
    (TopCat.Sheaf.integerCocycleGlobalSection Y S 0
      (CochainComplex.HomComplex.Cocycle.ofHom (𝟙 S)))
  let aLocal := (TopCat.Sheaf.globalSectionsComplexInt YU (H.obj S)).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection YU (H.obj S) 0
      (CochainComplex.HomComplex.Cocycle.ofHom (
        (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat YU) 0).map
          (TopCat.Sheaf.constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)) ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app
          ((TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of ℤ)))))
  let g0 := originalLocalBoundaryMap X d Ω U w
  let x := HomologicalComplex.homologyMap
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor YU).mapHomologicalComplex
      (.up ℤ) |>.map (g0)) 0 aLocal
  have hsource := TopCat.Sheaf.integerConstant_h0_restriction Y U
  dsimp only at hsource
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality YU g0 0 ⊤) aLocal
  simp only [ConcreteCategory.comp_apply] at hnat
  have hb :
      (((((S.sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap g0 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app
        (op (⊤ : Opens (TopCat.of U))))
        (((S.homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj
            (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀Y))) =
      TopCat.Sheaf.sectionCohomologyToSheafSection Y (C⟦(1 : ℤ)⟧) 0
        (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))) x := by
    have hs := hsource
    have hs' := congrArg
      (fun z =>
        ((((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom.hom.app
          (op (⊤ : Opens (TopCat.of U))))
          ((HomologicalComplex.homologyMap g0 0).hom.app
            (op (⊤ : Opens (TopCat.of U))) z)) hs
    dsimp only [aLocal, x, g0] at hs' hnat ⊢
    simp only at hs' hnat ⊢
    have hlocal := hs'.trans (congrArg
      (fun z =>
        ((((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom.hom.app
          (op (⊤ : Opens (TopCat.of U)))) z) hnat.symm)
    have hopen := ConcreteCategory.congr_hom
      (TopCat.Sheaf.sectionCohomologyToSheafSection_openRestriction Y U (C⟦(1 : ℤ)⟧) 0 ⊤) x
    simp only [ConcreteCategory.comp_apply] at hlocal hopen
    exact hlocal.trans hopen
  have hshift := TopCat.Sheaf.sectionCohomologyToSheafSection_shift_openRestriction_one
    Y U C ⊤ x
  dsimp only [H, B] at hshift
  rw [hb]
  let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor YU).mapHomologicalComplex
    (.up ℤ)
  let gshift := g0 ≫ (H.commShiftIso (1 : ℤ)).hom.app C
  have hxmap :
      (HomologicalComplex.homologyMap
        (Γ.map ((H.commShiftIso (1 : ℤ)).hom.app C)) 0) x =
        (HomologicalComplex.homologyMap (Γ.map gshift) 0) aLocal := by
    let k := (H.commShiftIso (1 : ℤ)).hom.app C
    change (HomologicalComplex.homologyMap (Γ.map k) 0)
        ((HomologicalComplex.homologyMap (Γ.map g0) 0) aLocal) =
      (HomologicalComplex.homologyMap (Γ.map (g0 ≫ k)) 0) aLocal
    have hm : HomologicalComplex.homologyMap (Γ.map (g0 ≫ k)) 0 =
        HomologicalComplex.homologyMap (Γ.map g0) 0 ≫
          HomologicalComplex.homologyMap (Γ.map k) 0 :=
      (congrArg (fun f => HomologicalComplex.homologyMap f 0) (Γ.map_comp g0 k)).trans
        (HomologicalComplex.homologyMap_comp (Γ.map g0) (Γ.map k) 0)
    exact (ConcreteCategory.congr_hom hm aLocal).symm
  have hnat2 := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality YU gshift 0 ⊤) aLocal
  simp only [ConcreteCategory.comp_apply] at hnat2
  have hsmap := congrArg
    (fun z => (HomologicalComplex.homologyMap gshift 0).hom.app (op ⊤) z) hsource
  simp only at hsmap
  have hinner0 :
      (((((S.sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gshift 0).hom.app (op (⊤ : Opens (TopCat.of U))))
        (((S.homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj
            (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀Y))) =
      TopCat.Sheaf.sectionCohomologyToSheafSection YU ((H.obj C)⟦(1 : ℤ)⟧) 0 ⊤
        ((HomologicalComplex.homologyMap (Γ.map gshift) 0) aLocal) := by
    dsimp only [gshift] at hnat2 hsmap ⊢
    simp only at hsmap ⊢
    exact hsmap.trans hnat2.symm
  have hinner :
      TopCat.Sheaf.sectionCohomologyToSheafSection YU ((H.obj C)⟦(1 : ℤ)⟧) 0 ⊤
          ((HomologicalComplex.homologyMap
            (Γ.map ((H.commShiftIso (1 : ℤ)).hom.app C)) 0) x) =
        (((((S.sc 0).mapHomologyIso F).inv ≫
          HomologicalComplex.homologyMap gshift 0).hom.app (op (⊤ : Opens (TopCat.of U))))
          (((S.homology 0).obj.map
            (homOfLE (le_top : U.isOpenEmbedding.functor.obj
              (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op)
            (TopCat.Sheaf.sectionCohomologyToSheafSection Y S 0 ⊤ a₀Y))) := by
    have hi := congrArg
      (fun z => TopCat.Sheaf.sectionCohomologyToSheafSection YU
        ((H.obj C)⟦(1 : ℤ)⟧) 0 ⊤ z) hxmap
    exact hi.trans hinner0.symm
  exact hshift.trans (congrArg (fun z =>
    (((C.sc 1).mapHomologyIso F).hom.hom.app (op (⊤ : Opens (TopCat.of U))))
      (((TopCat.Sheaf.sectionCohomologySheafShiftMap YU B 1 0 1 (by omega)).hom.app
        (op (⊤ : Opens (TopCat.of U)))) z)) hinner)

end AlgebraicGeometry.ComplexPoint
