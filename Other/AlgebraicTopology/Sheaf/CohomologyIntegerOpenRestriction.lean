/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CocycleGlobalSections
public import Other.AlgebraicTopology.Sheaf.CohomologySectionRestriction
public import Other.AlgebraicTopology.Sheaf.CohomologyOpenRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace TopCat.Sheaf

/-- The canonical integer section restricts to the canonical integer section on an open. -/
lemma constantToOpen_integerOne (Y : TopCat.{0}) (U : Opens Y) :
    (constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)).hom.app
        (op (⊤ : Opens (TopCat.of U))) (integerOne (Y := TopCat.of U)) =
      (integerConstantSheaf Y).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op
        (integerOne (Y := Y)) := by
  have h := congrArg (fun f => f.app (op (⊤ : Opens (TopCat.of U))))
    (toSheafify_constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ))
  have h' := congrArg (fun f => f (1 : ℤ)) h
  change (constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)).hom.app
      (op (⊤ : Opens (TopCat.of U)))
      ((toSheafify (Opens.grothendieckTopology (TopCat.of U))
        (integerConstantPresheaf (TopCat.of U))).app
        (op (⊤ : Opens (TopCat.of U))) (1 : ℤ)) = _ at h'
  change (constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)).hom.app
      (op (⊤ : Opens (TopCat.of U)))
      ((toSheafify (Opens.grothendieckTopology (TopCat.of U))
        (integerConstantPresheaf (TopCat.of U))).app
        (op (⊤ : Opens (TopCat.of U))) (1 : ℤ)) =
    (toSheafify (Opens.grothendieckTopology Y)
      (integerConstantPresheaf Y)).app
      (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))) (1 : ℤ) at h'
  have hkey :
      (sheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y)).map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op
          (integerOne (Y := Y)) =
        (toSheafify (Opens.grothendieckTopology Y)
          (integerConstantPresheaf Y)).app
          (op (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)))) (1 : ℤ) := by
    rw [integerOne, ← CategoryTheory.comp_apply]
    rw [← (toSheafify (Opens.grothendieckTopology Y)
      (integerConstantPresheaf Y)).naturality
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op]
    rfl
  exact (h'.trans hkey.symm)

/-- Restriction of the canonical global integer H⁰ input is the canonical local input. -/
lemma integerConstant_h0_restriction
    (Y : TopCat.{0}) (U : Opens Y) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let H := F.mapHomologicalComplex (.up ℤ)
    let S := integerConstantSingleComplex Y
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let J := CochainComplex.singleFunctor (Sheaf AddCommGrpCat (TopCat.of U)) 0
    let A : CochainComplex (Sheaf AddCommGrpCat (TopCat.of U)) ℤ := H.obj S
    let q : integerConstantSingleComplex (TopCat.of U) ⟶ A :=
      J.map (constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)) ≫
      I.inv.app ((constantFunctor Y).obj (AddCommGrpCat.of ℤ))
    let a₀Y := (globalSectionsComplexInt Y S).homologyπ 0
      (integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S)))
    let aLocal := (globalSectionsComplexInt (TopCat.of U) A).homologyπ 0
      (integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q))
    (((S.sc 0).mapHomologyIso F).inv.hom.app (op ⊤))
        ((S.homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op
          (sectionCohomologyToSheafSection Y S 0 ⊤ a₀Y)) =
      sectionCohomologyToSheafSection (TopCat.of U) A 0 ⊤ aLocal := by
  dsimp only
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let H := F.mapHomologicalComplex (.up ℤ)
  let S := integerConstantSingleComplex Y
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (Sheaf AddCommGrpCat (TopCat.of U)) 0
  let A : CochainComplex (Sheaf AddCommGrpCat (TopCat.of U)) ℤ := H.obj S
  let q : integerConstantSingleComplex (TopCat.of U) ⟶ A :=
    J.map (constantToOpenSheafRestriction Y U (AddCommGrpCat.of ℤ)) ≫
    I.inv.app ((constantFunctor Y).obj (AddCommGrpCat.of ℤ))
  have hopen := sectionCohomologyToSheafSection_openRestriction Y U S 0 ⊤
  let e := (S.sc 0).mapHomologyIso F
  have hleft := ConcreteCategory.congr_hom hopen
    ((globalSectionsComplexInt (TopCat.of U) A).homologyπ 0
      (integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q)))
  change (ConcreteCategory.hom (e.hom.hom.app (op (⊤ : Opens (TopCat.of U)))))
      ((ConcreteCategory.hom (sectionCohomologyToSheafSection (TopCat.of U) A 0 ⊤))
        ((globalSectionsComplexInt (TopCat.of U) A).homologyπ 0
          (integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q)))) = _ at hleft
  have hcycles :
      integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q) =
        cyclesMap (sectionComplexRestriction Y (.up ℤ) S
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) 0
          (integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S))) := by
    apply (AddCommGrpCat.mono_iff_injective
      ((globalSectionsComplexInt (TopCat.of U) A).iCycles 0)).mp inferInstance
    have hcy := ConcreteCategory.congr_hom
      (cyclesMap_i (sectionComplexRestriction Y (.up ℤ) S
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) 0)
      (integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S)))
    simp only [ConcreteCategory.comp_apply] at hcy
    exact (iCycles_integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q)).trans
      ((constantToOpen_integerOne Y U).trans
        ((congrArg (fun x =>
          (sectionComplexRestriction Y (.up ℤ) S
            (homOfLE (le_top : U.isOpenEmbedding.functor.obj
              (⊤ : Opens (TopCat.of U)) ≤ ⊤))).f 0 x)
          (iCycles_integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S)))).symm.trans
          hcy.symm))
  have hclass :
      (globalSectionsComplexInt (TopCat.of U) A).homologyπ 0
          (integerCocycleGlobalSection (TopCat.of U) A 0 (Cocycle.ofHom q)) =
        homologyMap (sectionComplexRestriction Y (.up ℤ) S
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) 0
          ((globalSectionsComplexInt Y S).homologyπ 0
            (integerCocycleGlobalSection Y S 0
              (Cocycle.ofHom (𝟙 S)))) := by
    rw [hcycles]
    exact (ConcreteCategory.congr_hom
      (homologyπ_naturality (sectionComplexRestriction Y (.up ℤ) S
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) 0)
      (integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S)))).symm
  let aY := (globalSectionsComplexInt Y S).homologyπ 0
    (integerCocycleGlobalSection Y S 0 (Cocycle.ofHom (𝟙 S)))
  let bY := (S.homology 0).obj.map
    (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤)).op
    (sectionCohomologyToSheafSection Y S 0 ⊤ aY)
  have hrestriction := ConcreteCategory.congr_hom
    (sectionCohomologyToSheafSection_restriction Y S 0
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U)) ≤ ⊤))) aY
  simp only [ConcreteCategory.comp_apply] at hrestriction
  have hleft' := hleft.trans (congrArg (fun a =>
    sectionCohomologyToSheafSection Y S 0
      (U.isOpenEmbedding.functor.obj (⊤ : Opens (TopCat.of U))) a) hclass)
  apply ((ConcreteCategory.isIso_iff_bijective
    (e.hom.hom.app (op (⊤ : Opens (TopCat.of U))))).mp inferInstance).1
  have he : e.inv.hom.app (op (⊤ : Opens (TopCat.of U))) ≫
      e.hom.hom.app (op (⊤ : Opens (TopCat.of U))) = 𝟙 _ := by
    have he := congrArg (fun f => f.hom.app (op (⊤ : Opens (TopCat.of U)))) e.inv_hom_id
    rw [ObjectProperty.FullSubcategory.comp_hom] at he
    exact he
  exact (ConcreteCategory.congr_hom he bY).trans (hrestriction.symm.trans hleft'.symm)

end TopCat.Sheaf
