/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.Homology.DerivedFunctorHomology
public import Other.AlgebraicTopology.Sheaf.CohomologySectionTransport
public import Other.AlgebraicGeometry.CocycleGlobalSectionNaturality

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace TopCat.Sheaf

/-- The local section of a shifted boundary is the shifted image of its integer input. -/
lemma sectionCohomology_integerCocycleGlobalSection_ofHom_shift_onOpen
    (Y : TopCat.{0})
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    (g : integerConstantSingleComplex Y ⟶ K⟦(1 : ℤ)⟧)
    (W : Opens Y) :
    let a := (globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homologyπ 0
      (integerCocycleGlobalSection Y (K⟦(1 : ℤ)⟧) 0 (Cocycle.ofHom g))
    let b := ShortComplex.homologyMap
      (globalSectionsShiftShortComplex Y K 1 0 1 (by omega)) a
    let a₀ := (globalSectionsComplexInt Y (integerConstantSingleComplex Y)).homologyπ 0
      (integerCocycleGlobalSection Y (integerConstantSingleComplex Y) 0
        (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))))
    (K.homology 1).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (sectionCohomologyToSheafSection Y K 1 ⊤ b) =
      (sectionCohomologySheafShiftMap Y K 1 0 1 (by omega)).hom.app (op W)
        ((homologyMap g 0).hom.app (op W)
          (((integerConstantSingleComplex Y).homology 0).obj.map
            (homOfLE (le_top : W ≤ ⊤)).op
            (sectionCohomologyToSheafSection Y
              (integerConstantSingleComplex Y) 0 ⊤ a₀))) := by
  dsimp only
  let a := (globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homologyπ 0
    (integerCocycleGlobalSection Y (K⟦(1 : ℤ)⟧) 0 (Cocycle.ofHom g))
  let b := ShortComplex.homologyMap
    (globalSectionsShiftShortComplex Y K 1 0 1 (by omega)) a
  let a₀ := (globalSectionsComplexInt Y (integerConstantSingleComplex Y)).homologyπ 0
    (integerCocycleGlobalSection Y (integerConstantSingleComplex Y) 0
      (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))))
  let r : W ⟶ ⊤ := homOfLE (le_top : W ≤ ⊤)
  have hshift := TopCat.Sheaf.sectionCohomologyShift_restrict_eq
    Y K 1 a W
    (((K⟦(1 : ℤ)⟧).homology 0).obj.map r.op
      (sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧) 0 ⊤ a)) rfl
  have he : (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))).postcomp g =
      Cocycle.ofHom g := by
    apply Subtype.ext
    exact Cochain.id_comp (Cochain.ofHom g)
  have hpost := sectionCohomology_integerCocycleGlobalSection_postcomp Y g 0
    (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y)))
  rw [he] at hpost
  have hnat := ConcreteCategory.congr_hom
    ((homologyMap g 0).hom.naturality r.op)
    (sectionCohomologyToSheafSection Y (integerConstantSingleComplex Y) 0 ⊤ a₀)
  have hpost' := congrArg
    (fun y => ((K⟦(1 : ℤ)⟧).homology 0).obj.map r.op y) hpost
  simp only [ConcreteCategory.comp_apply] at hpost' hnat
  dsimp [a, a₀, b, r] at hshift hpost' hnat ⊢
  let q := (sectionCohomologySheafShiftMap Y K 1 0 1 (by omega)).hom.app (op W)
  have hpostshift := congrArg (fun y => q y) hpost'
  have hnatshift := congrArg (fun y => q y) hnat.symm
  exact hshift.trans (hpostshift.trans hnatshift)

lemma sectionCohomology_integerCocycleGlobalSection_ofHom_derived_square
    (Y : TopCat.{0})
    (U : Opens Y)
    [HasDerivedCategory (Sheaf AddCommGrpCat Y)]
    [HasDerivedCategory (Sheaf AddCommGrpCat ((Opens.toTopCat Y).obj U))]
    (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    (g : integerConstantSingleComplex Y ⟶ K⟦(1 : ℤ)⟧)
    (gU : ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj (integerConstantSingleComplex Y) ⟶
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        (.up ℤ)).obj (K⟦(1 : ℤ)⟧))
    (hfg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
        (DerivedCategory.Q.map g) ≫
          (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
            (K⟦(1 : ℤ)⟧) =
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategoryFactors.hom.app
          (integerConstantSingleComplex Y) ≫ DerivedCategory.Q.map gU)
    (W : Opens (TopCat.of U)) :
    let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
    let a₀ := (globalSectionsComplexInt Y (integerConstantSingleComplex Y)).homologyπ 0
      (integerCocycleGlobalSection Y (integerConstantSingleComplex Y) 0
        (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))))
    let a := (globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homologyπ 0
      (integerCocycleGlobalSection Y (K⟦(1 : ℤ)⟧) 0 (Cocycle.ofHom g))
    let b := ShortComplex.homologyMap
      (globalSectionsShiftShortComplex Y K 1 0 1 (by omega)) a
    let t :=
      ((((integerConstantSingleComplex Y).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((K⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app (op W)
        (((integerConstantSingleComplex Y).homology 0).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
          (sectionCohomologyToSheafSection Y
            (integerConstantSingleComplex Y) 0 ⊤ a₀))
    (K.homology 1).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
        (sectionCohomologyToSheafSection Y K 1 ⊤ b) =
      (sectionCohomologySheafShiftMap Y K 1 0 1 (by omega)).hom.app
        (op (U.isOpenEmbedding.functor.obj W))
        t := by
  dsimp only
  let F := U.isOpenEmbedding.sheafPullback AddCommGrpCat
  let a₀ := (globalSectionsComplexInt Y (integerConstantSingleComplex Y)).homologyπ 0
    (integerCocycleGlobalSection Y (integerConstantSingleComplex Y) 0
      (Cocycle.ofHom (𝟙 (integerConstantSingleComplex Y))))
  let a := (globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homologyπ 0
    (integerCocycleGlobalSection Y (K⟦(1 : ℤ)⟧) 0 (Cocycle.ofHom g))
  let b := ShortComplex.homologyMap
    (globalSectionsShiftShortComplex Y K 1 0 1 (by omega)) a
  let r : U.isOpenEmbedding.functor.obj W ⟶ ⊤ :=
    homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)
  have hlocal := CategoryTheory.Functor.map_homologyMap_eq_of_derived_square
    F g gU hfg 0
  have hlocalW := congrArg (fun f => f.hom.app (op W)) hlocal
  have hsource := sectionCohomology_integerCocycleGlobalSection_ofHom_shift_onOpen
    Y K g (U.isOpenEmbedding.functor.obj W)
  have hlocalElem := ConcreteCategory.congr_hom hlocalW
    (((integerConstantSingleComplex Y).homology 0).obj.map r.op
      (sectionCohomologyToSheafSection Y (integerConstantSingleComplex Y) 0 ⊤ a₀))
  dsimp [a₀, a, b, r] at hsource hlocalElem ⊢
  rw [hsource]
  exact congrArg
    ((sectionCohomologySheafShiftMap Y K 1 0 1 (by omega)).hom.app
      (op (U.isOpenEmbedding.functor.obj W))) hlocalElem

end TopCat.Sheaf
