/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.Sheaf.CohomologySectionShiftTop
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

local instance arbitraryDegreeHasDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _

lemma derivedHomAddEquivGlobalSectionsKInjective_cocycle
    (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    [K.IsKInjective] (n : ℤ)
    (z : Cocycle (integerConstantSingleComplex Y) K n) :
    derivedHomAddEquivGlobalSectionsKInjective Y K n
      (ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q) =
      (globalSectionsComplexInt Y K).homologyπ n
        (integerCocycleGlobalSection Y K n z) := by
  rw [← CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]
  simp only [derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply,
    CochainComplex.HomComplex.homologyAddEquiv_symm_mk]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (homComplexSingleIntegerIsoGlobalSections Y K).hom n)
    ((leftHomologyData _ K n).cyclesIso.inv z)

lemma globalSections_homology_cocycle_rightUnshift
    (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    [K.IsKInjective] (n : ℤ)
    (z : Cocycle (integerConstantSingleComplex Y) K n) :
    (globalSectionsComplexInt Y K).homologyπ n
        (integerCocycleGlobalSection Y K n z) =
      ShortComplex.homologyMap (globalSectionsShiftShortComplex Y K n 0 n (by omega))
        ((globalSectionsComplexInt Y (K⟦n⟧)).homologyπ 0
          (integerCocycleGlobalSection Y (K⟦n⟧) 0
            (z.rightShift n 0 (zero_add n)))) := by
  let z₀ := z.rightShift n 0 (zero_add n)
  let x : ShiftedHom (DerivedCategory.Q.obj (integerConstantSingleComplex Y))
      (DerivedCategory.Q.obj (K⟦n⟧)) (0 : ℤ) :=
    ShiftedHom.map
      ((CochainComplex.HomComplex.Cocycle.equivHomShift
        (K := integerConstantSingleComplex Y) (L := K⟦n⟧) (n := 0)).symm z₀)
      DerivedCategory.Q
  have hr := derivedHomAddEquivGlobalSectionsKInjective_rightUnshift Y K n 0 n
    (by omega) x
  have h0 := derivedHomAddEquivGlobalSectionsKInjective_cocycle Y (K⟦n⟧) 0 z₀
  have h1 := derivedHomAddEquivGlobalSectionsKInjective_cocycle Y K n z
  have hx0 :
      CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
          (integerConstantSingleComplex Y) (K⟦n⟧) 0 x =
        CochainComplex.HomComplex.CohomologyClass.mk z₀ := by
    apply (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
      (integerConstantSingleComplex Y) (K⟦n⟧) 0).symm.injective
    rw [AddEquiv.symm_apply_apply,
      CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk]
  have hcK :
      CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
          (integerConstantSingleComplex Y) K n
        (x.comp ((DerivedCategory.Q.commShiftIso n).hom.app K)
          (show n + (0 : ℤ) = n by omega)) =
        CochainComplex.HomComplex.CohomologyClass.mk z := by
    rw [AlgebraicGeometry.ComplexPoint.kInjectiveDerivedHomAddEquivCohomologyClass_rightUnshift
      (integerConstantSingleComplex Y) K n 0 n (by omega) x, hx0,
      CochainComplex.HomComplex.rightUnshiftClass_mk]
    have hz : (z.rightShift n 0 (zero_add n)).rightUnshift n (zero_add n) = z := by
      apply Subtype.ext
      exact Cochain.rightUnshift_rightShift z.1 n 0 (zero_add n)
    rw [show z₀ = z.rightShift n 0 (zero_add n) by rfl, hz]
  have hc :
      derivedHomAddEquivGlobalSectionsKInjective Y K n
        (x.comp ((DerivedCategory.Q.commShiftIso n).hom.app K)
          (show n + (0 : ℤ) = n by omega)) =
        (globalSectionsComplexInt Y K).homologyπ n
          (integerCocycleGlobalSection Y K n z) := by
    dsimp only [derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
    rw [hcK, ← h1]
    dsimp only [derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
    have he := CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk
      (integerConstantSingleComplex Y) K n z
    have he' := congrArg
      (fun c => (integerConstantSingleComplex Y).kInjectiveDerivedHomAddEquivCohomologyClass
        K n c) he
    rw [← he', AddEquiv.apply_symm_apply]
  rw [hc, h0] at hr
  exact hr

lemma sectionCohomology_integerCocycleGlobalSection_ofHom_shift_onOpen_eq_zero
    (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
    [K.IsKInjective] (n : ℤ)
    (z : Cocycle (integerConstantSingleComplex Y) K n)
    (g : integerConstantSingleComplex Y ⟶ (K⟦n⟧))
    (hg0 : Cocycle.ofHom g = z.rightShift n 0 (zero_add n))
    (U : Opens Y)
    [HasDerivedCategory (Sheaf AddCommGrpCat (TopCat.of U))]
    (hg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      (DerivedCategory.Q.map g) = 0) (W : Opens (TopCat.of U)) :
    (K.homology n).obj.map (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (sectionCohomologyToSheafSection Y K n ⊤
        ((globalSectionsComplexInt Y K).homologyπ n
          (integerCocycleGlobalSection Y K n z))) = 0 := by
  let z₀ := z.rightShift n 0 (zero_add n)
  let r : U.isOpenEmbedding.functor.obj W ⟶ ⊤ :=
    homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)
  have hzero := sectionCohomology_integerCocycleGlobalSection_ofHom_onOpen_eq_zero
    Y U g hg W
  have hz : integerCocycleGlobalSection Y (K⟦n⟧) 0 (Cocycle.ofHom g) =
      integerCocycleGlobalSection Y (K⟦n⟧) 0 z₀ := by
    rw [hg0]
  rw [hz] at hzero
  have hclass := globalSections_homology_cocycle_rightUnshift Y K n z
  have htop := sectionCohomologyPresheafShiftShortComplex_top_homology
    Y K n 0 n (by omega)
  rw [← htop] at hclass
  have hshift := sectionCohomologyToSheafSection_shift_naturality
    Y K n 0 n (by omega) ⊤
  let a₀ := (globalSectionsComplexInt Y (K⟦n⟧)).homologyπ 0
    (integerCocycleGlobalSection Y (K⟦n⟧) 0 z₀)
  have hshift₀ := ConcreteCategory.congr_hom hshift a₀
  have hshift₀r := congrArg
    (fun y => (K.homology n).obj.map r.op y) hshift₀
  have hnat := ConcreteCategory.congr_hom
    ((sectionCohomologySheafShiftMap Y K n 0 n (by omega)).hom.naturality r.op)
    (sectionCohomologyToSheafSection Y (K⟦n⟧) 0 ⊤ a₀)
  have hzero' := congrArg
    (fun y => (sectionCohomologySheafShiftMap Y K n 0 n (by omega)).hom.app
      (op (U.isOpenEmbedding.functor.obj W)) y) hzero
  simp only [ConcreteCategory.comp_apply] at hshift₀r hnat hzero'
  dsimp [r, a₀, z₀] at hshift₀r hnat hzero' ⊢
  rw [hclass]
  exact hshift₀r.trans (hnat.symm.trans (by simpa only [map_zero] using hzero'))

end TopCat.Sheaf
