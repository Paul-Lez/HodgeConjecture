/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeNormalization
public import Other.AlgebraicTopology.Sheaf.CohomologySectionArbitraryDegreeVanishing
public import Other.AlgebraicGeometry.UnitExtensionOpenRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CategoryTheory.Localization

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint

local instance supportLocalVanishingTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance supportAnalyticDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance supportSheafDerivedCategory (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) :=
  HasDerivedCategory.standard _

lemma supportAmbientDerivedClass_topDerivedHom
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n) :
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
    let eTop := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective
      (TopCat.of (ComplexPoint X)) C (n - 1)
    eTop.symm (e α) =
      DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
        hypercohomologyAddEquivDerived X C (n - 1)
          (hypercohomologyMap X (rationalSupportConeToAmbientInjectiveCone X Z hZ)
            (n - 1) α) := by
  dsimp [rationalSupportAddEquivAmbientInjectiveConeGlobalSections,
    hypercohomologyAddEquivGlobalSectionsKInjective]
  simp only [AddEquiv.symm_apply_apply, Category.comp_id]
  rw [hypercohomologyAddEquivDerived_naturality]
  exact congrArg (fun f => DerivedCategory.Q.map
    (constantIntegerSheafComplexIntIsoSingle X).inv ≫ f)
    (hypercohomologyAddEquivDerived_naturality X
      (rationalSupportConeToAmbientInjectiveCone X Z hZ) (n - 1) α)

lemma supportAmbientDerivedClass_restrict_eq_zero
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (hα : (restrictToOpen X U).mapDerivedCategory.map
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
        DerivedCategory.Q) α) = 0) :
    (restrictToOpen X U).mapDerivedCategory.map
      (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
        (hypercohomologyAddEquivDerived X
          (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))
          (n - 1)
    (hypercohomologyMap X (rationalSupportConeToAmbientInjectiveCone X Z hZ)
            (n - 1) α))) = 0 := by
  have hα' : (restrictToOpen X U).mapDerivedCategory.map
      (hypercohomologyAddEquivDerived X (rationalCohomologyWithSupportComplex X Z)
        (n - 1) α) = 0 := by
    exact hα
  rw [Functor.map_comp]
  have hnat := hypercohomologyAddEquivDerived_naturality X
    (rationalSupportConeToAmbientInjectiveCone X Z hZ) (n - 1) α
  rw [hnat]
  simp only [Functor.map_comp, hα', zero_comp, comp_zero]

lemma supportSection_restrict_eq_zero_of_cocycle
    (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ)
    [K.IsKInjective] (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle
      (TopCat.Sheaf.integerConstantSingleComplex Y) K n)
    (b : (TopCat.Sheaf.globalSectionsComplexInt Y K).homology n)
    (hb : TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y K n
      (ShiftedHom.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
        DerivedCategory.Q) = b)
    (U : Opens Y)
    (hg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      (DerivedCategory.Q.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)) = 0)
    (W : Opens (TopCat.of U)) :
    (K.homology n).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ b) = 0 := by
  have hzero :=
    TopCat.Sheaf.sectionCohomology_integerCocycleGlobalSection_ofHom_shift_onOpen_eq_zero
      Y K n z (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z) rfl U hg W
  rw [← hb]
  have hc := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective_cocycle
    Y K n z
  have hfun := congrArg (fun t =>
    (K.homology n).obj.map
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ t)) hc
  exact hfun.trans hzero

lemma supportAmbientSection_restrict_eq_zero
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (hα : (restrictToOpen X U).mapDerivedCategory.map
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
        DerivedCategory.Q) α) = 0)
    (W : Opens (TopCat.of U)) :
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
    (C.homology (n - 1)).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection
        (TopCat.of (ComplexPoint X)) C (n - 1) ⊤ (e α)) = 0 := by
  let Y := TopCat.of (ComplexPoint X)
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  let eTop := TopCat.Sheaf.derivedHomAddEquivGlobalSectionsKInjective Y C (n - 1)
  let b := e α
  let x := eTop.symm b
  have hx : eTop x = b := eTop.apply_symm_apply b
  have hx0 : (restrictToOpen X U).mapDerivedCategory.map x = 0 := by
    change (restrictToOpen X U).mapDerivedCategory.map (eTop.symm (e α)) = 0
    rw [supportAmbientDerivedClass_topDerivedHom]
    exact supportAmbientDerivedClass_restrict_eq_zero X Z hZ n α U hα
  let E := CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass
    (TopCat.Sheaf.integerConstantSingleComplex Y) C (n - 1)
  obtain ⟨z, hz⟩ := (E x).mk_surjective
  have hzx : x = ShiftedHom.map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
      DerivedCategory.Q := by
    apply E.injective
    rw [← hz, ← CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
      AddEquiv.apply_symm_apply]
  have hg : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      (DerivedCategory.Q.map
        (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)) = 0 := by
    have hshift : (U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
        (ShiftedHom.map
          (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
          DerivedCategory.Q) = 0 := by
      rw [← hzx]
      exact hx0
    apply (cancel_mono ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapDerivedCategory.map
      ((DerivedCategory.Q.commShiftIso (n - 1)).hom.app C))).mp
    simpa only [Functor.map_comp, ShiftedHom.map, comp_zero, zero_comp] using hshift
  have hb : eTop (ShiftedHom.map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
      DerivedCategory.Q) = e α := by
    rw [← hzx]
    exact hx
  exact supportSection_restrict_eq_zero_of_cocycle Y C (n - 1) z
    (e α) hb U hg W

lemma sectionCohomologyToSheafSection_restrict_eq_zero_of_quasiIso
    (Y : TopCat.{0})
    (K L : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ)
    (m : K ⟶ L) [QuasiIso m] (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt Y K).homology n)
    (b : (TopCat.Sheaf.globalSectionsComplexInt Y L).homology n)
    (hm : HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).map m) n a = b)
    (W : Opens Y)
    (hL : (L.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y L n ⊤ b) = 0) :
    (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ a) = 0 := by
  change HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).map m) n a = b at hm
  have : IsIso (HomologicalComplex.homologyMap m n) :=
    (quasiIsoAt_iff_isIso_homologyMap m n).mp inferInstance
  let H := HomologicalComplex.homologyMap m n
  have hnat := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_naturality Y m n ⊤) a
  have hnatW := ConcreteCategory.congr_hom
    (H.hom.naturality (homOfLE (le_top : W ≤ ⊤)).op)
    (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤ a)
  have hnat' := hnat
  have hnatW' := hnatW
  simp only [ConcreteCategory.comp_apply] at hnat' hnatW'
  apply ((ConcreteCategory.isIso_iff_bijective (H.hom.app (op W))).mp inferInstance).1
  rw [hnatW', ← hnat', hm, hL, map_zero]

lemma sectionCohomologyShift_restrict_eq_zero
    (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ)
    (n : ℤ)
    (a : (TopCat.Sheaf.globalSectionsComplexInt Y (K⟦(1 : ℤ)⟧)).homology (n - 1))
    (W : Opens Y)
    (hzero :
      (((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.map
        (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
          (n - 1) ⊤ a) = 0)) :
    (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (ShortComplex.homologyMap
          (TopCat.Sheaf.globalSectionsShiftShortComplex Y K 1 (n - 1) n (by omega)) a)) = 0 := by
  let h : (1 : ℤ) + (n - 1) = n := by omega
  have hshift := TopCat.Sheaf.sectionCohomologyToSheafSection_shift_naturality
    Y K 1 (n - 1) n h W
  have hshiftTop := TopCat.Sheaf.sectionCohomologyToSheafSection_shift_naturality
    Y K 1 (n - 1) n h ⊤
  have htop := TopCat.Sheaf.sectionCohomologyPresheafShiftShortComplex_top_homology
    Y K 1 (n - 1) n h
  rw [htop] at hshiftTop
  have hshiftTopA := ConcreteCategory.congr_hom hshiftTop a
  have hshiftTopR := congrArg
    (fun y => (K.homology n).obj.map (homOfLE (le_top : W ≤ ⊤)).op y) hshiftTopA
  have hnat := ConcreteCategory.congr_hom
    ((TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n h).hom.naturality
      (homOfLE (le_top : W ≤ ⊤)).op)
    (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
      (n - 1) ⊤ a)
  have hzero' := congrArg
    (fun y => (TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 (n - 1) n h).hom.app
      (op W) y) hzero
  simp only [ConcreteCategory.comp_apply] at hshiftTopA hshiftTopR hnat hzero'
  dsimp [h] at hshiftTopA hshiftTopR hnat hzero' ⊢
  exact hshiftTopR.trans (hnat.symm.trans (by simpa only [map_zero] using hzero'))

lemma supportSheafSection_restrict_eq_zero
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (hα : (restrictToOpen X U).mapDerivedCategory.map
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
        DerivedCategory.Q) α) = 0)
    (W : Opens (TopCat.of U)) :
    let Y := TopCat.of (ComplexPoint X)
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
    let Hm := HomologicalComplex.homologyMap
      (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)
    let a := inv Hm
      (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n α)
    (K.homology n).obj.map
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (ShortComplex.homologyMap
          (TopCat.Sheaf.globalSectionsShiftShortComplex Y K 1 (n - 1) n (by omega)) a)) = 0 := by
  let Y := TopCat.of (ComplexPoint X)
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
  let K := S.X₁
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let Hm := HomologicalComplex.homologyMap
    (((Γ.mapHomologicalComplex (.up ℤ)).map m)) (n - 1)
  let e := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n
  let a := inv Hm (e α)
  have hL := supportAmbientSection_restrict_eq_zero X Z hZ n α U hα W
  have hm : HomologicalComplex.homologyMap
      (((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex (.up ℤ)).map m)
      (n - 1) a = e α := by
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id Hm) (e α)
  have hshift : ((K⟦(1 : ℤ)⟧).homology (n - 1)).obj.map
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y (K⟦(1 : ℤ)⟧)
        (n - 1) ⊤ a) = 0 := by
    exact sectionCohomologyToSheafSection_restrict_eq_zero_of_quasiIso
      Y (K⟦(1 : ℤ)⟧) C m (n - 1) a (e α) hm
      (U.isOpenEmbedding.functor.obj W) hL
  exact sectionCohomologyShift_restrict_eq_zero Y K n a
    (U.isOpenEmbedding.functor.obj W) hshift

lemma coneSupportSection_restrict_eq_zero
    (X : Over (Spec ↧ℂ))
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (α : RationalCohomologyWithSupport X Z n)
    (U : Opens (TopCat.of (ComplexPoint X)))
    (hα : (restrictToOpen X U).mapDerivedCategory.map
      ((Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
        DerivedCategory.Q) α) = 0)
    (W : Opens (TopCat.of U)) :
    let Y := TopCat.of (ComplexPoint X)
    let K := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)).X₁
    (K.homology n).obj.map
      (homOfLE (le_top : U.isOpenEmbedding.functor.obj W ≤ ⊤)).op
      (TopCat.Sheaf.sectionCohomologyToSheafSection Y K n ⊤
        (coneSupportAddEquivSupportedInjectiveHomology X Z hZ n α)) = 0 := by
  have h := supportSheafSection_restrict_eq_zero X Z hZ n α U hα W
  rw [coneSupportAddEquivSupportedInjectiveHomology_eq_supportSheaf]
  simpa only [map_neg, neg_zero] using congrArg Neg.neg h

end AlgebraicGeometry.ComplexPoint
