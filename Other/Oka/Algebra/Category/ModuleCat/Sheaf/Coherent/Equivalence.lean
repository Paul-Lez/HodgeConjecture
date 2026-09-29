/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality

/-! # Coherence under equivalences of sites -/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category* C] [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (e : C ≌ D)


instance isContinuous_overPost [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.post (X := X) e.functor).IsContinuous (J.over X) (K.over (e.functor.obj X)) := by
  haveI : (Over.postEquiv X e).symm.functor.IsCocontinuous (K.over _) (J.over X) :=
    isCocontinuous_comp _ _ (K.over _) (J.over _)
  exact (Over.postEquiv X e).symm.toAdjunction.isContinuous_of_isCocontinuous _ _


instance isContinuous_overPost_inverse [e.functor.IsCocontinuous J K] (Y : D) :
    (Over.post (X := Y) e.inverse).IsContinuous (K.over Y) (J.over (e.inverse.obj Y)) :=
  haveI : e.symm.inverse.IsCocontinuous J K := ‹_›
  e.symm.isContinuous_overPost Y


instance isContinuous_postEquiv_functor [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.postEquiv X e).functor.IsContinuous (J.over X) (K.over (e.functor.obj X)) :=
  e.isContinuous_overPost X


instance isContinuous_postEquiv_inverse [e.functor.IsCocontinuous J K] (X : C) :
    (Over.postEquiv X e).inverse.IsContinuous (K.over (e.functor.obj X)) (J.over X) :=
  have h₁ := e.isContinuous_overPost_inverse (J := J) (K := K) (e.functor.obj X)
  have h₂ : (Over.map (e.unitIso.inv.app X)).IsContinuous
      (J.over (e.inverse.obj (e.functor.obj X))) (J.over X) :=
    inferInstanceAs ((Over.map (e.unitIso.inv.app X)).IsContinuous
      (J.over ((e.functor ⋙ e.inverse).obj X)) (J.over ((𝟭 C).obj X)))
  @Functor.isContinuous_comp _ _ _ _ _ _ (Over.post e.inverse) (Over.map (e.unitIso.inv.app X))
    (K.over (e.functor.obj X)) (J.over _) (J.over X) h₁ h₂


instance isCocontinuous_postEquiv_functor [e.functor.IsCocontinuous J K] (X : C) :
    (Over.postEquiv X e).functor.IsCocontinuous (J.over X) (K.over (e.functor.obj X)) :=
  inferInstanceAs ((Over.post e.functor).IsCocontinuous _ _)


instance isCocontinuous_postEquiv_inverse [e.inverse.IsCocontinuous K J] (X : C) :
    (Over.postEquiv X e).inverse.IsCocontinuous (K.over (e.functor.obj X)) (J.over X) := by
  have h₂ : (Over.map (e.unitIso.inv.app X)).IsCocontinuous
      (J.over (e.inverse.obj (e.functor.obj X))) (J.over X) :=
    inferInstanceAs ((Over.map (e.unitIso.inv.app X)).IsCocontinuous
      (J.over ((e.functor ⋙ e.inverse).obj X)) (J.over ((𝟭 C).obj X)))
  exact @isCocontinuous_comp _ _ _ _ _ _ (Over.post e.inverse)
    (Over.map (e.unitIso.inv.app X)) (K.over (e.functor.obj X)) (J.over _) (J.over X) _ h₂

end CategoryTheory.Equivalence

namespace SheafOfModules

variable {C D : Type u} [SmallCategory C] [SmallCategory D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (eqv : C ≌ D)
  [eqv.functor.IsContinuous J K] [eqv.inverse.IsContinuous K J]
  [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)


noncomputable abbrev sliceRingHom (W : C) :
    S.over W ⟶ ((Over.post (X := W) eqv.functor).sheafPushforwardContinuous RingCat.{u}
      (J.over W) (K.over (eqv.functor.obj W))).obj (R.over (eqv.functor.obj W)) :=
  ((Over.forget W).sheafPushforwardContinuous RingCat.{u} (J.over W) J).map φ


noncomputable abbrev sliceRingHomInv (W : C) :
    R.over (eqv.functor.obj W) ⟶ ((Over.postEquiv W eqv).inverse.sheafPushforwardContinuous
      RingCat.{u} (K.over (eqv.functor.obj W)) (J.over W)).obj (S.over W) :=
  ((Over.forget (eqv.functor.obj W)).sheafPushforwardContinuous RingCat.{u} _ K).map ψ

include H₁ H₂ in

noncomputable def sliceEquivalence (W : C) :
    SheafOfModules.{u} (R.over (eqv.functor.obj W)) ≌ SheafOfModules.{u} (S.over W) :=
  pushforwardPushforwardEquivalence (Over.postEquiv W eqv) (sliceRingHom eqv φ W)
    (sliceRingHomInv eqv ψ W) (by
      ext Z : 2
      exact NatTrans.congr_app H₁ (Opposite.op Z.unop.left)) (by
      ext Z : 2
      exact NatTrans.congr_app H₂ (Opposite.op Z.unop.left))

omit [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J] in
include H₂ in

lemma symm_H₁ :
    Functor.whiskerRight (NatTrans.op eqv.symm.counit) S.obj =
      φ.hom ≫ eqv.symm.inverse.op.whiskerLeft ψ.hom := by
  ext X : 2
  have h := NatTrans.congr_app H₂ X
  change φ.hom.app X ≫ ψ.hom.app _ ≫ S.obj.map (eqv.unit.app X.unop).op = 𝟙 _ at h
  change S.obj.map (eqv.unitInv.app X.unop).op = φ.hom.app X ≫ ψ.hom.app _
  have e : S.obj.map (eqv.unit.app X.unop).op ≫ S.obj.map (eqv.unitInv.app X.unop).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
  have h' := h =≫ S.obj.map (eqv.unitInv.app X.unop).op
  rw [Category.assoc, Category.assoc] at h'
  erw [e] at h'
  erw [Category.comp_id, Category.id_comp] at h'
  exact h'.symm

omit [eqv.functor.IsCocontinuous J K] [eqv.inverse.IsCocontinuous K J] in
include H₁ in

lemma symm_H₂ :
    ψ.hom ≫ eqv.symm.functor.op.whiskerLeft φ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.symm.unit) R.obj = 𝟙 R.obj := by
  ext X : 2
  have h := NatTrans.congr_app H₁ X
  change R.obj.map (eqv.counit.app X.unop).op = ψ.hom.app X ≫ φ.hom.app _ at h
  change ψ.hom.app X ≫ φ.hom.app _ ≫ R.obj.map (eqv.counitInv.app X.unop).op = 𝟙 _
  have e : R.obj.map (eqv.counit.app X.unop).op ≫ R.obj.map (eqv.counitInv.app X.unop).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
  rw [← Category.assoc, ← h]
  exact e

variable [HasPullbacks C] [HasPullbacks D]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : D) (Y : Over X), HasSheafify ((K.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : D) (Y : Over X), ((K.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

include H₁ H₂ in

theorem isCoherent_pushforward_of_equivalence [IsIso φ]
    (η : (pushforward φ).obj (unit R) ≅ unit S) (M : SheafOfModules.{u} R) [M.IsCoherent] :
    ((pushforward φ).obj M).IsCoherent where
  isFiniteType := isFiniteType_pushforward_of_isLeftAdjoint eqv.functor φ η
  hasFiniteTypeRelations W := by
    intro I _ χ
    let E := sliceEquivalence eqv φ ψ H₁ H₂ W
    let ηW : unit (S.over W) ≅ E.functor.obj (unit (R.over (eqv.functor.obj W))) :=
      ((overFunctor S W).mapIso η).symm
    let χ₁ : free I ⟶ E.functor.obj (M.over (eqv.functor.obj W)) := χ
    let χ' := E.fullyFaithfulFunctor.preimage ((mapFreeIso E.functor I ηW).inv ≫ χ₁)
    haveI : (kernel χ').IsFiniteType := IsCoherent.hasFiniteTypeRelations M _ χ'
    haveI : IsIso (sliceRingHom eqv φ W) := Functor.map_isIso _ φ
    haveI (X : Over W) : (Over.post (Over.post eqv.functor)).IsContinuous ((J.over W).over X)
        ((K.over (eqv.functor.obj W)).over ((Over.post eqv.functor).obj X)) :=
      (Over.postEquiv W eqv).isContinuous_overPost X
    haveI : (E.functor.obj (kernel χ')).IsFiniteType :=
      isFiniteType_pushforward_of_isLeftAdjoint (Over.post eqv.functor) (sliceRingHom eqv φ W)
        ηW.symm
    have hχ : (mapFreeIso E.functor I ηW).hom ≫ E.functor.map χ' = χ₁ := by
      simp [χ']
    exact IsFiniteType.of_iso ((PreservesKernel.iso E.functor χ') ≪≫
      (kernelIsIsoComp _ _).symm ≪≫ kernelIsoOfEq hχ)

include H₁ H₂ in

theorem isCoherent_of_isCoherent_pushforward_of_equivalence [IsIso ψ]
    (η : (pushforward φ).obj (unit R) ≅ unit S) (M : SheafOfModules.{u} R)
    (hM : ((pushforward φ).obj M).IsCoherent) : M.IsCoherent := by
  let E := pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂
  haveI : eqv.symm.functor.IsContinuous K J := ‹eqv.inverse.IsContinuous K J›
  haveI : eqv.symm.inverse.IsContinuous J K := ‹eqv.functor.IsContinuous J K›
  haveI : eqv.symm.functor.IsCocontinuous K J := ‹eqv.inverse.IsCocontinuous K J›
  haveI : eqv.symm.inverse.IsCocontinuous J K := ‹eqv.functor.IsCocontinuous J K›
  haveI : IsIso (C := Sheaf K RingCat.{u}) (X := R)
      (Y := (eqv.symm.functor.sheafPushforwardContinuous RingCat.{u} K J).obj S) ψ :=
    ‹IsIso ψ›
  let η' : (pushforward ψ).obj (unit S) ≅ unit R :=
    (pushforward ψ).mapIso η.symm ≪≫ (E.unitIso.app (unit R)).symm
  haveI : ((pushforward ψ).obj ((pushforward φ).obj M)).IsCoherent :=
    isCoherent_pushforward_of_equivalence eqv.symm ψ φ (symm_H₁ eqv φ ψ H₂)
      (symm_H₂ eqv φ ψ H₁) η' ((pushforward φ).obj M)
  exact IsCoherent.of_iso (M := (pushforward ψ).obj ((pushforward φ).obj M))
    (E.unitIso.app M).symm

end SheafOfModules
