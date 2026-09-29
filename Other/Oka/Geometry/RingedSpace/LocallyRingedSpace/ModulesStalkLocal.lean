/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkNakayama
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbeddingUnit

/-!
# Stalks of sheaves of modules near a point

Let `f : X ⟶ Y` be a morphism of locally ringed spaces and `x : X` a point such that every open
neighbourhood of `x` contains `f⁻¹ V` for some open neighbourhood `V` of `f x` (e.g. `f` restricts
to an open embedding on a neighbourhood of `x` which is the full preimage of its image). Then:

- `AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_stalkPushforwardModules_of_forall`: the map
  `(f_* H)_{f x} → H_x` is bijective;
- `AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_stalkFunctor_map_pushforward`: `f_* φ` is
  bijective on the stalk at `f x` if `φ` is bijective on the stalk at `x`;
- `AlgebraicGeometry.LocallyRingedSpace.Hom.bijective_stalkFunctor_map_unit`: if moreover
  `𝒪_{Y, f x} → 𝒪_{X, x}` is an isomorphism, the unit `A ⟶ f_* f^* A` is bijective on the stalk
  at `f x`.

We also record that a morphism which is bijective on sections over all opens inside `W` is
bijective on stalks at the points of `W`
(`AlgebraicGeometry.LocallyRingedSpace.bijective_stalkFunctor_map_of_bijective_app`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

/-- A morphism of sheaves of modules which is bijective on sections over all opens contained in
`W` is bijective on the stalks at the points of `W`. -/
lemma bijective_stalkFunctor_map_of_bijective_app {M N : SheafOfModules.{u} Y.ringSheaf}
    (φ : M ⟶ N) {W : Opens Y.toPresheafedSpace}
    (hφ : ∀ V ≤ W, Function.Bijective (φ.val.app (op V))) {y : Y} (hy : y ∈ W) :
    Function.Bijective ((Y.stalkFunctor y).map φ) := by
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · obtain ⟨W₁, hW₁, hy₁, s, rfl⟩ := exists_germMod_eq_of_le hy a
    obtain ⟨W₂, hW₂, hy₂, t, rfl⟩ := exists_germMod_eq_of_le hy₁ b
    have hs : germMod M hy₁ s = germMod M hy₂ (M.val.presheaf.map (homOfLE hW₂).op s) :=
      (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hW₂) y hy₂ s).symm
    rw [hs, stalkFunctor_map_germMod, stalkFunctor_map_germMod] at hab
    rw [hs]
    obtain ⟨W₃, hy₃, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq N.val.presheaf y hy₂ hy₂ _ _ hab
    rw [Subsingleton.elim i₂ i₁] at heq
    have hn : ∀ z : M.val.obj (op W₂), N.val.presheaf.map i₁.op (φ.val.app (op W₂) z) =
        φ.val.app (op W₃) (M.val.presheaf.map i₁.op z) := fun z ↦
      congr($(φ.val.naturality i₁.op).hom z).symm
    rw [hn, hn] at heq
    have h₃ := (hφ W₃ ((i₁.le.trans hW₂).trans hW₁)).1 heq
    unfold germMod
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf i₁ y hy₃,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf i₁ y hy₃ t]
    exact congrArg (TopCat.Presheaf.germ M.val.presheaf W₃ y hy₃) h₃
  · obtain ⟨W₁, hW₁, hy₁, t, rfl⟩ := exists_germMod_eq_of_le hy b
    obtain ⟨s, rfl⟩ := (hφ W₁ hW₁).2 t
    exact ⟨germMod M hy₁ s, stalkFunctor_map_germMod φ hy₁ s⟩

variable {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) {x : X}
  (hf : ∀ W : Opens X.toPresheafedSpace, x ∈ W →
    ∃ V : Opens Y.toPresheafedSpace, f.base x ∈ V ∧ (Opens.map f.base).obj V ≤ W)

include hf in
/-- If every open neighbourhood of `x` contains the preimage of an open neighbourhood of `f x`,
the map `(f_* H)_{f x} → H_x` is bijective. -/
lemma Hom.bijective_stalkPushforwardModules_of_forall (H : SheafOfModules.{u} X.ringSheaf) :
    Function.Bijective (f.stalkPushforwardModules H x) := by
  let P := (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj H
  refine ⟨fun a b hab ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨V₁, hV₁, t₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.val.presheaf a
    obtain ⟨V₂, hV₂, t₂, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.val.presheaf b
    let V := V₁ ⊓ V₂
    have hV : f.base x ∈ V := ⟨hV₁, hV₂⟩
    rw [← TopCat.Presheaf.germ_res_apply P.val.presheaf (homOfLE inf_le_left : V ⟶ V₁) _ hV,
      ← TopCat.Presheaf.germ_res_apply P.val.presheaf (homOfLE inf_le_right : V ⟶ V₂) _ hV]
      at hab ⊢
    set s₁ := P.val.presheaf.map (homOfLE inf_le_left : V ⟶ V₁).op t₁
    set s₂ := P.val.presheaf.map (homOfLE inf_le_right : V ⟶ V₂).op t₂
    rw [f.stalkPushforwardModules_germ, f.stalkPushforwardModules_germ] at hab
    obtain ⟨W, hxW, i₁, i₂, heq⟩ := TopCat.Presheaf.germ_eq H.val.presheaf x hV hV _ _ hab
    rw [Subsingleton.elim i₂ i₁] at heq
    obtain ⟨V', hV', hV'W⟩ := hf W hxW
    let V'' := V ⊓ V'
    have hV'' : f.base x ∈ V'' := ⟨hV, hV'⟩
    let j : V'' ⟶ V := homOfLE inf_le_left
    have hj : (Opens.map f.base).obj V'' ≤ W := fun z hz ↦ hV'W hz.2
    have key : P.val.presheaf.map j.op s₁ = P.val.presheaf.map j.op s₂ := by
      change H.val.presheaf.map ((Opens.map f.base).map j).op s₁ =
        H.val.presheaf.map ((Opens.map f.base).map j).op s₂
      have e : ((Opens.map f.base).map j) = homOfLE hj ≫ i₁ := rfl
      rw [e, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, heq]
    rw [← TopCat.Presheaf.germ_res_apply P.val.presheaf j _ hV'',
      ← TopCat.Presheaf.germ_res_apply P.val.presheaf j _ hV'' s₂, key]
  · obtain ⟨W, hxW, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.val.presheaf m
    obtain ⟨V, hV, hVW⟩ := hf W hxW
    refine ⟨TopCat.Presheaf.germ P.val.presheaf V (f.base x) hV
      (H.val.presheaf.map (homOfLE hVW).op s), ?_⟩
    rw [f.stalkPushforwardModules_germ]
    exact TopCat.Presheaf.germ_res_apply H.val.presheaf (homOfLE hVW) x hV s

include hf in
/-- If every open neighbourhood of `x` contains the preimage of an open neighbourhood of `f x`
and `φ` is bijective on the stalk at `x`, then `f_* φ` is bijective on the stalk at `f x`. -/
lemma Hom.bijective_stalkFunctor_map_pushforward {H H' : SheafOfModules.{u} X.ringSheaf}
    (φ : H ⟶ H') (hφ : Function.Bijective ((X.stalkFunctor x).map φ)) :
    Function.Bijective ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ)) := by
  have h₁ := f.bijective_stalkPushforwardModules_of_forall hf H
  have h₂ := f.bijective_stalkPushforwardModules_of_forall hf H'
  rw [← Function.Bijective.of_comp_iff' h₂]
  have e : f.stalkPushforwardModules H' x ∘ (Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) =
      (X.stalkFunctor x).map φ ∘ f.stalkPushforwardModules H x :=
    funext (f.stalkPushforwardModules_naturality φ x)
  rw [e]
  exact hφ.comp h₁

include hf in
/-- If every open neighbourhood of `x` contains the preimage of an open neighbourhood of `f x`
and `𝒪_{Y, f x} → 𝒪_{X, x}` is an isomorphism, the unit `A ⟶ f_* f^* A` is bijective on the
stalk at `f x`. -/
lemma Hom.bijective_stalkFunctor_map_unit [IsIso (f.stalkMap x)]
    (A : SheafOfModules.{u} Y.ringSheaf) :
    Function.Bijective ((Y.stalkFunctor (f.base x)).map (f.pullbackModulesAdj.unit.app A)) := by
  have hb : Function.Bijective (f.stalkMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have he : Function.Bijective ((f.pullbackModulesStalkIso x).hom.app A) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have hs := f.bijective_stalkPushforwardModules_of_forall hf (f.pullbackModules.obj A)
  have e : ((f.pullbackModulesStalkIso x).hom.app A ∘ f.stalkPushforwardModules _ x) ∘
      (Y.stalkFunctor (f.base x)).map (f.pullbackModulesAdj.unit.app A) =
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app _ :=
    funext (f.pullbackModulesStalkIso_stalkPushforwardModules_unit A x)
  refine (Function.Bijective.of_comp_iff' (he.comp hs) _).1 ?_
  rw [e]
  refine ModuleCat.bijective_extendRestrictScalarsAdj_unit_app_of_surjective _ hb.2 _ ?_
  intro r hr m
  rw [RingHom.mem_ker] at hr
  rw [hb.1 (hr.trans (map_zero _).symm), zero_smul]

end AlgebraicGeometry.LocallyRingedSpace

end
