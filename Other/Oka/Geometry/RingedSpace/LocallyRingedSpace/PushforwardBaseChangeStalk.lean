/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PushforwardBaseChangeComp

/-!
# Stalks of base change morphisms along open embeddings

Let `f : X ⟶ Y` be a morphism of locally ringed spaces. We record:

* `Hom.bijective_stalkFunctor_map_pullbackModules`: `f^* φ` is bijective on the stalk at `x` if
  `φ` is bijective on the stalk at `f x`;
* `Hom.bijective_stalkFunctor_map_of_pushforward`: if every neighbourhood of `x` contains the
  preimage of a neighbourhood of `f x` (e.g. `f` inducing), `φ` is bijective on the stalk at `x`
  if `f_* φ` is bijective on the stalk at `f x`;
* `Hom.bijective_stalkFunctor_map_counit`: if moreover `𝒪_{Y, f x} → 𝒪_{X, x}` is an
  isomorphism, the counit `f^* f_* G ⟶ G` is bijective on the stalk at `x`;
* `bijective_app_of_bijective_stalkFunctor_map`: a morphism of sheaves of modules which is
  bijective on the stalks at the points of an open `U` is bijective on sections over `U`; hence
  `f_* φ` is bijective on the stalks over an open `W` if `φ` is bijective on the stalks over
  `f⁻¹ W` (`Hom.bijective_stalkFunctor_map_pushforward_of_forall`).

For a commutative square `f' ≫ g = g' ≫ f` in which `f` and `f'` are open embeddings with
bijective stalk maps, the base change morphism `g^* f_* G ⟶ f'_* g'^* G` is bijective on the
stalks at the points of the image of `f'`
(`bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding`): it is the unit of
`f'^* ⊣ f'_*`, followed by `f'_*` of `f'^* g^* f_* G ≅ g'^* f^* f_* G ⟶ g'^* G`, and near the image
of `f'` all of these are isomorphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

/-- Every neighbourhood of a point `x` contains the preimage of a neighbourhood of `f x` if the
underlying map of `f` is inducing. -/
lemma Hom.exists_preimage_le_of_isInducing (f : X ⟶ Y) (hf : IsInducing f.base) {x : X}
    (W : Opens X.toPresheafedSpace) (hx : x ∈ W) :
    ∃ V : Opens Y.toPresheafedSpace, f.base x ∈ V ∧ (Opens.map f.base).obj V ≤ W := by
  obtain ⟨t, ht, hts⟩ := hf.isOpen_iff.1 W.isOpen
  refine ⟨⟨t, ht⟩, ?_, fun z hz ↦ ?_⟩
  · change x ∈ f.base ⁻¹' t
    rw [hts]
    exact hx
  · change z ∈ f.base ⁻¹' t at hz
    rw [hts] at hz
    exact hz

/-- **Pullback preserves stalkwise bijectivity**: `f^* φ` is bijective on the stalk at `x` if `φ`
is bijective on the stalk at `f x`. -/
lemma Hom.bijective_stalkFunctor_map_pullbackModules (f : X ⟶ Y) (x : X)
    {M N : SheafOfModules.{u} Y.ringSheaf} (φ : M ⟶ N)
    (h : Function.Bijective ((Y.stalkFunctor (f.base x)).map φ)) :
    Function.Bijective ((X.stalkFunctor x).map (f.pullbackModules.map φ)) := by
  haveI : IsIso ((Y.stalkFunctor (f.base x)).map φ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso ((Y.stalkFunctor (f.base x) ⋙
      ModuleCat.extendScalars (f.stalkMap x).hom).map φ) := by
    rw [Functor.comp_map]
    exact Functor.map_isIso _ _
  haveI : IsIso ((f.pullbackModules ⋙ X.stalkFunctor x).map φ) :=
    (NatIso.isIso_map_iff (f.pullbackModulesStalkIso x) φ).2 inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).1 this

variable (f : X ⟶ Y) {x : X}
  (hf : ∀ W : Opens X.toPresheafedSpace, x ∈ W →
    ∃ V : Opens Y.toPresheafedSpace, f.base x ∈ V ∧ (Opens.map f.base).obj V ≤ W)

include hf in
/-- If every neighbourhood of `x` contains the preimage of a neighbourhood of `f x` and `f_* φ` is
bijective on the stalk at `f x`, then `φ` is bijective on the stalk at `x`. -/
lemma Hom.bijective_stalkFunctor_map_of_pushforward {H H' : SheafOfModules.{u} X.ringSheaf}
    (φ : H ⟶ H') (hφ : Function.Bijective ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ))) :
    Function.Bijective ((X.stalkFunctor x).map φ) := by
  have h₁ := f.bijective_stalkPushforwardModules_of_forall hf H
  have h₂ := f.bijective_stalkPushforwardModules_of_forall hf H'
  have e : (X.stalkFunctor x).map φ ∘ f.stalkPushforwardModules H x =
      f.stalkPushforwardModules H' x ∘ (Y.stalkFunctor (f.base x)).map
        ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) :=
    funext fun m ↦ (f.stalkPushforwardModules_naturality φ x m).symm
  rw [← Function.Bijective.of_comp_iff _ h₁, e]
  exact h₂.comp hφ

include hf in
/-- If every neighbourhood of `x` contains the preimage of a neighbourhood of `f x` and
`𝒪_{Y, f x} → 𝒪_{X, x}` is an isomorphism, the counit `f^* f_* G ⟶ G` is bijective on the stalk
at `x`. -/
lemma Hom.bijective_stalkFunctor_map_counit [IsIso (f.stalkMap x)]
    (G : SheafOfModules.{u} X.ringSheaf) :
    Function.Bijective ((X.stalkFunctor x).map (f.pullbackModulesAdj.counit.app G)) := by
  refine f.bijective_stalkFunctor_map_of_pushforward hf _ ?_
  have hη := f.bijective_stalkFunctor_map_unit hf
    ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G)
  have htri := congrArg (Y.stalkFunctor (f.base x)).map
    (f.pullbackModulesAdj.right_triangle_components G)
  rw [Functor.map_comp, CategoryTheory.Functor.map_id] at htri
  have hid : ∀ m, ((Y.stalkFunctor (f.base x)).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map (f.pullbackModulesAdj.counit.app G)))
      (((Y.stalkFunctor (f.base x)).map (f.pullbackModulesAdj.unit.app
        ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G))) m) = m := fun m ↦ by
    exact ConcreteCategory.congr_hom htri m
  refine ⟨fun a b hab ↦ ?_, fun m ↦ ⟨_, hid m⟩⟩
  obtain ⟨a, rfl⟩ := hη.2 a
  obtain ⟨b, rfl⟩ := hη.2 b
  rw [hid, hid] at hab
  rw [hab]

variable {Y : LocallyRingedSpace.{u}} in
/-- A morphism of sheaves of modules which is bijective on the stalks at all points of an open
`U` is bijective on the sections over `U`. -/
lemma bijective_app_of_bijective_stalkFunctor_map {M N : SheafOfModules.{u} Y.ringSheaf}
    (φ : M ⟶ N) (U : Opens Y.toPresheafedSpace)
    (h : ∀ y ∈ U, Function.Bijective ((Y.stalkFunctor y).map φ)) :
    Function.Bijective (φ.val.app (op U)) :=
  TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective (C := AddCommGrpCat.{u})
    ((SheafOfModules.toSheaf _).map φ) U h

variable {Y : LocallyRingedSpace.{u}} in
/-- If `φ` is bijective on the stalks at the points of `f⁻¹ W` for an open `W`, then `f_* φ` is
bijective on the stalks at the points of `W`. -/
lemma Hom.bijective_stalkFunctor_map_pushforward_of_forall {X : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) {H H' : SheafOfModules.{u} X.ringSheaf} (φ : H ⟶ H')
    (W : Opens Y.toPresheafedSpace)
    (h : ∀ z : X, f.base z ∈ W → Function.Bijective ((X.stalkFunctor z).map φ)) {y : Y}
    (hy : y ∈ W) :
    Function.Bijective ((Y.stalkFunctor y).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ)) :=
  bijective_stalkFunctor_map_of_bijective_app _ (fun V hV ↦
    bijective_app_of_bijective_stalkFunctor_map φ ((Opens.map f.base).obj V)
      fun z hz ↦ h z (hV hz)) hy

section Square

variable {X Y X' Y' : LocallyRingedSpace.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {g : X' ⟶ X}
  {g' : Y' ⟶ Y} (h : f' ≫ g = g' ≫ f)

/-- **Base change along open embeddings**: if `f` and `f'` are open embeddings with bijective
stalk maps, the base change morphism `g^* f_* G ⟶ f'_* g'^* G` is bijective on the stalks at the
points of the image of `f'`. -/
theorem bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding
    (hf : IsOpenEmbedding f.base) [∀ y, IsIso (f.stalkMap y)] (hf' : IsOpenEmbedding f'.base)
    [∀ y', IsIso (f'.stalkMap y')] (G : SheafOfModules.{u} Y.ringSheaf) (y' : Y') :
    Function.Bijective ((X'.stalkFunctor (f'.base y')).map (pushforwardModulesBaseChange h G)) := by
  have hψ : Function.Bijective ((Y'.stalkFunctor y').map
      ((Hom.pullbackModulesCommSqIso h).hom.app _ ≫
        g'.pullbackModules.map (f.pullbackModulesAdj.counit.app G))) := by
    rw [Functor.map_comp, ConcreteCategory.coe_comp]
    refine Function.Bijective.comp ?_ ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)
    exact g'.bijective_stalkFunctor_map_pullbackModules y' _
      (f.bijective_stalkFunctor_map_counit (fun W hW ↦ f.exists_preimage_le_of_isInducing
        hf.isInducing W hW) G)
  have hf'x := fun W hW ↦ f'.exists_preimage_le_of_isInducing hf'.isInducing (x := y') W hW
  rw [pushforwardModulesBaseChange, Functor.map_comp, ConcreteCategory.coe_comp]
  exact (f'.bijective_stalkFunctor_map_pushforward hf'x _ hψ).comp
    (f'.bijective_stalkFunctor_map_unit hf'x _)

end Square

end AlgebraicGeometry.LocallyRingedSpace

end
