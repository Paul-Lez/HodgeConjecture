/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PushforwardBaseChangeStalk

/-!
# Locality of base change morphisms

We show that stalkwise bijectivity of the base change morphism
`AlgebraicGeometry.LocallyRingedSpace.pushforwardModulesBaseChange` of a commutative square of
locally ringed spaces is compatible with pasting squares along isomorphisms
(`bijective_stalkFunctor_map_pushforwardModulesBaseChange_comp_of_isIso`,
`bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_comp`) and can be tested after
restriction to open subspaces
(`bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_restrict`): given a commutative cube
whose vertical faces over `u : V ⟶ Y` and `u' : V' ⟶ Y'` are squares of open embeddings with
bijective stalk maps, the base change morphism of the back face at `F` is bijective at `ua v` if
the base change morphism of the front face at `u'^* F` is bijective at `v`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.LocallyRingedSpace

section Helpers

variable {C : Type*} [Category C] {R : Type u} [Ring R] (F : C ⥤ ModuleCat.{u} R)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

lemma _root_.CategoryTheory.Functor.bijective_map_comp (hf : Function.Bijective (F.map f))
    (hg : Function.Bijective (F.map g)) : Function.Bijective (F.map (f ≫ g)) := by
  rw [F.map_comp, ConcreteCategory.coe_comp]
  exact hg.comp hf

lemma _root_.CategoryTheory.Functor.bijective_map_of_comp_left
    (h : Function.Bijective (F.map (f ≫ g))) (hg : Function.Bijective (F.map g)) :
    Function.Bijective (F.map f) := by
  rw [F.map_comp, ConcreteCategory.coe_comp] at h
  exact (Function.Bijective.of_comp_iff' hg _).1 h

lemma _root_.CategoryTheory.Functor.bijective_map_of_comp_right
    (h : Function.Bijective (F.map (f ≫ g))) (hf : Function.Bijective (F.map f)) :
    Function.Bijective (F.map g) := by
  rw [F.map_comp, ConcreteCategory.coe_comp] at h
  exact (Function.Bijective.of_comp_iff _ hf).1 h

end Helpers

section Comp

variable {Y₁ Y₂ Z Y₁' Y₂' Z' : LocallyRingedSpace.{u}} {a : Y₁ ⟶ Y₂} {b : Y₂ ⟶ Z}
  {a' : Y₁' ⟶ Y₂'} {b' : Y₂' ⟶ Z'} {g₁ : Y₁' ⟶ Y₁} {g₂ : Y₂' ⟶ Y₂} {g : Z' ⟶ Z}
  (h₁ : a' ≫ g₂ = g₁ ≫ a) (h₂ : b' ≫ g = g₂ ≫ b) (h : (a' ≫ b') ≫ g = g₁ ≫ (a ≫ b))
  (G : SheafOfModules.{u} Y₁.ringSheaf)

/-- If the base change morphism of the left square is an isomorphism, the base change morphism of
the composite square is bijective on the stalks at which the base change morphism of the right
square is. -/
lemma bijective_stalkFunctor_map_pushforwardModulesBaseChange_comp_of_isIso
    [IsIso (pushforwardModulesBaseChange h₁ G)] (z : Z')
    (hz : Function.Bijective ((Z'.stalkFunctor z).map (pushforwardModulesBaseChange h₂
      ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G)))) :
    Function.Bijective ((Z'.stalkFunctor z).map (pushforwardModulesBaseChange h G)) := by
  rw [pushforwardModulesBaseChange_comp h₁ h₂ h]
  exact (Z'.stalkFunctor z).bijective_map_comp _ _ hz
    ((ConcreteCategory.isIso_iff_bijective _).1 ((Z'.stalkFunctor z).mapIso
      ((SheafOfModules.pushforward.{u} b'.toRingSheafHom).mapIso
        (asIso (pushforwardModulesBaseChange h₁ G)))).isIso_hom)

/-- If the base change morphism of the right square is an isomorphism and every neighbourhood of
`x` contains the preimage under `b'` of a neighbourhood of `b' x`, the base change morphism of the
left square is bijective at `x` if the base change morphism of the composite square is bijective at
`b' x`. -/
lemma bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_comp
    [IsIso (pushforwardModulesBaseChange h₂
      ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G))] {x : Y₂'}
    (hb : ∀ W : Opens Y₂'.toPresheafedSpace, x ∈ W →
      ∃ V : Opens Z'.toPresheafedSpace, b'.base x ∈ V ∧ (Opens.map b'.base).obj V ≤ W)
    (hx : Function.Bijective ((Z'.stalkFunctor (b'.base x)).map
      (pushforwardModulesBaseChange h G))) :
    Function.Bijective ((Y₂'.stalkFunctor x).map (pushforwardModulesBaseChange h₁ G)) := by
  rw [pushforwardModulesBaseChange_comp h₁ h₂ h] at hx
  exact b'.bijective_stalkFunctor_map_of_pushforward hb _
    ((Z'.stalkFunctor (b'.base x)).bijective_map_of_comp_right _ _ hx
      ((ConcreteCategory.isIso_iff_bijective _).1 ((Z'.stalkFunctor (b'.base x)).mapIso
        (asIso (pushforwardModulesBaseChange h₂
          ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G)))).isIso_hom))

end Comp

section Restrict

variable {Y Y' Ya Ya' V V' Va Va' : LocallyRingedSpace.{u}}
  {π : Y' ⟶ Y} {πa : Ya' ⟶ Ya} {gY : Ya ⟶ Y} {gY' : Ya' ⟶ Y'} (h : πa ≫ gY = gY' ≫ π)
  {πV : V' ⟶ V} {πVa : Va' ⟶ Va} {gV : Va ⟶ V} {gV' : Va' ⟶ V'} (hV : πVa ≫ gV = gV' ≫ πV)
  {u : V ⟶ Y} {ua : Va ⟶ Ya} (hu : ua ≫ gY = gV ≫ u)
  {u' : V' ⟶ Y'} {ua' : Va' ⟶ Ya'} (hu' : ua' ≫ gY' = gV' ≫ u')

include h hu hu' in
/-- **Base change morphisms can be tested on open subspaces.** Consider a commutative cube with
back face `h : πa ≫ gY = gY' ≫ π`, front face `hV : πVa ≫ gV = gV' ≫ πV`, and side faces
`hu : ua ≫ gY = gV ≫ u`, `hu' : ua' ≫ gY' = gV' ≫ u'` in which `u, ua, u', ua'` are open embeddings
with bijective stalk maps, such that `π⁻¹(u(V)) ⊆ u'(V')` and `πa⁻¹(ua(Va)) ⊆ ua'(Va')`. If the base
change morphism of the front face at `u'^* F` is bijective at `v`, then the base change morphism of
the back face at `F` is bijective at `ua v`. -/
theorem bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_restrict
    (w : πV ≫ u = u' ≫ π) (w' : πVa ≫ ua = ua' ≫ πa)
    (hu_o : IsOpenEmbedding u.base) [∀ x, IsIso (u.stalkMap x)]
    (hua_o : IsOpenEmbedding ua.base) [∀ x, IsIso (ua.stalkMap x)]
    (hu'_o : IsOpenEmbedding u'.base) [∀ x, IsIso (u'.stalkMap x)]
    (hua'_o : IsOpenEmbedding ua'.base) [∀ x, IsIso (ua'.stalkMap x)]
    (hc : ∀ z : Y', π.base z ∈ Set.range u.base → z ∈ Set.range u'.base)
    (hc' : ∀ z : Ya', πa.base z ∈ Set.range ua.base → z ∈ Set.range ua'.base)
    (F : SheafOfModules.{u} Y'.ringSheaf) (v : Va)
    (hv : Function.Bijective ((Va.stalkFunctor v).map
      (pushforwardModulesBaseChange hV (u'.pullbackModules.obj F)))) :
    Function.Bijective ((Ya.stalkFunctor (ua.base v)).map (pushforwardModulesBaseChange h F)) := by
  let FV := u'.pullbackModules.obj F
  let θ : F ⟶ (SheafOfModules.pushforward.{u} u'.toRingSheafHom).obj FV :=
    u'.pullbackModulesAdj.unit.app F
  let W : Opens Ya.toPresheafedSpace := ⟨Set.range ua.base, hua_o.isOpen_range⟩
  have hy : ua.base v ∈ W := ⟨v, rfl⟩
  have hgY : ∀ va : Va, gY.base (ua.base va) = u.base (gV.base va) := fun va ↦
    congrArg (fun k : Va ⟶ Y ↦ k.base va) hu
  have hπ : ∀ z : Ya', π.base (gY'.base z) = gY.base (πa.base z) := fun z ↦
    (congrArg (fun k : Ya' ⟶ Y ↦ k.base z) h).symm
  -- the unit `F ⟶ u'_* u'^* F` is bijective on the stalks at the points of `u'(V')`
  have hθ : ∀ z : Y', z ∈ Set.range u'.base → Function.Bijective ((Y'.stalkFunctor z).map θ) := by
    rintro _ ⟨z, rfl⟩
    exact u'.bijective_stalkFunctor_map_unit
      (fun W hW ↦ u'.exists_preimage_le_of_isInducing hu'_o.isInducing W hW) F
  have hθ' : ∀ z : Ya', πa.base z ∈ W →
      Function.Bijective ((Ya'.stalkFunctor z).map (gY'.pullbackModules.map θ)) := by
    intro z hz
    have hr : π.base (gY'.base z) ∈ Set.range u.base := by
      obtain ⟨va, hva⟩ := hz
      rw [hπ, ← hva, hgY]
      exact ⟨_, rfl⟩
    exact gY'.bijective_stalkFunctor_map_pullbackModules z θ (hθ (gY'.base z) (hc _ hr))
  -- the two vertical maps in the naturality square of base change along `θ`
  have h₁ : Function.Bijective ((Ya.stalkFunctor (ua.base v)).map
      ((SheafOfModules.pushforward.{u} πa.toRingSheafHom).map (gY'.pullbackModules.map θ))) :=
    πa.bijective_stalkFunctor_map_pushforward_of_forall _ W hθ' hy
  have h₂ : Function.Bijective ((Ya.stalkFunctor (ua.base v)).map
      (gY.pullbackModules.map ((SheafOfModules.pushforward.{u} π.toRingSheafHom).map θ))) := by
    refine gY.bijective_stalkFunctor_map_pullbackModules _ _
      (π.bijective_stalkFunctor_map_pushforward_of_forall θ
        ⟨Set.range u.base, hu_o.isOpen_range⟩ (fun z hz ↦ hθ z (hc z hz)) ?_)
    rw [hgY]
    exact ⟨_, rfl⟩
  -- base change along `u'` is bijective over `ua'(Va')`
  have h₃ : Function.Bijective ((Ya.stalkFunctor (ua.base v)).map
      ((SheafOfModules.pushforward.{u} πa.toRingSheafHom).map
        (pushforwardModulesBaseChange hu' FV))) := by
    refine πa.bijective_stalkFunctor_map_pushforward_of_forall _ W (fun z hz ↦ ?_) hy
    obtain ⟨z', rfl⟩ := hc' z hz
    exact bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding hu' hu'_o
      hua'_o FV z'
  -- the composite square through `V'`, `V`, `Y`
  have hc1 : (πVa ≫ ua) ≫ gY = gV' ≫ (πV ≫ u) := by
    rw [Category.assoc, hu, reassoc_of% hV]
  have hc₂ : (ua' ≫ πa) ≫ gY = gV' ≫ (u' ≫ π) := by
    rw [Category.assoc, h, reassoc_of% hu']
  have h₄ : Function.Bijective ((Ya.stalkFunctor (ua.base v)).map
      (pushforwardModulesBaseChange hc1 FV)) := by
    rw [pushforwardModulesBaseChange_comp hV hu hc1]
    exact (Ya.stalkFunctor (ua.base v)).bijective_map_comp _ _
      (bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding hu hu_o hua_o
        _ v)
      (ua.bijective_stalkFunctor_map_pushforward
        (fun W hW ↦ ua.exists_preimage_le_of_isInducing hua_o.isInducing W hW) _ hv)
  have h₅ := (bijective_stalkFunctor_map_pushforwardModulesBaseChange_congr w w' hc1
    hc₂ FV (ua.base v)).1 h₄
  rw [pushforwardModulesBaseChange_comp hu' h hc₂] at h₅
  have h₆ := (Ya.stalkFunctor (ua.base v)).bijective_map_of_comp_left _ _ h₅ h₃
  -- naturality of base change along `θ`
  have h₇ : Function.Bijective ((Ya.stalkFunctor (ua.base v)).map
      (pushforwardModulesBaseChange h F ≫
        (SheafOfModules.pushforward.{u} πa.toRingSheafHom).map (gY'.pullbackModules.map θ))) := by
    rw [pushforwardModulesBaseChange_naturality h θ]
    exact (Ya.stalkFunctor (ua.base v)).bijective_map_comp _ _ h₂ h₆
  exact (Ya.stalkFunctor (ua.base v)).bijective_map_of_comp_left _ _ h₇ h₁

end Restrict

end AlgebraicGeometry.LocallyRingedSpace

end
