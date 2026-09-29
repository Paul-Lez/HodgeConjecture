/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyBaseChange
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkLocal

/-!
# Functoriality of the base change morphism of sheaves of modules

For a commutative square `f' ≫ g = g' ≫ f` of locally ringed spaces

```
Y' --f'--> X'
|g'        |g
v          v
Y  --f-->  X
```

and a sheaf of `𝒪_Y`-modules `G`, let `β_G : g^* f_* G ⟶ f'_* g'^* G` be the base change morphism
`AlgebraicGeometry.LocallyRingedSpace.pushforwardModulesBaseChange`. We show:

* `pushforwardModulesBaseChange_app_unit`: for `s ∈ Γ(f⁻¹ U, G) = Γ(U, f_* G)`, `β_G` sends the
  pullback `g^* s` of `s` to the pullback `g'^* s`, transported along
  `f'⁻¹ g⁻¹ U = g'⁻¹ f⁻¹ U`;
* `pushforwardModulesBaseChange_naturality`: `β_G` is natural in `G`;
* `pushforwardModulesBaseChange_comp`: `β` is compatible with pasting squares horizontally;
* `bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_isOpenEmbedding`: if `f` and `f'`
  are open embeddings with bijective stalk maps, `β_G` is bijective on the stalks at the points of
  the image of `f'`.

We also record some facts on stalks: pullback preserves stalkwise bijectivity
(`Hom.bijective_stalkFunctor_map_pullbackModules`), the counit `f^* f_* G ⟶ G` is bijective at
the points near which `f` is an open embedding with bijective stalk maps
(`Hom.bijective_stalkFunctor_map_counit`), and a morphism which is bijective on the stalks at the
points of an open `U` is bijective on the sections over `U`
(`bijective_app_of_bijective_stalkFunctor_map`).
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Two restriction maps of a sheaf of modules compose to the restriction map. -/
lemma val_map_map_apply {Y : LocallyRingedSpace.{u}} (M : SheafOfModules.{u} Y.ringSheaf)
    {V₁ V₂ V₃ : (Opens Y.toPresheafedSpace)ᵒᵖ} (i₁ : V₁ ⟶ V₂) (i₂ : V₂ ⟶ V₃) (i₃ : V₁ ⟶ V₃)
    (y : M.val.obj V₁) :
    M.val.map i₂ (M.val.map i₁ y) = M.val.map i₃ y := by
  change M.val.presheaf.map i₂ (M.val.presheaf.map i₁ y) = M.val.presheaf.map i₃ y
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun i ↦ M.val.presheaf.map i y) (Subsingleton.elim _ _)

section Square

variable {X Y X' Y' : LocallyRingedSpace.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {g : X' ⟶ X}
  {g' : Y' ⟶ Y} (h : f' ≫ g = g' ≫ f)

include h in
lemma preimage_comm_of_comm (U : Opens X.toPresheafedSpace) :
    (Opens.map f'.base).obj ((Opens.map g.base).obj U) =
      (Opens.map g'.base).obj ((Opens.map f.base).obj U) :=
  congrArg (fun k : Y' ⟶ X ↦ (Opens.map k.base).obj U) h

/-- On sections, `f_* g'_* ⟶ g_* f'_*` is restriction along `f'⁻¹ g⁻¹ U = g'⁻¹ f⁻¹ U`. -/
lemma pushforwardModulesCommSq_app_val_app (M : SheafOfModules.{u} Y'.ringSheaf)
    (U : Opens X.toPresheafedSpace)
    (s : M.val.obj (op ((Opens.map g'.base).obj ((Opens.map f.base).obj U)))) :
    ((pushforwardModulesCommSq h).app M).val.app (op U) s =
      M.val.map (eqToHom (preimage_comm_of_comm h U)).op s := by
  have := congrArg (fun φ ↦ φ.hom.app (op U) s)
    (modulesToAb_map_pushforwardModulesCommSq_app h M)
  simp only [modulesToAb_map_hom_app_apply] at this
  rw [this]
  have key : ∀ (A B : TopCat.AbSheaf X.toPresheafedSpace) (p : A = B),
      (eqToHom p).hom.app (op U) =
        eqToHom (congrArg (fun C : TopCat.AbSheaf X.toPresheafedSpace ↦ C.obj.obj (op U)) p) := by
    rintro _ _ rfl
    rfl
  rw [TopCat.Sheaf.pushforwardAbCommSqIso, eqToIso.hom, eqToHom_app, key]
  change _ = (M.val.presheaf.map (eqToHom (preimage_comm_of_comm h U)).op) s
  rw [eqToHom_op, eqToHom_map]
  rfl

/-- The morphism `f_* G ⟶ g_* f'_* g'^* G` adjoint to the base change morphism sends a section
`s` to `g'^* s`, transported along `f'⁻¹ g⁻¹ U = g'⁻¹ f⁻¹ U`. -/
lemma homEquiv_pushforwardModulesBaseChange_val_app (G : SheafOfModules.{u} Y.ringSheaf)
    (U : Opens X.toPresheafedSpace) (s : G.val.obj (op ((Opens.map f.base).obj U))) :
    ((g.pullbackModulesAdj.homEquiv _ _) (pushforwardModulesBaseChange h G)).val.app (op U) s =
      (g'.pullbackModules.obj G).val.map (eqToHom (preimage_comm_of_comm h U)).op
        ((g'.pullbackModulesAdj.unit.app G).val.app (op ((Opens.map f.base).obj U)) s) := by
  rw [Adjunction.homEquiv_unit]
  have h1 : ((g.pullbackModulesAdj.unit.app _ ≫
        (SheafOfModules.pushforward.{u} g.toRingSheafHom).map
          (pushforwardModulesBaseChange h G)).val.app (op U) s) =
      (((SheafOfModules.pushforward.{u} f.toRingSheafHom).map (g'.pullbackModulesAdj.unit.app G) ≫
        (pushforwardModulesCommSq h).app (g'.pullbackModules.obj G)).val.app (op U) s) :=
    congrArg (fun φ ↦ φ.val.app (op U) s)
      (unit_comp_pushforward_map_pushforwardModulesBaseChange h G)
  exact h1.trans (pushforwardModulesCommSq_app_val_app h (g'.pullbackModules.obj G) U
    ((g'.pullbackModulesAdj.unit.app G).val.app (op ((Opens.map f.base).obj U)) s))

/-- **The base change morphism on pulled back sections**: `g^* f_* G ⟶ f'_* g'^* G` sends the
pullback of `s ∈ Γ(U, f_* G) = Γ(f⁻¹ U, G)` to the pullback of `s` along `g'`, transported along
`f'⁻¹ g⁻¹ U = g'⁻¹ f⁻¹ U`. -/
lemma pushforwardModulesBaseChange_app_unit (G : SheafOfModules.{u} Y.ringSheaf)
    (U : Opens X.toPresheafedSpace) (s : G.val.obj (op ((Opens.map f.base).obj U))) :
    (pushforwardModulesBaseChange h G).val.app (op ((Opens.map g.base).obj U))
        ((g.pullbackModulesAdj.unit.app ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj
          G)).val.app (op U) s) =
      (g'.pullbackModules.obj G).val.map (eqToHom (preimage_comm_of_comm h U)).op
        ((g'.pullbackModulesAdj.unit.app G).val.app (op ((Opens.map f.base).obj U)) s) :=
  homEquiv_pushforwardModulesBaseChange_val_app h G U s

/-- **The base change morphism is natural** in the sheaf of modules. -/
lemma pushforwardModulesBaseChange_naturality {G G' : SheafOfModules.{u} Y.ringSheaf}
    (φ : G ⟶ G') :
    pushforwardModulesBaseChange h G ≫
        (SheafOfModules.pushforward.{u} f'.toRingSheafHom).map (g'.pullbackModules.map φ) =
      g.pullbackModules.map ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map φ) ≫
        pushforwardModulesBaseChange h G' := by
  apply (g.pullbackModulesAdj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  ext ⟨U⟩ x
  change (g'.pullbackModules.map φ).val.app _
      (((g.pullbackModulesAdj.homEquiv _ _) (pushforwardModulesBaseChange h G)).val.app (op U) x) =
    ((g.pullbackModulesAdj.homEquiv _ _) (pushforwardModulesBaseChange h G')).val.app (op U)
      (φ.val.app _ x)
  rw [homEquiv_pushforwardModulesBaseChange_val_app, homEquiv_pushforwardModulesBaseChange_val_app]
  have hn := congrArg (fun ψ ↦ ψ.val.app (op ((Opens.map f.base).obj U)) x)
    (g'.pullbackModulesAdj.unit.naturality φ)
  change (g'.pullbackModulesAdj.unit.app G').val.app _ (φ.val.app _ x) =
    (g'.pullbackModules.map φ).val.app _ ((g'.pullbackModulesAdj.unit.app G).val.app _ x) at hn
  erw [hn]
  exact congrArg (fun ψ ↦ ψ.hom ((g'.pullbackModulesAdj.unit.app G).val.app _ x))
    ((g'.pullbackModules.map φ).val.naturality (eqToHom (preimage_comm_of_comm h U)).op)

end Square

section Comp

variable {Y₁ Y₂ Z Y₁' Y₂' Z' : LocallyRingedSpace.{u}} {a : Y₁ ⟶ Y₂} {b : Y₂ ⟶ Z}
  {a' : Y₁' ⟶ Y₂'} {b' : Y₂' ⟶ Z'} {g₁ : Y₁' ⟶ Y₁} {g₂ : Y₂' ⟶ Y₂} {g : Z' ⟶ Z}
  (h₁ : a' ≫ g₂ = g₁ ≫ a) (h₂ : b' ≫ g = g₂ ≫ b) (h : (a' ≫ b') ≫ g = g₁ ≫ (a ≫ b))

/-- **The base change morphism is compatible with pasting squares**: the base change morphism of
the composite square is the base change morphism of the right square at `a_* G`, followed by
`b'_*` of the base change morphism of the left square. -/
lemma pushforwardModulesBaseChange_comp (G : SheafOfModules.{u} Y₁.ringSheaf) :
    pushforwardModulesBaseChange h G =
      pushforwardModulesBaseChange h₂ ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G) ≫
        (SheafOfModules.pushforward.{u} b'.toRingSheafHom).map
          (pushforwardModulesBaseChange h₁ G) := by
  apply (g.pullbackModulesAdj.homEquiv ((SheafOfModules.pushforward.{u} b.toRingSheafHom).obj
    ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G))
    ((SheafOfModules.pushforward.{u} b'.toRingSheafHom).obj
      ((SheafOfModules.pushforward.{u} a'.toRingSheafHom).obj
        (g₁.pullbackModules.obj G)))).injective
  erw [Adjunction.homEquiv_naturality_right]
  ext ⟨U⟩ x
  change ((g.pullbackModulesAdj.homEquiv _ _) (pushforwardModulesBaseChange h G)).val.app (op U) x =
    (pushforwardModulesBaseChange h₁ G).val.app _
      (((g.pullbackModulesAdj.homEquiv _ _) (pushforwardModulesBaseChange h₂
        ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G))).val.app (op U) x)
  rw [homEquiv_pushforwardModulesBaseChange_val_app, homEquiv_pushforwardModulesBaseChange_val_app]
  have hn := congrArg (fun ψ ↦ ψ.hom ((g₂.pullbackModulesAdj.unit.app _).val.app _ x))
    ((pushforwardModulesBaseChange h₁ G).val.naturality
      (eqToHom (preimage_comm_of_comm h₂ U)).op)
  dsimp only at hn
  erw [hn]
  change _ = ((g₁.pullbackModules.obj G).val.map _)
    ((pushforwardModulesBaseChange h₁ G).val.app (op ((Opens.map g₂.base).obj
      ((Opens.map b.base).obj U))) ((g₂.pullbackModulesAdj.unit.app
        ((SheafOfModules.pushforward.{u} a.toRingSheafHom).obj G)).val.app
          (op ((Opens.map b.base).obj U)) x))
  rw [pushforwardModulesBaseChange_app_unit h₁ G]
  exact (val_map_map_apply (g₁.pullbackModules.obj G) (eqToHom (preimage_comm_of_comm h₁ _)).op
    ((Opens.map a'.base).op.map (eqToHom (preimage_comm_of_comm h₂ U)).op)
    (eqToHom (preimage_comm_of_comm h U)).op _).symm

end Comp

/-- Stalkwise bijectivity of base change morphisms of squares with the same vertical maps and
equal horizontal maps. -/
lemma bijective_stalkFunctor_map_pushforwardModulesBaseChange_congr
    {X Y X' Y' : LocallyRingedSpace.{u}} {f₁ f₂ : Y ⟶ X} {f₁' f₂' : Y' ⟶ X'} {g : X' ⟶ X}
    {g' : Y' ⟶ Y} (e : f₁ = f₂) (e' : f₁' = f₂') (h₁ : f₁' ≫ g = g' ≫ f₁) (h₂ : f₂' ≫ g = g' ≫ f₂)
    (G : SheafOfModules.{u} Y.ringSheaf) (x : X') :
    Function.Bijective ((X'.stalkFunctor x).map (pushforwardModulesBaseChange h₁ G)) ↔
      Function.Bijective ((X'.stalkFunctor x).map (pushforwardModulesBaseChange h₂ G)) := by
  subst e e'
  rfl

end AlgebraicGeometry.LocallyRingedSpace

end
