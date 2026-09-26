/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp
public import Other.Oka.Topology.Sheaves.Cohomology.BaseChange

/-!
# The comparison map on cohomology and pushforward along closed embeddings

Consider a commutative square of locally ringed spaces

```
Y' --f'--> X'
|g'        |g
v          v
Y  --f-->  X
```

(`h : f' ≫ g = g' ≫ f`). For a sheaf of `𝒪_Y`-modules `G`, the base change morphism
`g^* f_* G ⟶ f'_* g'^* G` (`AlgebraicGeometry.LocallyRingedSpace.pushforwardModulesBaseChange`)
is the mate of the isomorphism `f'^* g^* ≅ g'^* f^*` of the square. The underlying abelian sheaf of
the pushforward `f_* G` of a sheaf of modules is the pushforward of the underlying abelian sheaf
(definitionally).

If `f` and `f'` are closed embeddings, the comparison maps `Hᵠ(Y, G) → Hᵠ(Y', g'^* G)` and
`Hᵠ(X, f_* G) → Hᵠ(X', g^* f_* G)` (`AlgebraicGeometry.LocallyRingedSpace.Hom.cohomologyMap`)
commute with the identifications `Hᵠ(Y, G) ≃ Hᵠ(X, f_* G)`, `Hᵠ(Y', g'^* G) ≃ Hᵠ(X', f'_* g'^* G)`
(`TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv`) up to the base change morphism
(`AlgebraicGeometry.LocallyRingedSpace.pushforwardClosedEmbeddingAddEquiv_cohomologyMap`).
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Topology

namespace CategoryTheory.Adjunction

variable {A : Type*} {B : Type*} {C : Type*} {D : Type*} [Category* A] [Category* B]
  [Category* C] [Category* D]
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lg : A ⥤ C} {Rg : C ⥤ A} {Lf' : C ⥤ D} {Rf' : D ⥤ C}
  {Lg' : B ⥤ D} {Rg' : D ⥤ B} (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjf' : Lf' ⊣ Rf')
  (adjg' : Lg' ⊣ Rg') (e : Lg ⋙ Lf' ⟶ Lf ⋙ Lg')

set_option backward.isDefEq.respectTransparency false in
/-- For a square of adjunctions and `e : Lg ⋙ Lf' ⟶ Lf ⋙ Lg'`, the base change morphism
`Lg Rf G ⟶ Rf' Lf' Lg Rf G ⟶ Rf' Lg' Lf Rf G ⟶ Rf' Lg' G` is adjoint (under `Lg ⊣ Rg`) to
`Rf G ⟶ Rf Rg' Lg' G ⟶ Rg Rf' Lg' G`, the second map being the conjugate of `e`. -/
lemma unit_comp_map_baseChange (G : B) :
    adjg.unit.app (Rf.obj G) ≫ Rg.map (adjf'.unit.app (Lg.obj (Rf.obj G)) ≫
        Rf'.map (e.app (Rf.obj G) ≫ Lg'.map (adjf.counit.app G))) =
      Rf.map (adjg'.unit.app G) ≫
        (conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') e).app (Lg'.obj G) := by
  have key := unit_conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') e (Rf.obj G)
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at key
  have nat := (conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') e).naturality
    (Lg'.map (adjf.counit.app G))
  simp only [Functor.comp_map] at nat
  have nat' := adjg'.unit.naturality (adjf.counit.app G)
  simp only [Functor.comp_map, Functor.id_map] at nat'
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, ← reassoc_of% key]
  erw [← nat]
  rw [← Functor.map_comp_assoc]
  erw [← nat']
  rw [Functor.map_comp_assoc, Adjunction.right_triangle_components_assoc]
  rfl

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y X' Y' : LocallyRingedSpace.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {g : X' ⟶ X}
  {g' : Y' ⟶ Y} (h : f' ≫ g = g' ≫ f)

include h in
/-- The underlying continuous maps of a commutative square of locally ringed spaces commute. -/
lemma base_comm_of_comm : f'.base ≫ g.base = g'.base ≫ f.base :=
  congrArg (fun k ↦ k.base) h

/-- **The base change morphism** `g^* f_* G ⟶ f'_* g'^* G` of sheaves of modules for a commutative
square `f' ≫ g = g' ≫ f` of locally ringed spaces: the composite of the unit of
`f'^* ⊣ f'_*` with `f'_*` of `f'^* g^* f_* G ≅ g'^* f^* f_* G ⟶ g'^* G`. -/
noncomputable def pushforwardModulesBaseChange (G : SheafOfModules.{u} Y.ringSheaf) :
    g.pullbackModules.obj ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) ⟶
      (SheafOfModules.pushforward.{u} f'.toRingSheafHom).obj (g'.pullbackModules.obj G) :=
  f'.pullbackModulesAdj.unit.app _ ≫
    (SheafOfModules.pushforward.{u} f'.toRingSheafHom).map
      ((Hom.pullbackModulesCommSqIso h).hom.app _ ≫
        g'.pullbackModules.map (f.pullbackModulesAdj.counit.app G))

/-- The morphism `f_* g'_* ⟶ g_* f'_*` of pushforwards of sheaves of modules conjugate to the
isomorphism `f'^* g^* ≅ g'^* f^*` of a commutative square. -/
noncomputable def pushforwardModulesCommSq :
    SheafOfModules.pushforward.{u} g'.toRingSheafHom ⋙
        SheafOfModules.pushforward.{u} f.toRingSheafHom ⟶
      SheafOfModules.pushforward.{u} f'.toRingSheafHom ⋙
        SheafOfModules.pushforward.{u} g.toRingSheafHom :=
  conjugateEquiv (f.pullbackModulesAdj.comp g'.pullbackModulesAdj)
    (g.pullbackModulesAdj.comp f'.pullbackModulesAdj) (Hom.pullbackModulesCommSqIso h).hom

/-- The base change morphism is adjoint to `f_*` of the unit of `g'^* ⊣ g'_*`, followed by
`f_* g'_* ⟶ g_* f'_*`. -/
lemma unit_comp_pushforward_map_pushforwardModulesBaseChange
    (G : SheafOfModules.{u} Y.ringSheaf) :
    g.pullbackModulesAdj.unit.app _ ≫
        (SheafOfModules.pushforward.{u} g.toRingSheafHom).map (pushforwardModulesBaseChange h G) =
      (SheafOfModules.pushforward.{u} f.toRingSheafHom).map (g'.pullbackModulesAdj.unit.app G) ≫
        (pushforwardModulesCommSq h).app (g'.pullbackModules.obj G) := by
  exact Adjunction.unit_comp_map_baseChange _ _ _ _ _ G

/-- The conjugate of the isomorphism `k^* ≅ k'^*` of pullbacks along equal morphisms is, on
underlying abelian sheaves, the identification of the pushforwards. -/
lemma modulesToAb_map_conjugateEquiv_pullbackModulesCongr_hom_app {k k' : Y' ⟶ X}
    (e : k = k') (M : SheafOfModules.{u} Y'.ringSheaf) :
    (modulesToAb X).map ((conjugateEquiv k'.pullbackModulesAdj k.pullbackModulesAdj
      (Hom.pullbackModulesCongr e).hom).app M) =
      eqToHom (by rw [e]) := by
  subst e
  simp [Hom.pullbackModulesCongr]

set_option maxHeartbeats 400000 in
-- The defeq checks between `(g' ≫ f)_*` and `f_* ∘ g'_*` on sheaves of modules are expensive.
/-- On underlying abelian sheaves, `f_* g'_* ⟶ g_* f'_*` is
`TopCat.Sheaf.pushforwardAbCommSqIso`. -/
lemma modulesToAb_map_pushforwardModulesCommSq_app (M : SheafOfModules.{u} Y'.ringSheaf) :
    (modulesToAb X).map ((pushforwardModulesCommSq h).app M) =
      (TopCat.Sheaf.pushforwardAbCommSqIso (base_comm_of_comm h)).hom.app M.toAb := by
  have hν : pushforwardModulesCommSq h =
      conjugateEquiv (f.pullbackModulesAdj.comp g'.pullbackModulesAdj)
          (g' ≫ f).pullbackModulesAdj (Hom.pullbackModulesComp g' f).inv ≫
        conjugateEquiv (g' ≫ f).pullbackModulesAdj (f' ≫ g).pullbackModulesAdj
          (Hom.pullbackModulesCongr h).hom ≫
        conjugateEquiv (f' ≫ g).pullbackModulesAdj
          (g.pullbackModulesAdj.comp f'.pullbackModulesAdj) (Hom.pullbackModulesComp f' g).hom := by
    rw [conjugateEquiv_comp, conjugateEquiv_comp]
    rfl
  have h₁ : conjugateEquiv (f.pullbackModulesAdj.comp g'.pullbackModulesAdj)
      (g' ≫ f).pullbackModulesAdj (Hom.pullbackModulesComp g' f).inv =
        (SheafOfModules.pushforwardComp.{u} f.toRingSheafHom g'.toRingSheafHom).hom :=
    SheafOfModules.conjugateEquiv_pullbackComp_inv f.toRingSheafHom g'.toRingSheafHom
  have h₃ : conjugateEquiv (g.pullbackModulesAdj.comp f'.pullbackModulesAdj)
      (f' ≫ g).pullbackModulesAdj (Hom.pullbackModulesComp f' g).inv =
        (SheafOfModules.pushforwardComp.{u} g.toRingSheafHom f'.toRingSheafHom).hom :=
    SheafOfModules.conjugateEquiv_pullbackComp_inv g.toRingSheafHom f'.toRingSheafHom
  have e₁ : (conjugateEquiv (f.pullbackModulesAdj.comp g'.pullbackModulesAdj)
      (g' ≫ f).pullbackModulesAdj (Hom.pullbackModulesComp g' f).inv).app M = 𝟙 _ := by
    rw [h₁]
    rfl
  have e₃ : (conjugateEquiv (f' ≫ g).pullbackModulesAdj
      (g.pullbackModulesAdj.comp f'.pullbackModulesAdj) (Hom.pullbackModulesComp f' g).hom).app M =
        𝟙 _ := by
    have := congrArg (fun τ ↦ τ.app M) (conjugateEquiv_comm
      (g.pullbackModulesAdj.comp f'.pullbackModulesAdj) (f' ≫ g).pullbackModulesAdj
      (Hom.pullbackModulesComp f' g).hom_inv_id)
    simp only [NatTrans.comp_app, h₃] at this
    exact (Category.id_comp _).symm.trans this
  rw [hν, NatTrans.comp_app, NatTrans.comp_app, e₁, e₃]
  erw [Category.id_comp, Category.comp_id]
  refine (modulesToAb_map_conjugateEquiv_pullbackModulesCongr_hom_app h M).trans ?_
  rw [TopCat.Sheaf.pushforwardAbCommSqIso, eqToIso.hom, eqToHom_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On underlying abelian sheaves, `g⁻¹ f_* G ⟶ g^* f_* G ⟶ f'_* g'^* G` is the base change
morphism of abelian sheaves followed by `f'_*` of `g'⁻¹ G ⟶ g'^* G`. -/
lemma toPullbackModules_comp_modulesToAb_map_pushforwardModulesBaseChange
    (G : SheafOfModules.{u} Y.ringSheaf) :
    g.toPullbackModules ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) ≫
        (modulesToAb X').map (pushforwardModulesBaseChange h G) =
      TopCat.Sheaf.pullbackPushforwardBaseChangeApp (base_comm_of_comm h) G.toAb ≫
        f'.pushforwardAb.map (g'.toPullbackModules G) := by
  apply ((Hom.pullbackAbAdj g).homEquiv _ _).injective
  let c := (TopCat.Sheaf.pushforwardAbCommSqIso (base_comm_of_comm h)).hom
  have L : (Hom.pullbackAbAdj g).homEquiv _ _
      (g.toPullbackModules ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) ≫
        (modulesToAb X').map (pushforwardModulesBaseChange h G)) =
      f.pushforwardAb.map ((modulesToAb Y).map (g'.pullbackModulesAdj.unit.app G)) ≫
        c.app (g'.pullbackModules.obj G).toAb := by
    rw [Adjunction.homEquiv_naturality_right, Hom.homEquiv_toPullbackModules]
    calc _ = (modulesToAb X).map (g.pullbackModulesAdj.unit.app _ ≫
          (SheafOfModules.pushforward.{u} g.toRingSheafHom).map
            (pushforwardModulesBaseChange h G)) := (Functor.map_comp _ _ _).symm
      _ = (modulesToAb X).map
          ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map
            (g'.pullbackModulesAdj.unit.app G) ≫
          (pushforwardModulesCommSq h).app (g'.pullbackModules.obj G)) :=
        congrArg (modulesToAb X).map (unit_comp_pushforward_map_pushforwardModulesBaseChange h G)
      _ = (modulesToAb X).map ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map
            (g'.pullbackModulesAdj.unit.app G)) ≫
          (modulesToAb X).map ((pushforwardModulesCommSq h).app (g'.pullbackModules.obj G)) :=
        Functor.map_comp _ _ _
      _ = _ := congrArg (fun t ↦ (modulesToAb X).map ((SheafOfModules.pushforward.{u}
            f.toRingSheafHom).map (g'.pullbackModulesAdj.unit.app G)) ≫ t)
          (modulesToAb_map_pushforwardModulesCommSq_app h (g'.pullbackModules.obj G))
  have R : (Hom.pullbackAbAdj g).homEquiv _ _
      (TopCat.Sheaf.pullbackPushforwardBaseChangeApp (base_comm_of_comm h) G.toAb ≫
        f'.pushforwardAb.map (g'.toPullbackModules G)) =
      f.pushforwardAb.map ((modulesToAb Y).map (g'.pullbackModulesAdj.unit.app G)) ≫
        c.app (g'.pullbackModules.obj G).toAb := by
    have hN := c.naturality (g'.toPullbackModules G)
    have hU : (TopCat.Sheaf.pullbackPushforwardAbAdj g'.base).unit.app G.toAb ≫
        g'.pushforwardAb.map (g'.toPullbackModules G) =
          (modulesToAb Y).map (g'.pullbackModulesAdj.unit.app G) := by
      rw [← Hom.homEquiv_toPullbackModules, Adjunction.homEquiv_unit]
    rw [Adjunction.homEquiv_naturality_right]
    erw [TopCat.Sheaf.homEquiv_pullbackPushforwardBaseChangeApp]
    rw [Category.assoc]
    erw [← hN]
    rw [← hU, Functor.map_comp, Category.assoc]
    rfl
  exact L.trans R.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The comparison map commutes with pushforward along closed embeddings**: for a commutative
square `f' ≫ g = g' ≫ f` of locally ringed spaces with `f`, `f'` closed embeddings, a sheaf of
modules `G` on `Y` and `x ∈ Hⁿ(Y, G)`, the image of `g'^*(x) ∈ Hⁿ(Y', g'^* G)` in
`Hⁿ(X', f'_* g'^* G)` is the image of `g^*(f_* x) ∈ Hⁿ(X', g^* f_* G)` under the base change
morphism. -/
theorem pushforwardClosedEmbeddingAddEquiv_cohomologyMap (hf : IsClosedEmbedding f.base)
    (hf' : IsClosedEmbedding f'.base) (G : SheafOfModules.{u} Y.ringSheaf) {n : ℕ} (x : H G n) :
    TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv hf' (g'.pullbackModules.obj G).toAb n
        (g'.cohomologyMap G n x) =
      H.map (pushforwardModulesBaseChange h G) n
        (g.cohomologyMap ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G) n
          (TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv hf G.toAb n x)) := by
  rw [Hom.cohomologyMap_apply, Hom.cohomologyMap_apply, H.map,
    ← TopCat.Sheaf.H.map_comp_apply,
    toPullbackModules_comp_modulesToAb_map_pushforwardModulesBaseChange,
    TopCat.Sheaf.H.map_comp_apply]
  exact (TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv_map hf' (g'.toPullbackModules G)
    (TopCat.Sheaf.H.pullback g'.base x)).trans (congrArg
      (TopCat.Sheaf.H.map ((TopCat.Sheaf.pushforwardAb f'.base).map (g'.toPullbackModules G)) n)
      (TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv_pullback (base_comm_of_comm h) hf hf'
        G.toAb x))

end AlgebraicGeometry.LocallyRingedSpace

end
