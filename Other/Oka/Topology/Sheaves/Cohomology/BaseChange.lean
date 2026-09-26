/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.Homology.DerivedCategory.Ext.MapNatTrans
public import Other.Oka.Topology.Sheaves.Cohomology.ClosedEmbedding

/-!
# Pullback of cohomology and pushforward along closed embeddings

Consider a commutative square of continuous maps

```
Y' --f'--> X'
|g'        |g
v          v
Y  --f-->  X
```

(`h : f' ≫ g = g' ≫ f`). The pushforwards along the two composites agree
(`TopCat.Sheaf.pushforwardAbCommSqIso h : g'_* ⋙ f_* ≅ f'_* ⋙ g_*`), and its mate is the base
change morphism of abelian sheaves

`TopCat.Sheaf.pullbackPushforwardBaseChange h : f_* ⋙ g⁻¹ ⟶ g'⁻¹ ⋙ f'_*`

(components `TopCat.Sheaf.pullbackPushforwardBaseChangeApp h F`).

If `f` and `f'` are closed embeddings, then the pullback maps on cohomology commute with the
identifications `Hⁿ(Y, G) ≃ Hⁿ(X, f_* G)` (`TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv`)
up to the base change morphism (`TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv_pullback`):
for `x ∈ Hⁿ(Y, G)`,

`f'_*(g'^* x) = β_G (g^* (f_* x))` in `Hⁿ(X', f'_* g'⁻¹ G)`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian Topology

namespace TopCat.Sheaf

/-- The adjunction `p⁻¹ ⊣ p_*` for abelian sheaves, typed with `TopCat.AbSheaf`. -/
noncomputable abbrev pullbackPushforwardAbAdj {S T : TopCat.{u}} (p : S ⟶ T) :
    pullbackAb p ⊣ pushforwardAb p :=
  pullbackPushforwardAdjunction AddCommGrpCat.{u} p

variable {X Y X' Y' : TopCat.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'} {g : X' ⟶ X} {g' : Y' ⟶ Y}
  (h : f' ≫ g = g' ≫ f)

/-- The pushforwards along the two composites of a commutative square of continuous maps agree:
`f_* g'_* ≅ g_* f'_*`. -/
noncomputable def pushforwardAbCommSqIso :
    pushforwardAb g' ⋙ pushforwardAb f ≅ pushforwardAb f' ⋙ pushforwardAb g :=
  eqToIso (by
    change pushforwardAb (g' ≫ f) = pushforwardAb (f' ≫ g)
    rw [h])

/-- On global sections, `f_* g'_* ≅ g_* f'_*` is the identity. -/
lemma pushforwardAbCommSqIso_hom_app_hom_app_top (F : AbSheaf Y') :
    ((pushforwardAbCommSqIso h).hom.app F).hom.app (op ⊤) = 𝟙 (F.obj.obj (op ⊤)) := by
  have key : ∀ (A B : AbSheaf X) (p : A = B), (eqToHom p).hom.app (op ⊤) =
      eqToHom (congrArg (fun C : AbSheaf X ↦ C.obj.obj (op ⊤)) p) := by
    rintro _ _ rfl
    rfl
  rw [pushforwardAbCommSqIso, eqToIso.hom, eqToHom_app]
  exact (key _ _ _).trans (eqToHom_refl _ _)

/-- The component at `F` of the base change morphism `g⁻¹ f_* F ⟶ f'_* g'⁻¹ F`. -/
noncomputable def pullbackPushforwardBaseChangeApp (F : AbSheaf Y) :
    (pullbackAb g).obj ((pushforwardAb f).obj F) ⟶ (pushforwardAb f').obj ((pullbackAb g').obj F) :=
  ((pullbackPushforwardAbAdj g).homEquiv _ _).symm
    ((pushforwardAb f).map ((pullbackPushforwardAbAdj g').unit.app F) ≫
      (pushforwardAbCommSqIso h).hom.app _)

@[reassoc]
lemma pullbackPushforwardBaseChangeApp_naturality {F F' : AbSheaf Y} (φ : F ⟶ F') :
    (pullbackAb g).map ((pushforwardAb f).map φ) ≫ pullbackPushforwardBaseChangeApp h F' =
      pullbackPushforwardBaseChangeApp h F ≫ (pushforwardAb f').map ((pullbackAb g').map φ) := by
  apply ((pullbackPushforwardAbAdj g).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackPushforwardBaseChangeApp, pullbackPushforwardBaseChangeApp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have e₁ := (pushforwardAbCommSqIso h).hom.naturality ((pullbackAb g').map φ)
  have e₂ := (pullbackPushforwardAbAdj g').unit.naturality φ
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at e₁ e₂
  rw [← Functor.map_comp_assoc]
  erw [e₂]
  rw [Functor.map_comp_assoc]
  erw [e₁]
  rfl

/-- **The base change morphism** `g⁻¹ f_* ⟶ f'_* g'⁻¹` of a commutative square
`f' ≫ g = g' ≫ f` of continuous maps: the mate of `f_* g'_* ≅ g_* f'_*`. -/
@[simps]
noncomputable def pullbackPushforwardBaseChange :
    pushforwardAb f ⋙ pullbackAb g ⟶ pullbackAb g' ⋙ pushforwardAb f' where
  app F := pullbackPushforwardBaseChangeApp h F
  naturality _ _ φ := pullbackPushforwardBaseChangeApp_naturality h φ

/-- The adjoint of `g⁻¹ f_* F ⟶ f'_* g'⁻¹ F` under `g⁻¹ ⊣ g_*` is `f_*` of the unit of
`g'⁻¹ ⊣ g'_*` followed by `f_* g'_* ≅ g_* f'_*`. -/
lemma homEquiv_pullbackPushforwardBaseChangeApp (F : AbSheaf Y) :
    (pullbackPushforwardAbAdj g).homEquiv _ _
        (pullbackPushforwardBaseChangeApp h F) =
      (pushforwardAb f).map ((pullbackPushforwardAbAdj g').unit.app F) ≫
        (pushforwardAbCommSqIso h).hom.app _ :=
  Equiv.apply_symm_apply _ _

section ConstZ

variable {S T : TopCat.{u}} (p : S ⟶ T)

/-- The adjoint of `ℤ_T ≅ p⁻¹ ℤ_S` (inverse of `TopCat.Sheaf.pullbackConstZIso`) under
`ℤ_T ⊣ Γ(T, -)` is the unit of `p⁻¹ ℤ_S ⊣ Γ(S, p_* -)`. -/
lemma constantSheafAdj_homEquiv_pullbackConstZIso_inv :
    (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop).homEquiv
        _ _ (pullbackConstZIso p).inv =
      ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{u} isTerminalTop).comp
        (pullbackPushforwardAdjunction AddCommGrpCat.{u} p)).unit.app
          (AddCommGrpCat.of (ULift ℤ)) :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _

/-- The adjoint of `ℤ_T ⟶ p_* ℤ_S` under `ℤ_T ⊣ Γ(T, -)` is the unit of `ℤ_S ⊣ Γ(S, -)`. -/
lemma constantSheafAdj_homEquiv_constZToPushforward :
    (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{u} isTerminalTop).homEquiv
        _ _ (constZToPushforward p) =
      (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop).unit.app
        (AddCommGrpCat.of (ULift ℤ)) := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{u} isTerminalTop).comp
      (pullbackPushforwardAdjunction AddCommGrpCat.{u} p))
    (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop)
    (AddCommGrpCat.of (ULift ℤ))
  rw [Adjunction.comp_homEquiv] at this
  exact this

/-- The adjoint of `ℤ_S ≅ p⁻¹ ℤ_T ⟶ M` under `ℤ_S ⊣ Γ(S, -)` is the adjoint of
`p⁻¹ ℤ_T ⟶ M` under `p⁻¹ ⊣ p_*` and `ℤ_T ⊣ Γ(T, -)`. -/
lemma constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp {M : AbSheaf S}
    (m : (pullbackAb p).obj (constZ T) ⟶ M) :
    (constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop).homEquiv
        _ _ ((pullbackConstZIso p).inv ≫ m) =
      (constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{u} isTerminalTop).homEquiv
        _ _ ((pullbackPushforwardAbAdj p).homEquiv _ _ m) := by
  rw [Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_pullbackConstZIso_inv]
  have := ((constantSheafAdj (Opens.grothendieckTopology T) AddCommGrpCat.{u}
    isTerminalTop).comp (pullbackPushforwardAdjunction AddCommGrpCat.{u} p)).homEquiv_unit
      (AddCommGrpCat.of (ULift ℤ)) M m
  rw [Adjunction.comp_homEquiv] at this
  exact this.symm

end ConstZ

/-- The base change morphism is compatible with the canonical morphisms `ℤ ⟶ p_* ℤ`. -/
lemma constZToPushforward_comp_pushforwardAb_map_pullbackConstZIso_inv :
    constZToPushforward f' ≫ (pushforwardAb f').map (pullbackConstZIso g').inv =
      (pullbackConstZIso g).inv ≫ (pullbackAb g).map (constZToPushforward f) ≫
        pullbackPushforwardBaseChangeApp h (constZ Y) := by
  let A := fun (S : TopCat.{u}) ↦
    constantSheafAdj (Opens.grothendieckTopology S) AddCommGrpCat.{u} isTerminalTop
  apply ((A X').homEquiv _ _).injective
  have lhs : (A X').homEquiv _ _
      (constZToPushforward f' ≫ (pushforwardAb f').map (pullbackConstZIso g').inv) =
      ((A Y).comp (pullbackPushforwardAdjunction AddCommGrpCat.{u} g')).unit.app
        (AddCommGrpCat.of (ULift ℤ)) := by
    rw [Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_constZToPushforward,
      ← constantSheafAdj_homEquiv_pullbackConstZIso_inv, Adjunction.homEquiv_unit]
    rfl
  obtain ⟨u, hu⟩ : ∃ u : constZ Y ⟶ (pushforwardAb g').obj ((pullbackAb g').obj (constZ Y)),
      u = (pullbackPushforwardAbAdj g').unit.app _ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : (pushforwardAb f).obj ((pushforwardAb g').obj
      ((pullbackAb g').obj (constZ Y))) ⟶
        (pushforwardAb g).obj ((pushforwardAb f').obj ((pullbackAb g').obj (constZ Y))),
      c = (pushforwardAbCommSqIso h).hom.app _ := ⟨_, rfl⟩
  have hc' : c.hom.app (op ⊤) = 𝟙 _ := hc ▸ pushforwardAbCommSqIso_hom_app_hom_app_top h _
  have hβ : (pullbackPushforwardAbAdj g).homEquiv _ _
      ((pullbackAb g).map (constZToPushforward f) ≫ pullbackPushforwardBaseChangeApp h (constZ Y)) =
      constZToPushforward f ≫ (pushforwardAb f).map u ≫ c := by
    rw [Adjunction.homEquiv_naturality_left, homEquiv_pullbackPushforwardBaseChangeApp, hu, hc]
    rfl
  have rhs : (A X').homEquiv _ _ ((pullbackConstZIso g).inv ≫ (pullbackAb g).map
      (constZToPushforward f) ≫ pullbackPushforwardBaseChangeApp h (constZ Y)) =
      ((A Y).comp (pullbackPushforwardAdjunction AddCommGrpCat.{u} g')).unit.app
        (AddCommGrpCat.of (ULift ℤ)) := by
    rw [constantSheafAdj_homEquiv_pullbackConstZIso_inv_comp, hβ,
      Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_constZToPushforward,
      Adjunction.comp_unit_app]
    congr 1
    change ((pushforwardAb f).map u ≫ c).hom.app (op ⊤) = _
    rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, hc', hu]
    exact Category.comp_id _
  rw [lhs, rhs]

/-- `Hⁿ(Y, G) ≃ Hⁿ(X, f_* G)` is natural in `G`. -/
lemma H.pushforwardClosedEmbeddingAddEquiv_map (hf : IsClosedEmbedding f) {G G' : AbSheaf Y}
    (φ : G ⟶ G') {n : ℕ} (x : H G n) :
    H.pushforwardClosedEmbeddingAddEquiv hf G' n (H.map φ n x) =
      H.map ((pushforwardAb f).map φ) n (H.pushforwardClosedEmbeddingAddEquiv hf G n x) := by
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).1
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).2
  change (Ext.mk₀ (constZToPushforward f)).comp ((x.comp (Ext.mk₀ φ) (add_zero n)).mapExactFunctor
      (pushforwardAb f)) (zero_add n) =
    ((Ext.mk₀ (constZToPushforward f)).comp (x.mapExactFunctor (pushforwardAb f)) (zero_add n)).comp
      (Ext.mk₀ ((pushforwardAb f).map φ)) (add_zero n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- **Pullback of cohomology commutes with pushforward along closed embeddings**: for a
commutative square `f' ≫ g = g' ≫ f` with `f`, `f'` closed embeddings and `x ∈ Hⁿ(Y, G)`, the
class `f'_*(g'^* x) ∈ Hⁿ(X', f'_* g'⁻¹ G)` is the image of `g^*(f_* x) ∈ Hⁿ(X', g⁻¹ f_* G)` under
the base change morphism. -/
theorem H.pushforwardClosedEmbeddingAddEquiv_pullback (hf : IsClosedEmbedding f)
    (hf' : IsClosedEmbedding f') (G : AbSheaf Y) {n : ℕ} (x : H G n) :
    H.pushforwardClosedEmbeddingAddEquiv hf' _ n (H.pullback g' x) =
      H.map (pullbackPushforwardBaseChangeApp h G) n
        (H.pullback g (H.pushforwardClosedEmbeddingAddEquiv hf G n x)) := by
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).1
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf).2
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf').1
  haveI := (preservesFiniteLimitsAndColimits_pushforwardAb hf').2
  have e : ∀ {S T : TopCat.{u}} {p : S ⟶ T} (hp : IsClosedEmbedding p) (F : AbSheaf S)
      [PreservesFiniteLimits (pushforwardAb p)] [PreservesFiniteColimits (pushforwardAb p)]
      (y : H F n), H.pushforwardClosedEmbeddingAddEquiv hp F n y =
        (Ext.mk₀ (constZToPushforward p)).comp (y.mapExactFunctor (pushforwardAb p))
          (zero_add n) := fun _ _ _ _ _ ↦ rfl
  have nat := Ext.mapExactFunctor_mapExactFunctor_comp_mk₀ (Φ₁ := pushforwardAb f)
    (Φ₂ := pullbackAb g) (Ψ₁ := pullbackAb g') (Ψ₂ := pushforwardAb f')
    (pullbackPushforwardBaseChangeApp h) (pullbackPushforwardBaseChangeApp_naturality h) x
  rw [e, e, H.pullback, H.pullback, H.mapOfExact_apply, H.mapOfExact_apply, H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, nat, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    constZToPushforward_comp_pushforwardAb_map_pullbackConstZIso_inv h, Category.assoc]

end TopCat.Sheaf

end
