/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ClosedImmersionPushforward
public import Other.Oka.Analytification.GAGA.OpenImmersion
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PushforwardBaseChangeLocal

/-!
# Locality of the analytic base change morphism

For a morphism `π : Y' ⟶ Y` of schemes locally of finite type over `ℂ` and a sheaf of modules `G`
on `Y'`, let `β_G : (π_* G)^an ⟶ (π^an)_* G^an` be the base change morphism
`ComplexAnalytic.analytificationPushforwardBaseChange π G`. We show that bijectivity of `β_G` on
stalks can be checked locally:

* **composition with closed immersions**: if `ι` is a closed immersion, `β` for `ι ≫ p` at `G` is
  `β` for `p` at `ι_* G`, followed by an isomorphism
  (`ComplexAnalytic.bijective_bcStalk_comp`); and if `k` is
  a closed immersion, `β` for `π` is bijective at `y` if `β` for `π ≫ k` is bijective at `k^an y`
  (`ComplexAnalytic.bijective_bcStalk_of_comp`);
* **restriction to opens**: if `u : V ⟶ Y` and `u' : V' ⟶ Y'` are open immersions with
  `π_V ≫ u = u' ≫ π` and `π⁻¹(u(V)) ⊆ u'(V')`, then `β` for `π` at `G` is bijective at `u^an v`
  if `β` for `π_V` at `u'^* G` is bijective at `v`
  (`ComplexAnalytic.bijective_bcStalk_of_isOpenImmersion`).

The proofs combine the compatibility of base change morphisms with pasting of squares
(`AlgebraicGeometry.LocallyRingedSpace.pushforwardModulesBaseChange_comp`), the fact that base
change is an isomorphism along closed immersions
(`ComplexAnalytic.isIso_analytificationPushforwardBaseChange`) and bijective on stalks along open
immersions, see
`Other/Oka/Geometry/RingedSpace/LocallyRingedSpace/PushforwardBaseChangeLocal.lean`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite Topology
open AlgebraicGeometry.LocallyRingedSpace

universe u

noncomputable section

namespace ComplexAnalytic

variable {X Y Z : SchemeLFTℂ.{u}}

/-- The stalk at `y ∈ Y^an` of the base change morphism `(π_* G)^an ⟶ (π^an)_* G^an`. -/
abbrev bcStalk (π : X ⟶ Y) (G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    (y : analytification.obj Y) :=
  ((analytification.obj Y).toLocallyRingedSpace.stalkFunctor y).map
    (analytificationPushforwardBaseChange π G)

/-- The base change morphism is the base change morphism of the square of comparison morphisms. -/
lemma analytificationPushforwardBaseChange_eq (π : X ⟶ Y)
    (G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) :
    analytificationPushforwardBaseChange π G =
      pushforwardModulesBaseChange (analytificationπLRS_naturality π) G :=
  rfl

/-- The base change morphism is an isomorphism if and only if it is bijective on all stalks. -/
lemma isIso_analytificationPushforwardBaseChange_iff (π : X ⟶ Y)
    (G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) :
    IsIso (analytificationPushforwardBaseChange π G) ↔ ∀ y, Function.Bijective (bcStalk π G y) :=
  ⟨fun _ _ ↦ (ConcreteCategory.isIso_iff_bijective _).1 inferInstance,
    fun h ↦ isIso_of_bijective_stalkFunctor_map _ h⟩

/-- Bijectivity of base change morphisms on stalks is invariant under isomorphisms of sheaves. -/
lemma bijective_bcStalk_iff_of_iso (π : X ⟶ Y)
    {M M' : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} (e : M ≅ M')
    (y : analytification.obj Y) :
    Function.Bijective (bcStalk π M y) ↔ Function.Bijective (bcStalk π M' y) := by
  have hnat := pushforwardModulesBaseChange_naturality (analytificationπLRS_naturality π) e.hom
  let F := (analytification.obj Y).toLocallyRingedSpace.stalkFunctor y
  have h₁ : Function.Bijective (F.map ((analytificationπLRS Y).pullbackModules.map
      ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).map e.hom))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  have h₂ : Function.Bijective (F.map
      ((SheafOfModules.pushforward.{u} (analytification.map π).toLRSHom.toRingSheafHom).map
        ((analytificationπLRS X).pullbackModules.map e.hom))) :=
    (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  rw [bcStalk, bcStalk, analytificationPushforwardBaseChange_eq,
    analytificationPushforwardBaseChange_eq]
  have hb := congrArg (fun φ ↦ Function.Bijective (F.map φ)) hnat
  constructor
  · intro h
    exact F.bijective_map_of_comp_right _ _ (Eq.mp hb (F.bijective_map_comp _ _ h h₂)) h₁
  · intro h
    exact F.bijective_map_of_comp_left _ _ (Eq.mpr hb (F.bijective_map_comp _ _ h₁ h)) h₂

section Comp

variable (a : X ⟶ Y) (b : Y ⟶ Z) (G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)

lemma analytificationπLRS_comp_naturality :
    ((analytification.map a).toLRSHom ≫ (analytification.map b).toLRSHom) ≫
      analytificationπLRS Z = analytificationπLRS X ≫ (a.hom.left.toLRSHom ≫ b.hom.left.toLRSHom) :=
  by rw [Category.assoc, analytificationπLRS_naturality b,
    reassoc_of% (analytificationπLRS_naturality a)]

/-- The base change morphism of `a ≫ b` is the base change morphism of the pasted square. -/
lemma bijective_bcStalk_comp_iff (z : analytification.obj Z) :
    Function.Bijective (bcStalk (a ≫ b) G z) ↔
      Function.Bijective (((analytification.obj Z).toLocallyRingedSpace.stalkFunctor z).map
        (pushforwardModulesBaseChange (analytificationπLRS_comp_naturality a b) G)) :=
  bijective_stalkFunctor_map_pushforwardModulesBaseChange_congr rfl
    (by rw [Functor.map_comp]; rfl) (analytificationπLRS_naturality (a ≫ b)) _ G z

/-- If `a` is a closed immersion and the base change morphism of `b` at `a_* G` is bijective at
`z`, so is the base change morphism of `a ≫ b` at `G`. -/
lemma bijective_bcStalk_comp [IsClosedImmersion a.hom.left] (z : analytification.obj Z)
    (h : Function.Bijective (bcStalk b
      ((SheafOfModules.pushforward.{u} a.hom.left.toLRSHom.toRingSheafHom).obj G) z)) :
    Function.Bijective (bcStalk (a ≫ b) G z) := by
  haveI : IsIso (pushforwardModulesBaseChange (analytificationπLRS_naturality a) G) :=
    isIso_analytificationPushforwardBaseChange a G
  exact (bijective_bcStalk_comp_iff a b G z).2
    (bijective_stalkFunctor_map_pushforwardModulesBaseChange_comp_of_isIso
      (analytificationπLRS_naturality a) (analytificationπLRS_naturality b) _ G z h)

/-- If `b` is a closed immersion and the base change morphism of `a ≫ b` at `G` is bijective at
`b^an y`, then the base change morphism of `a` at `G` is bijective at `y`. -/
lemma bijective_bcStalk_of_comp [IsClosedImmersion b.hom.left] (y : analytification.obj Y)
    (h : Function.Bijective (bcStalk (a ≫ b) G ((analytification.map b).toLRSHom.base y))) :
    Function.Bijective (bcStalk a G y) := by
  haveI : IsIso (pushforwardModulesBaseChange (analytificationπLRS_naturality b)
      ((SheafOfModules.pushforward.{u} a.hom.left.toLRSHom.toRingSheafHom).obj G)) :=
    isIso_analytificationPushforwardBaseChange b _
  exact bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_comp
    (analytificationπLRS_naturality a) (analytificationπLRS_naturality b) _ G
    (fun W hW ↦ (analytification.map b).toLRSHom.exists_preimage_le_of_isInducing
      (isClosedEmbedding_analytification_map b).isInducing W hW)
    ((bijective_bcStalk_comp_iff a b G _).1 h)

end Comp

section Restrict

variable {V V' Y' : SchemeLFTℂ.{u}} (π : Y' ⟶ Y) (πV : V' ⟶ V) (u : V ⟶ Y) (u' : V' ⟶ Y')
  [IsOpenImmersion u.hom.left] [IsOpenImmersion u'.hom.left]

/-- **The analytic base change morphism can be tested on open subschemes**: if `u : V ⟶ Y` and
`u' : V' ⟶ Y'` are open immersions with `π_V ≫ u = u' ≫ π` and `π⁻¹(u(V)) ⊆ u'(V')`, then the base
change morphism of `π` at `F` is bijective at `u^an v` if the base change morphism of `π_V` at
`u'^* F` is bijective at `v`. -/
theorem bijective_bcStalk_of_isOpenImmersion (w : πV ≫ u = u' ≫ π)
    (hc : ∀ z, π.hom.left.base z ∈ Set.range u.hom.left.base → z ∈ Set.range u'.hom.left.base)
    (F : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf)
    (v : analytification.obj V)
    (hv : Function.Bijective (bcStalk πV (u'.hom.left.toLRSHom.pullbackModules.obj F) v)) :
    Function.Bijective (bcStalk π F ((analytification.map u).toLRSHom.base v)) := by
  have hc' : ∀ z, (analytification.map π).toLRSHom.base z ∈
      Set.range (analytification.map u).toLRSHom.base →
        z ∈ Set.range (analytification.map u').toLRSHom.base := by
    intro z hz
    rw [range_analytification_map] at hz ⊢
    change (analytificationπLRS Y).base ((analytification.map π).toLRSHom.base z) ∈
      Set.range u.hom.left.base at hz
    rw [analytificationπ_base_map] at hz
    exact hc _ hz
  have w' : (analytification.map πV).toLRSHom ≫ (analytification.map u).toLRSHom =
      (analytification.map u').toLRSHom ≫ (analytification.map π).toLRSHom := by
    have := congrArg (fun k ↦ (analytification.map k).toLRSHom) w
    simp only [Functor.map_comp] at this
    exact this
  exact bijective_stalkFunctor_map_pushforwardModulesBaseChange_of_restrict
    (analytificationπLRS_naturality π) (analytificationπLRS_naturality πV)
    (analytificationπLRS_naturality u) (analytificationπLRS_naturality u')
    (congrArg (fun k ↦ k.hom.left.toLRSHom) w) w' u.hom.left.isOpenEmbedding
    (isOpenEmbedding_analytification_map u) u'.hom.left.isOpenEmbedding
    (isOpenEmbedding_analytification_map u') hc hc' F v hv

end Restrict

end ComplexAnalytic

end
