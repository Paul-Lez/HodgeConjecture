/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveGAGA
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceHom
public import Other.Oka.Analytification.GAGA.ClosedImmersionPushforward

/-!
# GAGA-2 for projective schemes

For a projective scheme `X` over `ℂ` and coherent sheaves `F`, `G` on `X`, analytification
`Hom(F, G) → Hom(F^an, G^an)` is bijective (`ComplexAnalytic.gaga₂`, Serre's GAGA-2).

The proof: choose a closed immersion `i : X ⟶ ℙⁿ`. Pushforward along `i` and along `i^an` is fully
faithful (the counits of `i^* ⊣ i_*` and `(i^an)^* ⊣ (i^an)_*` are isomorphisms, since `i` and
`i^an` are closed embeddings with surjective stalk maps). The base change isomorphism
`(i_* F)^an ≅ (i^an)_* (F^an)` is natural in `F`
(`ComplexAnalytic.analytificationPushforwardBaseChange_naturality`), so the map for `F`, `G` on `X`
is identified with the map for `i_* F`, `i_* G` on `ℙⁿ`, which is bijective by GAGA-2 on `ℙⁿ`
(`ComplexAnalytic.gaga₂_projectiveSpace`).

`ComplexAnalytic.gaga` bundles GAGA-1 and GAGA-2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- **GAGA-2 on `ℙⁿ`**: for coherent sheaves `F`, `G` on `ℙⁿ_ℂ`, analytification
`Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem gaga₂_projectiveSpace (n : ℕ)
    (F G : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] [G.IsCoherent] :
    Function.Bijective ((analytificationModules (projectiveSpace.{u} n)).map : (F ⟶ G) → _) :=
  bijective_analytificationModules_map_projectiveSpace
    (fun G hG ↦ @gaga_projectiveSpace n G hG 0) F G

variable {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X)

/-- **Naturality of the base change morphism** `(i_* G)^an ⟶ (i^an)_* (G^an)` in `G`. -/
lemma analytificationPushforwardBaseChange_naturality
    {G G' : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf} (φ : G ⟶ G') :
    (analytificationModules X).map
        ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).map φ) ≫
      analytificationPushforwardBaseChange i G' =
    analytificationPushforwardBaseChange i G ≫
      (SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).map
        ((analytificationModules Z).map φ) := by
  simp only [analytificationPushforwardBaseChange, Category.assoc]
  have hη := (analytification.map i).toLRSHom.pullbackModulesAdj.unit.naturality
    ((analytificationModules X).map
      ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).map φ))
  erw [reassoc_of% hη]
  congr 1
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  have h1 := (LocallyRingedSpace.Hom.pullbackModulesCommSqIso
    (analytificationπLRS_naturality i)).hom.naturality
      ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).map φ)
  have h2 := i.hom.left.toLRSHom.pullbackModulesAdj.counit_naturality φ
  simp only [Functor.comp_map] at h1
  change _ ≫ _ ≫ _ = (_ ≫ _) ≫ (analytificationπLRS Z).pullbackModules.map φ
  erw [reassoc_of% h1]
  have h3 := congrArg (analytificationπLRS Z).pullbackModules.map h2
  rw [Functor.map_comp, Functor.map_comp] at h3
  exact congrArg (_ ≫ ·) h3

/-- Pushforward of sheaves of modules along a closed embedding of locally ringed spaces with
surjective stalk maps is fully faithful. -/
def fullyFaithfulPushforwardModulesOfIsClosedEmbedding {A B : LocallyRingedSpace.{u}} (f : A ⟶ B)
    (hf : Topology.IsClosedEmbedding f.base) (hs : ∀ x, Function.Surjective (f.stalkMap x)) :
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).FullyFaithful :=
  haveI : ∀ G, IsIso (f.pullbackModulesAdj.counit.app G) :=
    fun G ↦ f.isIso_pullbackModulesAdj_counit_app hf hs G
  haveI : IsIso f.pullbackModulesAdj.counit := NatIso.isIso_of_isIso_app _
  f.pullbackModulesAdj.fullyFaithfulROfIsIsoCounit

/-- **GAGA-2 for closed subschemes of `ℙⁿ`**: for a closed immersion `i : X ⟶ ℙⁿ` over `ℂ` and
coherent sheaves `F`, `G` on `X`, analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem bijective_analytificationModules_map_of_isClosedImmersion {X : SchemeLFTℂ.{u}} {n : ℕ}
    (i : X ⟶ projectiveSpace.{u} n) [IsClosedImmersion i.hom.left]
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] [G.IsCoherent] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) := by
  haveI : IsLocallyNoetherian (projectiveSpace.{u} n).obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpace.{u} n).obj.hom
  have hcF := isCoherent_pushforward_of_isClosedImmersion i.hom.left F
  have hcG := isCoherent_pushforward_of_isClosedImmersion i.hom.left G
  have hP := fullyFaithfulPushforwardModulesOfIsClosedEmbedding i.hom.left.toLRSHom
    i.hom.left.isClosedEmbedding i.hom.left.stalkMap_surjective
  have hPan := fullyFaithfulPushforwardModulesOfIsClosedEmbedding (analytification.map i).toLRSHom
    (isClosedEmbedding_analytification_map i) (surjective_stalkMap_analytification_map i)
  haveI := isIso_analytificationPushforwardBaseChange i F
  haveI := isIso_analytificationPushforwardBaseChange i G
  let e := (asIso (analytificationPushforwardBaseChange i F)).homCongr
    (asIso (analytificationPushforwardBaseChange i G))
  have hB := @gaga₂_projectiveSpace n _ _ hcF hcG
  have hcomp : (SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).map
        ∘ ((analytificationModules X).map : (F ⟶ G) → _) =
      e ∘ (analytificationModules (projectiveSpace.{u} n)).map ∘
        (SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).map := by
    funext φ
    simp only [Function.comp_apply, e, Iso.homCongr_apply, asIso_inv, asIso_hom,
      analytificationPushforwardBaseChange_naturality, IsIso.inv_hom_id_assoc]
  refine (Function.Bijective.of_comp_iff' (hPan.map_bijective _ _) _).1 ?_
  rw [hcomp]
  exact e.bijective.comp (hB.comp (hP.map_bijective F G))

/-- **Serre's GAGA-2**: for a projective scheme `X` over `ℂ` and coherent sheaves `F`, `G` on
`X`, analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem gaga₂ (X : SchemeLFTℂ.{u}) (hX : IsProjectiveℂ X)
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent] [G.IsCoherent] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) := by
  obtain ⟨n, i, hi⟩ := hX
  exact bijective_analytificationModules_map_of_isClosedImmersion i F G

/-- **Serre's GAGA** (GAGA-1 and GAGA-2) for a projective scheme `X` over `ℂ`: for coherent
sheaves `F`, `G` on `X`, the comparison maps `Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective for all
`q`, and analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem gaga (X : SchemeLFTℂ.{u}) (hX : IsProjectiveℂ X) :
    (∀ (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ),
      Function.Bijective (gagaMap X F q)) ∧
    (∀ (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
      [F.IsCoherent] [G.IsCoherent],
      Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _)) :=
  ⟨fun F _ q ↦ gaga₁ X hX F q, fun F G _ _ ↦ gaga₂ X hX F G⟩

end ComplexAnalytic

end
