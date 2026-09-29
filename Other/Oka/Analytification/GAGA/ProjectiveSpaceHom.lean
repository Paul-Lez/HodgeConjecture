/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CohomologyComparison
public import Other.Oka.Analytification.GAGA.ProjectiveSpace
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TheoremA
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwistPullbackModules
public import Other.Oka.CategoryTheory.Functor.MapBijective
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PullbackModulesUnitHom

/-!
# GAGA for morphisms of coherent sheaves on `ℙⁿ`

We prove Serre's GAGA-2 on `ℙⁿ`: for coherent sheaves `F`, `G` on `ℙⁿ` the analytification
`Hom(F, G) → Hom(F^an, G^an)` is bijective
(`ComplexAnalytic.bijective_analytificationModules_map_projectiveSpace`), assuming GAGA in
degree `0`: the comparison map `Γ(ℙⁿ, G) → Γ(ℙⁿ_an, G^an)` is bijective for every coherent `G`
(hypothesis `h0`, stated with `ComplexAnalytic.gagaMap _ G 0`).

The proof is Serre's:
1. `F = 𝒪`: under the adjunction `(-)^an ⊣ π_*`, analytification of morphisms `𝒪 ⟶ G` is
   composition with the unit `G ⟶ π_* G^an`, i.e. the comparison map on global sections.
2. `F = O(k)`: the pullback of a twist is the twist of the pullback
   (`AlgebraicGeometry.LocallyRingedSpace.pullbackModulesTwistIso`), so twisting by `-k` on both
   sides (autoequivalences) reduces to `Hom(𝒪, G(-k))`, and `G(-k)` is coherent.
3. `F = 𝒪^I(-m)`: a coproduct of copies of `O(-m)`, preserved by analytification.
4. General `F`: by Serre's theorem A there is an epimorphism `𝒪^I(-m) ⟶ F` with coherent kernel
   `K`; injectivity for all coherent `F` follows, and then surjectivity from injectivity for
   `K`, since analytification is right exact.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

/-- **Analytification of morphisms out of `𝒪_X`** is bijective onto morphisms out of `𝒪_X^an`
whenever the comparison map on global sections is bijective. -/
lemma bijective_analytificationModules_map_unit (X : SchemeLFTℂ.{u})
    (G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    (hG : Function.Bijective (gagaMap X G 0)) :
    Function.Bijective ((analytificationModules X).map :
      (SheafOfModules.unit X.obj.left.toLocallyRingedSpace.ringSheaf ⟶ G) → _) := by
  refine (analytificationπLRS X).bijective_pullbackModules_map_unit G ?_
  have hc : (fun b ↦ ((analytificationModulesAdj X).unit.app G).val.app (op ⊤) b) =
      LocallyRingedSpace.H.equiv₀ _ ∘ gagaMap X G 0 ∘ (LocallyRingedSpace.H.equiv₀ G).symm := by
    funext b
    rw [Function.comp_apply, Function.comp_apply, equiv₀_gagaMap, AddEquiv.apply_symm_apply]
  change Function.Bijective (fun b ↦ ((analytificationModulesAdj X).unit.app G).val.app (op ⊤) b)
  rw [hc]
  exact (LocallyRingedSpace.H.equiv₀ _).bijective.comp
    (hG.comp (LocallyRingedSpace.H.equiv₀ G).symm.bijective)

variable {n : ℕ}
  (h0 : ∀ G : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf,
    G.IsCoherent → Function.Bijective (gagaMap (projectiveSpace.{u} n) G 0))

include h0

/-- GAGA-2 for `F = O(k)` on `ℙⁿ`, assuming GAGA in degree `0`. -/
lemma bijective_analytificationModules_map_twistingSheaf (k : ℤ) (G : ℙₒ(n; ULift.{u} ℂ).Modules)
    [G.IsCoherent] :
    Function.Bijective ((analytificationModules (projectiveSpace.{u} n)).map :
      (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) k ⟶ G) → _) := by
  let c := ProjectiveSpace.cocycle n (ULift.{u} ℂ) ^ (-k)
  have hU := ProjectiveSpace.iSup_U n (ULift.{u} ℂ)
  let e := LocallyRingedSpace.pullbackModulesTwistIso
    (analytificationπLRS (projectiveSpace.{u} n)) c hU
  refine Functor.bijective_map_of_natIso (C := ℙₒ(n; ULift.{u} ℂ).Modules)
    (hTfull := (Scheme.Modules.twistEquivalence c hU).full_functor)
    (hTfaith := (Scheme.Modules.twistEquivalence c hU).faithful_functor)
    (hT' := (LocallyRingedSpace.modTwistEquivalence
      (LocallyRingedSpace.cocycleComap (analytificationπLRS (projectiveSpace.{u} n)) c)
      (LocallyRingedSpace.iSup_preimOpen hU)).faithful_functor)
    (analytificationModules (projectiveSpace.{u} n)) e _ _ ?_
  let iso : ProjectiveSpace.twist (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) k) (-k) ≅
      SheafOfModules.unit _ :=
    ProjectiveSpace.twistTwistIso _ k (-k) ≪≫
      (Scheme.Modules.twistFunctorCongr (congrArg (_ ^ ·) (add_neg_cancel k))).app _ ≪≫
      ProjectiveSpace.twistZeroIso _
  exact Functor.bijective_map_of_iso_left (C := ℙₒ(n; ULift.{u} ℂ).Modules) _ iso.symm _
    (bijective_analytificationModules_map_unit _ _
      (h0 _ (ProjectiveSpace.isCoherent_twist G (-k))))

/-- GAGA-2 for `F = 𝒪^I(m)` on `ℙⁿ`, assuming GAGA in degree `0`. -/
lemma bijective_analytificationModules_map_twist_free (I : Type u) (m : ℤ)
    (G : ℙₒ(n; ULift.{u} ℂ).Modules) [G.IsCoherent] :
    Function.Bijective ((analytificationModules (projectiveSpace.{u} n)).map :
      (ProjectiveSpace.twist (SheafOfModules.free I) m ⟶ G) → _) := by
  have hs := Functor.bijective_map_sigma
    (C := SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    (analytificationModules (projectiveSpace.{u} n))
    (fun _ : I ↦ ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) m) G
    fun _ ↦ bijective_analytificationModules_map_twistingSheaf h0 m G
  exact Functor.bijective_map_of_iso_left (C := ℙₒ(n; ULift.{u} ℂ).Modules) _
    (ProjectiveSpace.twistFreeIso I m).symm G hs

/-- Injectivity of GAGA-2 on `ℙⁿ`, assuming GAGA in degree `0`. -/
lemma injective_analytificationModules_map_projectiveSpace' (F G : ℙₒ(n; ULift.{u} ℂ).Modules)
    [F.IsCoherent] [G.IsCoherent] :
    Function.Injective ((analytificationModules (projectiveSpace.{u} n)).map : (F ⟶ G) → _) := by
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  obtain ⟨m₀, h⟩ := ProjectiveSpace.exists_epi_twist_free_isCoherent_kernel F
  obtain ⟨I, _, p, hp, -, -⟩ := h m₀ le_rfl
  exact Functor.injective_map_of_epi (C := ℙₒ(n; ULift.{u} ℂ).Modules) _ p G
    (bijective_analytificationModules_map_twist_free h0 I _ G).1

/-- **GAGA-2 on `ℙⁿ`**: for coherent sheaves `F`, `G` on `ℙⁿ`, analytification
`Hom(F, G) → Hom(F^an, G^an)` is bijective, assuming GAGA in degree `0` (`h0`). -/
theorem bijective_analytificationModules_map_projectiveSpace' (F G : ℙₒ(n; ULift.{u} ℂ).Modules)
    [F.IsCoherent] [G.IsCoherent] :
    Function.Bijective ((analytificationModules (projectiveSpace.{u} n)).map : (F ⟶ G) → _) := by
  refine ⟨injective_analytificationModules_map_projectiveSpace' h0 F G, ?_⟩
  haveI : IsNoetherianRing (ULift.{u} ℂ) := isNoetherianRing_of_ringEquiv ℂ ULift.ringEquiv.symm
  obtain ⟨m₀, h⟩ := ProjectiveSpace.exists_epi_twist_free_isCoherent_kernel F
  obtain ⟨I, _, p, hp, -, hK⟩ := h m₀ le_rfl
  exact Functor.surjective_map_of_epi (C := ℙₒ(n; ULift.{u} ℂ).Modules) _ p G
    (hA := (inferInstance :
      (analytificationModules (projectiveSpace.{u} n)).PreservesZeroMorphisms))
    (hAp := by
      haveI : Epi (C := SheafOfModules.{u}
        (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) p := hp
      exact (analytificationModules (projectiveSpace.{u} n)).map_epi p)
    (bijective_analytificationModules_map_twist_free h0 I _ G).2
    (injective_analytificationModules_map_projectiveSpace' h0 _ G)

/-- **GAGA-2 on `ℙⁿ`**, for sheaves of modules on the underlying locally ringed space: for
coherent `F`, `G`, analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective, assuming GAGA in
degree `0` (`h0`). -/
theorem bijective_analytificationModules_map_projectiveSpace
    (F G : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    [hF : F.IsCoherent] [hG : G.IsCoherent] :
    Function.Bijective ((analytificationModules (projectiveSpace.{u} n)).map : (F ⟶ G) → _) :=
  @bijective_analytificationModules_map_projectiveSpace' n h0 F G hF hG

end ComplexAnalytic

end
