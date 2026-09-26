/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CohomologyComparison
public import Other.Oka.Analytification.GAGA.SheafAnalytificationIsCoherent
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafCoherent

/-!
# GAGA-2 from GAGA-1 in degree zero

Let `X` be a scheme locally of finite type over `ℂ` and `F`, `G` sheaves of `𝒪_X`-modules. The
analytification `Hom(F, G) → Hom(F^an, G^an)` factors as

`Hom(F, G) = Γ(X, 𝓗om(F, G)) → Γ(X^an, 𝓗om(F, G)^an) → Γ(X^an, 𝓗om(F^an, G^an)) = Hom(F^an, G^an)`,

where the first map is the GAGA comparison map in degree `0` for `𝓗om(F, G)`
(`ComplexAnalytic.equiv₀_gagaMap`) and the second is induced by the comparison morphism
`𝓗om(F, G)^an ⟶ 𝓗om(F^an, G^an)`
(`AlgebraicGeometry.LocallyRingedSpace.homSheafPullbackComp`), which is an isomorphism for `F`
coherent (`ComplexAnalytic.isIso_homSheafAnalytificationComp`), since the stalk maps of
`X^an ⟶ X` are flat. Hence analytification of morphisms out of a coherent sheaf is bijective as
soon as the comparison map in degree `0` is bijective for `𝓗om(F, G)`
(`ComplexAnalytic.bijective_analytificationModules_map_of_bijective_gagaMap_homSheaf`), and GAGA-1
in degree `0` for all coherent sheaves implies GAGA-2 for all coherent sheaves, `𝓗om(F, G)` being
coherent (`ComplexAnalytic.bijective_analytificationModules_map_of_bijective_gagaMap`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable (X : SchemeLFTℂ.{u})

/-- The comparison morphism `𝓗om(F, G)^an ⟶ 𝓗om(F^an, G^an)`. -/
abbrev homSheafAnalytificationComp
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) :
    (analytificationModules X).obj (LocallyRingedSpace.homSheaf F G) ⟶
      LocallyRingedSpace.homSheaf ((analytificationModules X).obj F)
        ((analytificationModules X).obj G) :=
  LocallyRingedSpace.homSheafPullbackComp (analytificationπLRS X) F G

variable {X}

/-- **GAGA-2 from GAGA-1 in degree zero**: if the GAGA comparison map `Γ(X, 𝓗om(F, G)) →
Γ(X^an, 𝓗om(F, G)^an)` is bijective and `𝓗om(F, G)^an ⟶ 𝓗om(F^an, G^an)` is an isomorphism, then
analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem bijective_analytificationModules_map_of_isIso_homSheafPullbackComp
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    (h0 : Function.Bijective (gagaMap X (LocallyRingedSpace.homSheaf F G) 0))
    [IsIso (homSheafAnalytificationComp X F G)] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) := by
  set π := analytificationπLRS X
  set H := LocallyRingedSpace.homSheaf F G
  let η : H.val.obj (op ⊤) → ((analytificationModules X).obj H).val.obj (op ⊤) :=
    fun t ↦ ((analytificationModulesAdj X).unit.app H).val.app (op ⊤) t
  have hη : Function.Bijective η := by
    have hc : η = LocallyRingedSpace.H.equiv₀ _ ∘ gagaMap X H 0 ∘
        (LocallyRingedSpace.H.equiv₀ H).symm := by
      funext b
      rw [Function.comp_apply, Function.comp_apply, equiv₀_gagaMap, AddEquiv.apply_symm_apply]
    rw [hc]
    exact (LocallyRingedSpace.H.equiv₀ _).bijective.comp
      (h0.comp (LocallyRingedSpace.H.equiv₀ H).symm.bijective)
  let c : ((analytificationModules X).obj H).val.obj (op ⊤) →
      (LocallyRingedSpace.homSheaf ((analytificationModules X).obj F)
        ((analytificationModules X).obj G)).val.obj (op ⊤) :=
    fun t ↦ (homSheafAnalytificationComp X F G).val.app (op ⊤) t
  have hc : Function.Bijective c := by
    haveI : IsIso ((homSheafAnalytificationComp X F G).val.app (op ⊤)) :=
      Functor.map_isIso (SheafOfModules.evaluation _ (op ⊤)) (homSheafAnalytificationComp X F G)
    exact ConcreteCategory.bijective_of_isIso ((homSheafAnalytificationComp X F G).val.app (op ⊤))
  have key : ((analytificationModules X).map : (F ⟶ G) → _) =
      LocallyRingedSpace.homSheafGlobalEquiv _ _ ∘ c ∘ η ∘
        (LocallyRingedSpace.homSheafGlobalEquiv F G).symm := by
    funext φ
    simp only [Function.comp_apply]
    change π.pullbackModules.map φ = _
    rw [← LocallyRingedSpace.homSheafGlobalEquiv_homSheafPullback π F G φ,
      ← LocallyRingedSpace.unit_comp_homSheafPullbackComp π F G]
    rfl
  rw [key]
  exact (LocallyRingedSpace.homSheafGlobalEquiv _ _).bijective.comp
    (hc.comp (hη.comp (LocallyRingedSpace.homSheafGlobalEquiv F G).symm.bijective))

variable (X) in
/-- **Analytification commutes with `𝓗om` out of a coherent sheaf**: for `F` coherent, the
comparison morphism `𝓗om(F, G)^an ⟶ 𝓗om(F^an, G^an)` is an isomorphism. -/
instance isIso_homSheafAnalytificationComp
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] :
    IsIso (homSheafAnalytificationComp X F G) :=
  haveI : ((analytificationπLRS X).pullbackModules.obj F).IsCoherent :=
    isCoherent_analytificationModules X F
  LocallyRingedSpace.isIso_homSheafPullbackComp _ F G (flat_stalkMap_analytificationπ X)

/-- **GAGA-2 from GAGA-1 in degree zero**: for `F` coherent and `G` any sheaf of `𝒪_X`-modules,
if the GAGA comparison map `Γ(X, 𝓗om(F, G)) → Γ(X^an, 𝓗om(F, G)^an)` is bijective, then
analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem bijective_analytificationModules_map_of_bijective_gagaMap_homSheaf
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    (h0 : Function.Bijective (gagaMap X (LocallyRingedSpace.homSheaf F G) 0)) :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) :=
  bijective_analytificationModules_map_of_isIso_homSheafPullbackComp F G h0

/-- **GAGA-2 from GAGA-1 in degree zero**: if the GAGA comparison map
`Γ(X, H) → Γ(X^an, H^an)` is bijective for every coherent sheaf `H` on `X`, then for coherent
`F`, `G` analytification `Hom(F, G) → Hom(F^an, G^an)` is bijective. -/
theorem bijective_analytificationModules_map_of_bijective_gagaMap
    (h0 : ∀ H : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf, H.IsCoherent →
      Function.Bijective (gagaMap X H 0))
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    [G.IsCoherent] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) :=
  bijective_analytificationModules_map_of_bijective_gagaMap_homSheaf F G
    (h0 _ (LocallyRingedSpace.isCoherent_homSheaf F G))

end ComplexAnalytic

end
