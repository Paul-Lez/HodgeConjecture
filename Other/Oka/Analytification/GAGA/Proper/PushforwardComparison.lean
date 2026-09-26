/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ClosedImmersionCohomology
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PushforwardAcyclic

/-!
# The GAGA comparison map and pushforward of acyclic sheaves

Let `π : Y' ⟶ Y` be a morphism of schemes locally of finite type over `ℂ` and `G` a sheaf of
`𝒪_{Y'}`-modules such that `G` is `π`-acyclic and `G^an` is `π^an`-acyclic
(`TopCat.Sheaf.IsPushforwardAcyclic`: the higher direct images vanish). Then pushforward
identifies cohomology on both sides
(`AlgebraicGeometry.LocallyRingedSpace.Hom.pushforwardModulesAcyclicAddEquiv`), and the square

```
Hᵠ(Y, π_* G) --gagaMap--> Hᵠ(Y^an, (π_* G)^an) --base change--> Hᵠ(Y^an, (π^an)_* G^an)
     ≃ ↑                                                                   ↑ ≃
Hᵠ(Y', G) ------------------------gagaMap------------------------> Hᵠ(Y'^an, G^an)
```

commutes (`ComplexAnalytic.gagaMap_pushforward_of_isPushforwardAcyclic`). Consequently, if the
base change morphism `ComplexAnalytic.analytificationPushforwardBaseChange π G` is an
isomorphism, the comparison map for `π_* G` on `Y` is bijective (injective, surjective) in degree
`q` if and only if the comparison map for `G` on `Y'` is
(`ComplexAnalytic.bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic`). This generalises
`ComplexAnalytic.bijective_gagaMap_pushforward_iff` from closed immersions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {Y' Y : SchemeLFTℂ.{u}} (π : Y' ⟶ Y)
  (G : SheafOfModules.{u} Y'.obj.left.toLocallyRingedSpace.ringSheaf)
  (hG : TopCat.Sheaf.IsPushforwardAcyclic π.hom.left.toLRSHom.base G.toAb)
  (hGan : TopCat.Sheaf.IsPushforwardAcyclic (analytification.map π).toLRSHom.base
    ((analytificationModules Y').obj G).toAb)

/-- **The GAGA comparison map commutes with pushforward of acyclic sheaves**: if `G` is
`π`-acyclic and `G^an` is `π^an`-acyclic, then for `x ∈ Hᵠ(Y', G)` the comparison map of
`π_* G` applied to `π_* x`, followed by the base change morphism `(π_* G)^an ⟶ (π^an)_* G^an`,
is `π^an_*` of the comparison map of `G` applied to `x`. -/
theorem gagaMap_pushforward_of_isPushforwardAcyclic (q : ℕ) (x : LocallyRingedSpace.H G q) :
    LocallyRingedSpace.H.map (analytificationPushforwardBaseChange π G) q
        (gagaMap Y _ q (π.hom.left.toLRSHom.pushforwardModulesAcyclicAddEquiv hG q x)) =
      (analytification.map π).toLRSHom.pushforwardModulesAcyclicAddEquiv hGan q
        (gagaMap Y' G q x) :=
  (LocallyRingedSpace.pushforwardModulesAcyclicAddEquiv_cohomologyMap
    (analytificationπLRS_naturality π) G hG hGan x).symm

section IsIso

variable [IsIso (analytificationPushforwardBaseChange π G)] (q : ℕ)

include hG hGan in
/-- The GAGA comparison map for `π_* G` is the comparison map for `G`, conjugated by the
identifications of cohomology along `π` and `π^an` and the base change isomorphism. -/
lemma gagaMap_pushforward_eq_comp_of_isPushforwardAcyclic :
    ⇑(gagaMap Y ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj G) q) =
      (analytificationPushforwardBaseChangeCohomologyAddEquiv π G q).symm ∘
        (analytification.map π).toLRSHom.pushforwardModulesAcyclicAddEquiv hGan q ∘
          gagaMap Y' G q ∘ (π.hom.left.toLRSHom.pushforwardModulesAcyclicAddEquiv hG q).symm := by
  funext y
  obtain ⟨x, rfl⟩ := (π.hom.left.toLRSHom.pushforwardModulesAcyclicAddEquiv hG q).surjective y
  simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
  rw [AddEquiv.eq_symm_apply]
  exact gagaMap_pushforward_of_isPushforwardAcyclic π G hG hGan q x

include hG hGan in
/-- If `G` is `π`-acyclic, `G^an` is `π^an`-acyclic and the base change morphism
`(π_* G)^an ⟶ (π^an)_* G^an` is an isomorphism, the GAGA comparison map for `π_* G` in degree `q`
is bijective if and only if the one for `G` is. -/
theorem bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic :
    Function.Bijective
        (gagaMap Y ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Bijective (gagaMap Y' G q) := by
  rw [gagaMap_pushforward_eq_comp_of_isPushforwardAcyclic π G hG hGan, EquivLike.comp_bijective,
    EquivLike.comp_bijective, EquivLike.bijective_comp]

include hG hGan in
/-- If `G` is `π`-acyclic, `G^an` is `π^an`-acyclic and the base change morphism
`(π_* G)^an ⟶ (π^an)_* G^an` is an isomorphism, the GAGA comparison map for `π_* G` in degree `q`
is injective if and only if the one for `G` is. -/
theorem injective_gagaMap_pushforward_iff_of_isPushforwardAcyclic :
    Function.Injective
        (gagaMap Y ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Injective (gagaMap Y' G q) := by
  rw [gagaMap_pushforward_eq_comp_of_isPushforwardAcyclic π G hG hGan, EquivLike.comp_injective,
    EquivLike.comp_injective, EquivLike.injective_comp]

include hG hGan in
/-- If `G` is `π`-acyclic, `G^an` is `π^an`-acyclic and the base change morphism
`(π_* G)^an ⟶ (π^an)_* G^an` is an isomorphism, the GAGA comparison map for `π_* G` in degree `q`
is surjective if and only if the one for `G` is. -/
theorem surjective_gagaMap_pushforward_iff_of_isPushforwardAcyclic :
    Function.Surjective
        (gagaMap Y ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Surjective (gagaMap Y' G q) := by
  rw [gagaMap_pushforward_eq_comp_of_isPushforwardAcyclic π G hG hGan, EquivLike.comp_surjective,
    EquivLike.comp_surjective, EquivLike.surjective_comp]

end IsIso

include hG hGan in
/-- **GAGA for pushforwards of acyclic sheaves**: if `G` is `π`-acyclic, `G^an` is
`π^an`-acyclic and the base change morphism `(π_* G)^an ⟶ (π^an)_* G^an` is an isomorphism, the
GAGA comparison maps for `π_* G` on `Y` are bijective in all degrees if and only if those for `G`
on `Y'` are. -/
theorem forall_bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic
    [IsIso (analytificationPushforwardBaseChange π G)] :
    (∀ q, Function.Bijective (gagaMap Y
        ((SheafOfModules.pushforward.{u} π.hom.left.toLRSHom.toRingSheafHom).obj G) q)) ↔
      ∀ q, Function.Bijective (gagaMap Y' G q) :=
  forall_congr' fun q ↦ bijective_gagaMap_pushforward_iff_of_isPushforwardAcyclic π G hG hGan q

end ComplexAnalytic

end
