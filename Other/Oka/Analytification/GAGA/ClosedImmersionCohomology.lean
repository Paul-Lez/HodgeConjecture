/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ClosedImmersion
public import Other.Oka.Analytification.GAGA.CohomologyComparison
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CohomologyBaseChange

/-!
# The GAGA comparison map and pushforward along closed immersions

Let `i : Z ⟶ X` be a closed immersion of schemes locally of finite type over `ℂ` and `G` a sheaf
of `𝒪_Z`-modules. Pushforward along the closed embeddings `i` and `i^an` identifies cohomology
(`ComplexAnalytic.closedImmersionCohomologyAddEquiv`,
`ComplexAnalytic.closedImmersionAnCohomologyAddEquiv`), and the square

```
Hᵠ(X, i_* G) --gagaMap--> Hᵠ(X^an, (i_* G)^an) --base change--> Hᵠ(X^an, (i^an)_* G^an)
     ≃ ↑                                                                   ↑ ≃
Hᵠ(Z, G) ------------------------gagaMap------------------------> Hᵠ(Z^an, G^an)
```

commutes (`ComplexAnalytic.gagaMap_pushforward`), where the base change map is induced by
`ComplexAnalytic.analytificationPushforwardBaseChange`. Consequently, if the base change morphism
is an isomorphism, the comparison map for `i_* G` on `X` is bijective (injective, surjective) if
and only if the comparison map for `G` on `Z` is
(`ComplexAnalytic.bijective_gagaMap_pushforward_iff`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X)

/-- The base change morphism `(i_* G)^an ⟶ (i^an)_* G^an` is the base change morphism of the
commutative square of locally ringed spaces formed by `i`, `i^an` and the comparison morphisms. -/
lemma analytificationPushforwardBaseChange_eq
    (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf) :
    analytificationPushforwardBaseChange i G =
      LocallyRingedSpace.pushforwardModulesBaseChange (analytificationπLRS_naturality i) G :=
  rfl

variable [IsClosedImmersion i.hom.left]

/-- `Hᵠ(Z, G) ≃ Hᵠ(X, i_* G)` for a closed immersion `i`. -/
def closedImmersionCohomologyAddEquiv
    (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf) (q : ℕ) :
    LocallyRingedSpace.H G q ≃+ LocallyRingedSpace.H
      ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q :=
  TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv i.hom.left.isClosedEmbedding G.toAb q

/-- `Hᵠ(Z^an, M) ≃ Hᵠ(X^an, (i^an)_* M)` for a closed immersion `i`. -/
def closedImmersionAnCohomologyAddEquiv
    (M : SheafOfModules.{u} (analytification.obj Z).toLocallyRingedSpace.ringSheaf) (q : ℕ) :
    LocallyRingedSpace.H M q ≃+ LocallyRingedSpace.H
      ((SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).obj M) q :=
  TopCat.Sheaf.H.pushforwardClosedEmbeddingAddEquiv (isClosedEmbedding_analytification_map i)
    M.toAb q

/-- **The GAGA comparison map commutes with pushforward along closed immersions**: for
`x ∈ Hᵠ(Z, G)`, the comparison map of `i_* G` applied to `i_* x`, followed by the base change
morphism `(i_* G)^an ⟶ (i^an)_* G^an`, is `i^an_*` of the comparison map of `G` applied to `x`. -/
theorem gagaMap_pushforward
    (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf) (q : ℕ)
    (x : LocallyRingedSpace.H G q) :
    LocallyRingedSpace.H.map (analytificationPushforwardBaseChange i G) q
        (gagaMap X _ q (closedImmersionCohomologyAddEquiv i G q x)) =
      closedImmersionAnCohomologyAddEquiv i _ q (gagaMap Z G q x) :=
  (LocallyRingedSpace.pushforwardClosedEmbeddingAddEquiv_cohomologyMap
    (analytificationπLRS_naturality i) i.hom.left.isClosedEmbedding
    (isClosedEmbedding_analytification_map i) G x).symm

section IsIso

variable (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf)
  [IsIso (analytificationPushforwardBaseChange i G)] (q : ℕ)

/-- The isomorphism `Hᵠ(X^an, (i_* G)^an) ≃ Hᵠ(X^an, (i^an)_* G^an)` induced by the base change
isomorphism. -/
def analytificationPushforwardBaseChangeCohomologyAddEquiv :
    LocallyRingedSpace.H ((analytificationModules X).obj
        ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G)) q ≃+
      LocallyRingedSpace.H ((SheafOfModules.pushforward.{u}
        (analytification.map i).toLRSHom.toRingSheafHom).obj
          ((analytificationModules Z).obj G)) q :=
  TopCat.Sheaf.H.addEquivOfIso
    ((LocallyRingedSpace.modulesToAb _).mapIso (asIso (analytificationPushforwardBaseChange i G))) q

/-- The GAGA comparison map for `i_* G` is the comparison map for `G`, conjugated by the
identifications of cohomology along `i` and `i^an` and the base change isomorphism. -/
lemma gagaMap_pushforward_eq_comp :
    ⇑(gagaMap X ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q) =
      (analytificationPushforwardBaseChangeCohomologyAddEquiv i G q).symm ∘
        closedImmersionAnCohomologyAddEquiv i _ q ∘ gagaMap Z G q ∘
          (closedImmersionCohomologyAddEquiv i G q).symm := by
  funext y
  obtain ⟨x, rfl⟩ := (closedImmersionCohomologyAddEquiv i G q).surjective y
  simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
  rw [AddEquiv.eq_symm_apply]
  exact gagaMap_pushforward i G q x

/-- If the base change morphism `(i_* G)^an ⟶ (i^an)_* G^an` is an isomorphism, the GAGA
comparison map for `i_* G` is bijective if and only if the one for `G` is. -/
theorem bijective_gagaMap_pushforward_iff :
    Function.Bijective
        (gagaMap X ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Bijective (gagaMap Z G q) := by
  rw [gagaMap_pushforward_eq_comp, EquivLike.comp_bijective, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- If the base change morphism `(i_* G)^an ⟶ (i^an)_* G^an` is an isomorphism, the GAGA
comparison map for `i_* G` is injective if and only if the one for `G` is. -/
theorem injective_gagaMap_pushforward_iff :
    Function.Injective
        (gagaMap X ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Injective (gagaMap Z G q) := by
  rw [gagaMap_pushforward_eq_comp, EquivLike.comp_injective, EquivLike.comp_injective,
    EquivLike.injective_comp]

/-- If the base change morphism `(i_* G)^an ⟶ (i^an)_* G^an` is an isomorphism, the GAGA
comparison map for `i_* G` is surjective if and only if the one for `G` is. -/
theorem surjective_gagaMap_pushforward_iff :
    Function.Surjective
        (gagaMap X ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Surjective (gagaMap Z G q) := by
  rw [gagaMap_pushforward_eq_comp, EquivLike.comp_surjective, EquivLike.comp_surjective,
    EquivLike.surjective_comp]

end IsIso

end ComplexAnalytic

end
