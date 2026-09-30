/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.SheafAnalytification
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology

/-!
# The GAGA comparison map on cohomology

For `X` a scheme locally of finite type over `ℂ`, `π : X^an ⟶ X` the comparison morphism and `F`
a sheaf of `𝒪_X`-modules with analytification `F^an = π^* F`, the comparison map

```
ComplexAnalytic.gagaMap X F q : Hᵠ(X, F) →+ Hᵠ(X^an, F^an)
```

is the pullback map `Hᵠ(X, F) → Hᵠ(X^an, π⁻¹ F)` followed by the map induced by
`π⁻¹ F ⟶ π^* F` (`AlgebraicGeometry.LocallyRingedSpace.Hom.cohomologyMap`). It is natural in `F`
(`ComplexAnalytic.gagaMap_map`), and since the analytification is exact it commutes with the
connecting homomorphisms of every short exact sequence of sheaves of modules on `X`
(`ComplexAnalytic.gagaMap_δ`). In degree zero it is the map on global sections
`F(X) → F^an(X^an)` given by the unit `F ⟶ π_* F^an` (`ComplexAnalytic.equiv₀_gagaMap`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace ComplexAnalytic

variable (X : SchemeLFTℂ.{u})

/-- **The GAGA comparison map** `Hᵠ(X, F) → Hᵠ(X^an, F^an)` for a sheaf of modules `F` on a
scheme `X` locally of finite type over `ℂ`. -/
def gagaMap (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) (q : ℕ) :
    LocallyRingedSpace.H F q →+ LocallyRingedSpace.H ((analytificationModules X).obj F) q :=
  (analytificationπLRS X).cohomologyMap F q

variable {X}

/-- The GAGA comparison map is natural in the sheaf. -/
lemma gagaMap_map {F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf}
    (φ : F ⟶ G) {q : ℕ} (x : LocallyRingedSpace.H F q) :
    gagaMap X G q (LocallyRingedSpace.H.map φ q x) =
      LocallyRingedSpace.H.map ((analytificationModules X).map φ) q (gagaMap X F q x) :=
  (analytificationπLRS X).cohomologyMap_map φ x

/-- The analytification of a short exact sequence of sheaves of modules is short exact. -/
lemma shortExact_map_analytificationModules
    {S : ShortComplex (SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)}
    (hS : S.ShortExact) : (S.map (analytificationModules X)).ShortExact :=
  hS.map_of_exact _

/-- The GAGA comparison map commutes with the connecting homomorphisms of a short exact
sequence of sheaves of modules on `X` and of its analytification. -/
lemma gagaMap_δ
    {S : ShortComplex (SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)}
    (hS : S.ShortExact) {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : LocallyRingedSpace.H S.X₃ n₀) :
    gagaMap X S.X₁ n₁ (LocallyRingedSpace.H.δ hS n₀ n₁ h x) =
      LocallyRingedSpace.H.δ (shortExact_map_analytificationModules hS) n₀ n₁ h
        (gagaMap X S.X₃ n₀ x) :=
  (analytificationπLRS X).cohomologyMap_δ hS (shortExact_map_analytificationModules hS) h x

/-- In degree zero the GAGA comparison map is the map on global sections `F(X) → F^an(X^an)`
given by the unit `F ⟶ π_* F^an` of the adjunction `(-)^an ⊣ π_*`. -/
lemma equiv₀_gagaMap (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    (x : LocallyRingedSpace.H F 0) :
    LocallyRingedSpace.H.equiv₀ _ (gagaMap X F 0 x) =
      ((analytificationModulesAdj X).unit.app F).val.app (op ⊤)
        (LocallyRingedSpace.H.equiv₀ F x) :=
  (analytificationπLRS X).equiv₀_cohomologyMap F x

end ComplexAnalytic

end
