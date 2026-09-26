/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceCoherentGAGA
public import Other.Oka.AlgebraicGeometry.Modules.CoherentPushforward

/-!
# GAGA for coherent sheaves on projective schemes

A scheme `X` locally of finite type over `ℂ` is *projective* (`ComplexAnalytic.IsProjectiveℂ`)
if it admits a closed immersion `i : X ⟶ ℙⁿ` over `ℂ` for some `n`. For such `X` and every
coherent sheaf `F` on `X`, the comparison map `Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all
`q` (`ComplexAnalytic.gaga₁`, Serre's GAGA-1).

The proof: `i_* F` is coherent on `ℙⁿ`
(`AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion`), so GAGA on `ℙⁿ`
(`ComplexAnalytic.gaga_projectiveSpace`) applies to it, and the comparison map for `i_* F` on
`ℙⁿ` is bijective if and only if the one for `F` on `X` is
(`ComplexAnalytic.bijective_gagaMap_pushforward_iff`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- A scheme locally of finite type over `ℂ` is **projective** if it admits a closed immersion
over `ℂ` into some projective space `ℙⁿ_ℂ`. -/
def IsProjectiveℂ (X : SchemeLFTℂ.{u}) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ projectiveSpace.{u} n), IsClosedImmersion i.hom.left

/-- **GAGA for coherent sheaves on closed subschemes of `ℙⁿ`**: for a closed immersion
`i : X ⟶ ℙⁿ` over `ℂ` and a coherent `F` on `X`, the comparison map
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all `q`. -/
theorem gagaMap_bijective_of_isClosedImmersion {X : SchemeLFTℂ.{u}} {n : ℕ}
    (i : X ⟶ projectiveSpace.{u} n) [IsClosedImmersion i.hom.left]
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) := by
  haveI := isIso_analytificationPushforwardBaseChange i F
  haveI : IsLocallyNoetherian (projectiveSpace.{u} n).obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpace.{u} n).obj.hom
  have hc := isCoherent_pushforward_of_isClosedImmersion i.hom.left F
  exact (bijective_gagaMap_pushforward_iff i F q).1 (@gaga_projectiveSpace n _ hc q)

/-- **Serre's GAGA-1**: for a projective scheme `X` over `ℂ` and a coherent sheaf `F` on `X`,
the comparison map `Hᵠ(X, F) → Hᵠ(X^an, F^an)` is bijective for all `q`. -/
theorem gaga₁ (X : SchemeLFTℂ.{u}) (hX : IsProjectiveℂ X)
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) := by
  obtain ⟨n, i, hi⟩ := hX
  exact gagaMap_bijective_of_isClosedImmersion i F q

end ComplexAnalytic

end
