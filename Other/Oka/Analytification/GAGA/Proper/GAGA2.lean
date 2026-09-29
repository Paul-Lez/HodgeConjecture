/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.GAGA1
public import Other.Oka.Analytification.GAGA.Proper.HomSheaf

/-!
# GAGA-2 for proper schemes

For a proper scheme `X` over `ℂ` and coherent sheaves `F`, `G` on `X`, analytification
`Hom(F, G) → Hom(F^an, G^an)` is bijective (`ComplexAnalytic.gaga₂_of_isProperℂ`), assuming
`ComplexAnalytic.RelativeAnalyticSerre`. It follows from GAGA-1 in degree zero applied to the
coherent sheaf `𝓗om(F, G)`.
-/

@[expose] public section

universe u

namespace ComplexAnalytic

/-- **GAGA-2 for proper schemes**: analytification is fully faithful on coherent sheaves. -/
theorem gaga₂_of_isProperℂ {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X)
    (h : RelativeAnalyticSerre.{u})
    (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    [G.IsCoherent] :
    Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _) :=
  bijective_analytificationModules_map_of_bijective_gagaMap
    (fun H _ ↦ gaga₁_of_isProperℂ hX h H 0) F G

end ComplexAnalytic

end
