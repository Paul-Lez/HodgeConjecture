/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveGAGAHom
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceAnHyperplaneCover
public import Other.Oka.Analytification.GAGA.CartanSerre
public import Other.Oka.Analytification.GAGA.ClosedImmersionCoherent
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PullbackCoherent
public import Other.Oka.AlgebraicGeometry.Modules.Coherent

/-!
# GAGA-3 for projective schemes, and Serre's GAGA theorem

For a projective scheme `X` over `ℂ`, every coherent analytic sheaf `M` on `X^an` is isomorphic to
the analytification of a coherent algebraic sheaf on `X` (`ComplexAnalytic.gaga₃`, Serre's
GAGA-3). `ComplexAnalytic.gagaFull` bundles GAGA-1, GAGA-2 and GAGA-3.

The proof: choose a closed immersion `i : X ⟶ ℙⁿ`. The pushforward `(i^an)_* M` is coherent on
`ℙⁿ_an` (`ComplexAnalytic.isCoherent_pushforward_analytification_map`), so by GAGA-3 on `ℙⁿ`
(`ComplexAnalytic.gaga₃_projectiveSpace`, with Cartan–Serre finiteness
`ComplexAnalytic.projectiveSpaceAn.finiteDimensional_H_one`) it is isomorphic to `N^an` for a
coherent `N` on `ℙⁿ`. Then `F = i^* N` is coherent
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf`),
and
`F^an = π_X^* i^* N ≅ (i^an)^* π^* N = (i^an)^* N^an ≅ (i^an)^* (i^an)_* M ≅ M`,
the last isomorphism being the counit of `(i^an)^* ⊣ (i^an)_*`, an isomorphism because `i^an` is a
closed embedding with surjective stalk maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace ComplexAnalytic

/-- **Serre's GAGA-3 on `ℙⁿ`**: every coherent analytic sheaf on `ℙⁿ_an` is isomorphic to the
analytification of a coherent algebraic sheaf on `ℙⁿ`. -/
theorem gaga₃_projectiveSpace_of_isCoherent (n : ℕ)
    (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules (projectiveSpace.{u} n)).obj F ≅ M) :=
  gaga₃_projectiveSpace (fun n M hM ↦ @projectiveSpaceAn.finiteDimensional_H_one n M hM) n M hM

/-- **GAGA-3 for closed subschemes of `ℙⁿ`**: for a closed immersion `i : X ⟶ ℙⁿ` over `ℂ`,
every coherent analytic sheaf on `X^an` is isomorphic to the analytification of a coherent
algebraic sheaf on `X`, namely `i^* N` for a coherent `N` on `ℙⁿ` with `N^an ≅ (i^an)_* M`. -/
theorem gaga₃_of_isClosedImmersion {X : SchemeLFTℂ.{u}} {n : ℕ}
    (i : X ⟶ projectiveSpace.{u} n) [IsClosedImmersion i.hom.left]
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) := by
  haveI := hM
  obtain ⟨N, hN, ⟨e⟩⟩ := gaga₃_projectiveSpace_of_isCoherent n _
    (isCoherent_pushforward_analytification_map i M)
  haveI := hN
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  haveI : IsLocallyNoetherian X.obj.left := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  refine ⟨i.hom.left.toLRSHom.pullbackModules.obj N,
    LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
      X.obj.left.isCoherentStructureSheaf _ N, ⟨?_⟩⟩
  have hc := (analytification.map i).toLRSHom.isIso_pullbackModulesAdj_counit_app
    (isClosedEmbedding_analytification_map i) (surjective_stalkMap_analytification_map i) M
  exact ((LocallyRingedSpace.Hom.pullbackModulesCommSqIso
      (analytificationπLRS_naturality i)).app N).symm ≪≫
    (analytification.map i).toLRSHom.pullbackModules.mapIso e ≪≫
    @asIso _ _ _ _ ((analytification.map i).toLRSHom.pullbackModulesAdj.counit.app M) hc

/-- **Serre's GAGA-3**: for a projective scheme `X` over `ℂ`, every coherent analytic sheaf on
`X^an` is isomorphic to the analytification of a coherent algebraic sheaf on `X`. -/
theorem gaga₃ (X : SchemeLFTℂ.{u}) (hX : IsProjectiveℂ X)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) := by
  obtain ⟨n, i, hi⟩ := hX
  exact gaga₃_of_isClosedImmersion i M hM

/-- **Serre's GAGA theorem** for a projective scheme `X` over `ℂ`:
1. for every coherent sheaf `F` on `X`, the comparison maps `Hᵠ(X, F) → Hᵠ(X^an, F^an)` are
   bijective for all `q` (GAGA-1);
2. for coherent sheaves `F`, `G` on `X`, analytification `Hom(F, G) → Hom(F^an, G^an)` is
   bijective (GAGA-2);
3. every coherent analytic sheaf on `X^an` is isomorphic to `F^an` for a coherent sheaf `F` on `X`
   (GAGA-3). -/
theorem gagaFull (X : SchemeLFTℂ.{u}) (hX : IsProjectiveℂ X) :
    (∀ (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ),
      Function.Bijective (gagaMap X F q)) ∧
    (∀ (F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
      [F.IsCoherent] [G.IsCoherent],
      Function.Bijective ((analytificationModules X).map : (F ⟶ G) → _)) ∧
    (∀ (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf),
      M.IsCoherent → ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
        F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M)) :=
  ⟨(gaga X hX).1, (gaga X hX).2, gaga₃ X hX⟩

end ComplexAnalytic

end
