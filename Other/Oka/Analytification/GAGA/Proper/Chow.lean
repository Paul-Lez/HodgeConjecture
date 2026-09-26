/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Chow
public import Other.Oka.Analytification.GAGA.ProjectiveGAGA

/-!
# Chow's lemma over `ℂ`

For an irreducible scheme `Y` proper over `ℂ` there are a projective scheme `Y'` over `ℂ`, a
closed immersion `j : Y' ⟶ ℙᴺ` and a morphism `π : Y' ⟶ Y` over `ℂ` such that
`(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion and `π` is an isomorphism over a nonempty open
`U ⊆ Y` (`ComplexAnalytic.exists_chow_of_irreducibleSpace`). The scheme `Y'` is irreducible and
`π⁻¹ U` is scheme-theoretically dense in `Y'`. If `Y` is integral, so is `Y'`
(`ComplexAnalytic.exists_chow`).

Over an open `V ⊆ Y`, `π⁻¹ V` is the preimage of `V ×_ℂ ℙᴺ` under the closed immersion `(π, j)`;
for `V = Spec A` this identifies `π⁻¹ V` with a closed subscheme of `ℙᴺ_A`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic

namespace Chow

variable {Y : SchemeLFTℂ.{u}} {N : ℕ} {Z : Scheme.{u}}
  (c : Z ⟶ pullback Y.obj.hom (ProjectiveSpace.toSpec N (ULift.{u} ℂ))) [IsClosedImmersion c]

/-- The scheme `Z` over `ℂ`, for a closed immersion `c : Z ⟶ Y ×_ℂ ℙᴺ`. -/
noncomputable def obj : SchemeLFTℂ.{u} :=
  ⟨Over.mk (c ≫ pullback.fst _ _ ≫ Y.obj.hom), by
    have : LocallyOfFiniteType Y.obj.hom := Y.property
    change LocallyOfFiniteType (c ≫ pullback.fst _ _ ≫ Y.obj.hom)
    infer_instance⟩

/-- The first projection `Z ⟶ Y` over `ℂ`, for `c : Z ⟶ Y ×_ℂ ℙᴺ`. -/
noncomputable def π : obj c ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (c ≫ pullback.fst _ _) (Category.assoc _ _ _))

/-- The second projection `Z ⟶ ℙᴺ` over `ℂ`, for `c : Z ⟶ Y ×_ℂ ℙᴺ`. -/
noncomputable def j : obj c ⟶ projectiveSpace.{u} N :=
  ObjectProperty.homMk (Over.homMk (c ≫ pullback.snd _ _) (by
    change (c ≫ pullback.snd _ _) ≫ ProjectiveSpace.toSpec N _ = c ≫ pullback.fst _ _ ≫ _
    rw [Category.assoc, ← pullback.condition]))

/-- `(π, j) = c`. -/
lemma lift_π_j : pullback.lift (π c).hom.left (j c).hom.left
    ((Over.w (π c).hom).trans (Over.w (j c).hom).symm) = c := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

end Chow

/-- **Chow's lemma over `ℂ`, irreducible case.** For an irreducible scheme `Y` proper over `ℂ`
there are `N`, a scheme `Y'` over `ℂ`, a closed immersion `j : Y' ⟶ ℙᴺ` and a morphism
`π : Y' ⟶ Y` over `ℂ`, such that `(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, `π` restricts to
an isomorphism `π⁻¹ U ≅ U` for some nonempty open `U ⊆ Y`, `Y'` is irreducible and `π⁻¹ U` is
scheme-theoretically dense in `Y'`. -/
theorem exists_chow_of_irreducibleSpace (Y : SchemeLFTℂ.{u}) [IrreducibleSpace Y.obj.left]
    [IsProper Y.obj.hom] :
    ∃ (N : ℕ) (Y' : SchemeLFTℂ.{u}) (j : Y' ⟶ projectiveSpace.{u} N) (π : Y' ⟶ Y)
      (U : Y.obj.left.Opens),
      IsClosedImmersion j.hom.left ∧
      IsClosedImmersion (pullback.lift π.hom.left j.hom.left
        ((Over.w π.hom).trans (Over.w j.hom).symm) :
          Y'.obj.left ⟶ pullback Y.obj.hom (projectiveSpace.{u} N).obj.hom) ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IrreducibleSpace Y'.obj.left ∧
      IsSchemeTheoreticallyDominant (π.hom.left ⁻¹ᵁ U).ι := by
  obtain ⟨N, Z, c, U, hc, hq, hU, hπ, hZ, hd⟩ :=
    AlgebraicGeometry.exists_chow_of_irreducibleSpace Y.obj.hom
  have := hc
  exact ⟨N, Chow.obj c, Chow.j c, Chow.π c, U, hq, (Chow.lift_π_j c).symm ▸ hc, hU, hπ, hZ, hd⟩

/-- **Chow's lemma over `ℂ`.** For an integral scheme `Y` proper over `ℂ` there are `N`, a scheme
`Y'` over `ℂ`, a closed immersion `j : Y' ⟶ ℙᴺ` and a morphism `π : Y' ⟶ Y` over `ℂ`, such that
`(π, j) : Y' ⟶ Y ×_ℂ ℙᴺ` is a closed immersion, `π` restricts to an isomorphism `π⁻¹ U ≅ U` for
some nonempty open `U ⊆ Y`, and `Y'` is integral. -/
theorem exists_chow (Y : SchemeLFTℂ.{u}) [IsIntegral Y.obj.left] [IsProper Y.obj.hom] :
    ∃ (N : ℕ) (Y' : SchemeLFTℂ.{u}) (j : Y' ⟶ projectiveSpace.{u} N) (π : Y' ⟶ Y)
      (U : Y.obj.left.Opens),
      IsClosedImmersion j.hom.left ∧
      IsClosedImmersion (pullback.lift π.hom.left j.hom.left
        ((Over.w π.hom).trans (Over.w j.hom).symm) :
          Y'.obj.left ⟶ pullback Y.obj.hom (projectiveSpace.{u} N).obj.hom) ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IsIntegral Y'.obj.left := by
  obtain ⟨N, Z, c, U, hc, hq, hU, hπ, hZ⟩ := AlgebraicGeometry.exists_chow Y.obj.hom
  have := hc
  exact ⟨N, Chow.obj c, Chow.j c, Chow.π c, U, hq, (Chow.lift_π_j c).symm ▸ hc, hU, hπ, hZ⟩

/-- The scheme `Y'` in Chow's lemma is projective. -/
theorem exists_chow_isProjectiveℂ (Y : SchemeLFTℂ.{u}) [IsIntegral Y.obj.left]
    [IsProper Y.obj.hom] :
    ∃ (Y' : SchemeLFTℂ.{u}) (π : Y' ⟶ Y) (U : Y.obj.left.Opens), IsProjectiveℂ Y' ∧
      (U : Set Y.obj.left).Nonempty ∧ IsIso (π.hom.left ∣_ U) ∧ IsIntegral Y'.obj.left := by
  obtain ⟨N, Y', j, π, U, hj, -, hU, hπ, hY'⟩ := exists_chow Y
  exact ⟨Y', π, U, ⟨N, j, hj⟩, hU, hπ, hY'⟩

end ComplexAnalytic

end
