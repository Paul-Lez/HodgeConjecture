/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.ProjectiveGAGA

/-!
# Proper schemes over `ℂ`

A scheme `X` locally of finite type over `ℂ` is *proper* (`ComplexAnalytic.IsProperℂ`) if its
structure morphism `X ⟶ Spec ℂ` is proper. We show:

- `ComplexAnalytic.IsProjectiveℂ.isProperℂ`: projective schemes are proper;
- `ComplexAnalytic.IsProperℂ.of_isClosedImmersion`: a scheme admitting a closed immersion into a
  proper scheme is proper;
- `ComplexAnalytic.IsProperℂ.compactSpace`: the underlying space of a proper scheme is compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace ComplexAnalytic

/-- A scheme locally of finite type over `ℂ` is **proper** if its structure morphism
`X ⟶ Spec ℂ` is proper. -/
def IsProperℂ (X : SchemeLFTℂ.{u}) : Prop :=
  IsProper X.obj.hom

/-- The structure morphism of a proper scheme over `ℂ` is proper. -/
lemma IsProperℂ.isProper {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X) : IsProper X.obj.hom :=
  hX

/-- A scheme admitting a closed immersion over `ℂ` into a proper scheme is proper. -/
theorem IsProperℂ.of_isClosedImmersion {Y X : SchemeLFTℂ.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i.hom.left] (hX : IsProperℂ X) : IsProperℂ Y := by
  haveI : IsProper X.obj.hom := hX
  change IsProper Y.obj.hom
  rw [← Over.w i.hom]
  infer_instance

/-- **Projective schemes over `ℂ` are proper.** -/
theorem IsProjectiveℂ.isProperℂ {X : SchemeLFTℂ.{u}} (hX : IsProjectiveℂ X) : IsProperℂ X := by
  obtain ⟨n, i, hi⟩ := hX
  exact IsProperℂ.of_isClosedImmersion i (isProper_projectiveSpace_hom n)

/-- The underlying topological space of a proper scheme over `ℂ` is compact. -/
theorem IsProperℂ.compactSpace {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X) :
    CompactSpace X.obj.left := by
  haveI : IsProper X.obj.hom := hX
  exact QuasiCompact.compactSpace_of_compactSpace X.obj.hom

end ComplexAnalytic

end
