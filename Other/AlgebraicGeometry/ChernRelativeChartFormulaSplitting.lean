/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeClass

/-!
# How the canonical relative class depends on the splitting

The relative first Chern class of `Other/AlgebraicGeometry/ChernRelativeClass.lean` is built from
a lift `ℓ` of the constant integer section `1` over an open set `Ω`. Two such lifts differ by a
unit section `w` of `𝒪ˣ` over `Ω`, and this file computes the difference of the two relative
classes: it is the image of `w` under the composite

  `Γ(Ω, 𝒪ˣ) ⟶ Hom(ℤ_X, j_*(𝒪ˣ|_Ω)) --inr--> Hom(ℤ_X, cone(η))`,

i.e. the "boundary of the class of `w`". This is the first half of the localisation statement
needed for the chart formula, and it is the precise form of the ambiguity that forces the
quantifier over `ℓ` in `HasRelativeChernChartFormulaExists` to be existential.

Everything here happens at the level of *morphisms of complexes*, where sums and differences are
available, so no group structure on `SmallShiftedHom` is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance chernRelativeSplittingTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable {X d}

namespace HolomorphicUnitExtension

variable (E : HolomorphicUnitExtension X d) (Ω : Opens (TopCat.of (ComplexPoint X)))
  (ℓ₁ ℓ₂ : E.middle.obj.obj (op Ω))
  (hℓ₁ : E.projection.hom.app (op Ω) ℓ₁ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection)
  (hℓ₂ : E.projection.hom.app (op Ω) ℓ₂ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection)

/-- The two factorisations of the restriction morphism attached to two lifts of `1` over `Ω`
differ by a morphism factoring through the projection: their difference kills the inclusion of the
unit sheaf, and the projection is a cokernel of that inclusion. -/
theorem exists_restrictionFactorisation_eq_add :
    ∃ s : constantIntegerSheaf X ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d),
      E.restrictionFactorisation Ω ℓ₂ hℓ₂ =
        E.restrictionFactorisation Ω ℓ₁ hℓ₁ + E.projection ≫ s := by
  have hzero : E.inclusion ≫
      (E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁) = 0 := by
    rw [Preadditive.comp_sub, E.inclusion_comp_restrictionFactorisation Ω ℓ₂ hℓ₂,
      E.inclusion_comp_restrictionFactorisation Ω ℓ₁ hℓ₁, sub_self]
  haveI := E.shortExact.epi_g
  obtain ⟨s, hs⟩ := Cofork.IsColimit.desc' E.shortExact.exact.gIsCokernel
    (E.restrictionFactorisation Ω ℓ₂ hℓ₂ - E.restrictionFactorisation Ω ℓ₁ hℓ₁) hzero
  exact ⟨s, by rw [show E.projection ≫ s = _ from hs]; abel⟩

end HolomorphicUnitExtension

end AlgebraicGeometry.ComplexPoint
