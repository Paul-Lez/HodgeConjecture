/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiScalarComparison
public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact
public import Other.AlgebraicTopology.IntegralSingularHomologyFinite

/-!
# Integral denominator clearing from a finite good cover

This file reduces `HasIntegralDenominatorClearing` to the existence of a finite good cover of
the analytic space, through the integral and rational Betti comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The analytic complex-point space admits a finite good cover: finitely many open sets, all of
whose nonempty finite intersections are contractible. -/
def HasFiniteGoodCover : Prop :=
  ∃ (ι : Type) (_ : LinearOrder ι) (U : ι → Set (ComplexPoint X)),
    AlgebraicTopology.Singular.FiniteGoodCover (TopCat.of (ComplexPoint X)) U

/-- A finite good cover makes every integral singular homology group finitely generated. -/
theorem module_finite_singularHomology_of_hasFiniteGoodCover (h : HasFiniteGoodCover X) (n : ℕ) :
    Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n) := by
  obtain ⟨ι, hι, U, hU⟩ := h
  let := hι
  exact AlgebraicTopology.Singular.singularChainComplex_homology_module_finite_of_finiteGoodCover
    hU n

end AlgebraicGeometry.ComplexPoint
