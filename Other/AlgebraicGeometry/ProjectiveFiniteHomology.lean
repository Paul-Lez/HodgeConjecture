/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexPointRealManifold
public import Other.AlgebraicGeometry.IntegralDenominatorClearing
public import Other.Geometry.Manifold.CompactManifoldFiniteHomology

/-!
# Finite generation of the homology of a smooth projective variety

The analytic space of a smooth projective integral complex variety is a compact Hausdorff real
smooth manifold, so its integral singular homology is finitely generated. This discharges the
topological obligation `HasFiniteSecondHomology`, and hence integral denominator clearing: the
rational Lefschetz `(1, 1)` theorem now depends only on the divisor representation of unit-sheaf
extensions.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The integral singular homology of the analytic space of a smooth projective integral complex
variety is finitely generated in every degree. -/
theorem module_finite_singularHomology (n : ℕ) :
    Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n) :=
  AlgebraicTopology.Singular.module_finite_homology_of_compactSpace_isManifold
    𝓘(ℝ, Fin (dim X.left) → ℂ) (M := ComplexPoint X) n

/-- The topological obligation holds for every smooth projective integral complex variety. -/
theorem hasFiniteSecondHomology : HasFiniteSecondHomology X :=
  module_finite_singularHomology X 2

/-- Integral denominator clearing holds for every smooth projective integral complex variety. -/
theorem hasIntegralDenominatorClearing : HasIntegralDenominatorClearing X :=
  hasIntegralDenominatorClearing_of_hasFiniteSecondHomology X (hasFiniteSecondHomology X)

/-- The rational Lefschetz `(1, 1)` theorem follows from the divisor representation of unit-sheaf
extensions alone. -/
theorem _root_.RationalLefschetzOneOne.of_divisor
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations (fun X _ _ _ ↦ hasIntegralDenominatorClearing X) hdivisor

end AlgebraicGeometry.ComplexPoint
