/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import Other.AlgebraicTopology.SheafCohomologyWithSupport

/-!
# Compactly supported rational cohomology of the analytic complex-point space

These definitions specialize the general Ext and filtered-colimit construction to the
rational constant sheaf on the analytic complex-point space. They require no smoothness,
properness, or separation hypotheses. The closed-support API uses nonnegative degrees,
as does Mathlib's sheaf cohomology.

The arbitrary-subset, integer-degree cone model in `CohomologyWithSupport` remains a separate
API; identifying its closed-support specialization with this Ext model requires a comparison
theorem.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- Rational sheaf cohomology with support in a closed subset of the analytic complex-point space,
using Ext. -/
abbrev RationalCohomologyWithClosedSupport
    (Z : Closeds (ComplexPoint X)) (n : ℕ) :=
  TopCat.Sheaf.cohomologyWithSupport (TopCat.of (ComplexPoint X)) Z
    (constantFieldSheaf ℚ X) n

instance (Z : Closeds (ComplexPoint X)) (n : ℕ) :
    AddCommGroup (RationalCohomologyWithClosedSupport X Z n) :=
  inferInstanceAs (AddCommGroup
    (((TopCat.Sheaf.cohomologyWithSupportFunctor
      (TopCat.of (ComplexPoint X)) n).obj Z).obj
        (constantFieldSheaf ℚ X)))

/-- Rational compactly supported cohomology of the analytic complex-point space. -/
abbrev RationalCompactlySupportedCohomology (n : ℕ) : AddCommGrpCat :=
  TopCat.Sheaf.compactlySupportedCohomology (TopCat.of (ComplexPoint X))
    (constantFieldSheaf ℚ X) n

/-- A rational class with specified compact closed support defines a compactly supported class. -/
def toRationalCompactlySupportedCohomology
    (K : CompactCloseds (ComplexPoint X)) (n : ℕ) :
    AddCommGrpCat.of (RationalCohomologyWithClosedSupport X K.1 n) ⟶
      RationalCompactlySupportedCohomology X n :=
  TopCat.Sheaf.toCompactlySupportedCohomology (TopCat.of (ComplexPoint X)) K
    (constantFieldSheaf ℚ X) n

end AlgebraicGeometry.ComplexPoint
