/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import HodgeConjecture.Definitions.AlgebraicTopology.SheafCohomologyWithSupport

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

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- Rational sheaf cohomology with support in a closed subset of the analytic complex-point space,
using Ext. -/
abbrev RationalCohomologyWithClosedSupport
    (Z : Closeds (ComplexPoint (Over.mk structureMap))) (n : ℕ) :=
  TopCat.Sheaf.cohomologyWithSupport (TopCat.of (ComplexPoint (Over.mk structureMap))) Z
    (constantFieldSheaf ℚ structureMap) n

instance (Z : Closeds (ComplexPoint (Over.mk structureMap))) (n : ℕ) :
    AddCommGroup (RationalCohomologyWithClosedSupport structureMap Z n) :=
  inferInstanceAs (AddCommGroup
    (((TopCat.Sheaf.cohomologyWithSupportFunctor
      (TopCat.of (ComplexPoint (Over.mk structureMap))) n).obj Z).obj
        (constantFieldSheaf ℚ structureMap)))

/-- Rational compactly supported cohomology of the analytic complex-point space. -/
abbrev RationalCompactlySupportedCohomology (n : ℕ) : AddCommGrpCat :=
  TopCat.Sheaf.compactlySupportedCohomology (TopCat.of (ComplexPoint (Over.mk structureMap)))
    (constantFieldSheaf ℚ structureMap) n

/-- A rational class with specified compact closed support defines a compactly supported class. -/
def toRationalCompactlySupportedCohomology
    (K : CompactCloseds (ComplexPoint (Over.mk structureMap))) (n : ℕ) :
    AddCommGrpCat.of (RationalCohomologyWithClosedSupport structureMap K.1 n) ⟶
      RationalCompactlySupportedCohomology structureMap n :=
  TopCat.Sheaf.toCompactlySupportedCohomology (TopCat.of (ComplexPoint (Over.mk structureMap))) K
    (constantFieldSheaf ℚ structureMap) n

end AlgebraicGeometry.ComplexPoint
