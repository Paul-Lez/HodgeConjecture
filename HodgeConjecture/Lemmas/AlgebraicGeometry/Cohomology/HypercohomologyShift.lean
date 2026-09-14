/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.HomComplexShiftNaturality
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.HypercohomologyNaturality
/-! # Shift normalization of hypercohomology and global sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyShiftSheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X))) :=
  HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X)))

end AlgebraicGeometry.ComplexPoint
