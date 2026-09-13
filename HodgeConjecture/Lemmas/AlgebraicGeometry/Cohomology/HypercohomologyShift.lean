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

namespace TopCat.Sheaf

variable (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
  (s n n' : ℤ) (h : n + s = n')

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyShiftSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

end AlgebraicGeometry.ComplexPoint
