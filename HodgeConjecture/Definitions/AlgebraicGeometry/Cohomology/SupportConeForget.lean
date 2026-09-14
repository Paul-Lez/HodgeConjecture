/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExact
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.HypercohomologyShift

/-! # Support-forgetting in the actual rational injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X))) :=
  HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat (TopCat.of (Point ℂ X)))

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

end AlgebraicGeometry.ComplexPoint
