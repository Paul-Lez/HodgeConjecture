/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.Algebra.Homology.MapExtendNaturality
public import Other.AlgebraicGeometry.Cohomology.SupportConeComparison
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportSingularGlobal

import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.KInjectiveHom

/-!
# Hypercohomology and singular cohomology with support

This file develops the bounded-below flasque comparison needed for cohomology with support.
It applies the same explicit injective-replacement argument used for ordinary singular
cohomology to the mapping cone of singular restriction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

universe u v

variable (X : Over (Spec ↧ℂ))

local instance bettiSupportHypercohomologyComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bettiSupportHypercohomologyAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard AddCommGrpCat

/-- Let `X` be a scheme over `ℂ`, `K` an integer-indexed complex of sheaves of abelian groups on its
analytic space, and `n` an integer. This additive equivalence identifies hypercohomology
`ℍ^n(X(ℂ); K)` with `Hom_D(ℤ[0], K[n])`, morphisms in the derived category of sheaves on `X(ℂ)`. -/
def hypercohomologyAddEquivDerived
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ) :
    ℍ^n(X; K) ≃+
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj K) n where
  toEquiv := Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q
  map_add' := hypercohomologyEquiv_add X K n

end AlgebraicGeometry.ComplexPoint
