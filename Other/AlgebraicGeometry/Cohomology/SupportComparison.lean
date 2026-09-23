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

public import Other.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.CochainResolution
public import HodgeConjecture.Mathlib.Algebra.Homology.LiftToInjective
public import HodgeConjecture.Lemmas.Algebra.Homology.MappingConeQuasiIso
public import Mathlib.Algebra.Homology.ModelCategory.Injective

/-!
# Singular comparison with support

This file proves the categorical input needed to replace the constant-sheaf term in the
mapping-cone model for supported cohomology by a singular-cochain resolution. In particular,
direct image along an open embedding preserves injective additive sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen



namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational constant-to-singular comparison is a monomorphism of integer-indexed sheaf
complexes. -/
lemma rationalToSingularCochainComplexInt_mono :
    Mono (rationalToSingularCochainComplexInt X) := by
  exact AlgebraicTopology.Singular.constantsToSingularCochainComplexInt_mono ℚ _

variable [IsIntegral X.left] [Smooth X.hom]

local instance bettiSupportComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance bettiSupportComparisonMono : Mono (rationalToSingularCochainComplexInt X) :=
  rationalToSingularCochainComplexInt_mono X

local instance bettiSupportComparisonQuasiIso : QuasiIso (rationalToSingularCochainComplexInt X) :=
  rationalToSingularCochainComplexInt_quasiIso X

end AlgebraicGeometry.ComplexPoint
