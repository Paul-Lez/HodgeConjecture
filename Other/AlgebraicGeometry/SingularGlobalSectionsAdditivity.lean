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

public import Other.AlgebraicGeometry.BettiGlobalSectionsComparison
/-!
# The singular global-sections comparison as a `ℚ`-linear equivalence

The singular comparison is built as an additive equivalence in
`Definitions/AlgebraicGeometry/Cohomology/GlobalSections.lean`. Because both sides are
`ℚ`-vector spaces and every additive map between `ℚ`-modules is `ℚ`-linear, it upgrades to a
`ℚ`-linear equivalence with no further work. That upgrade is not needed to state the
conjecture, so it is recorded here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance bettiGlobalSectionsAdditivityHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Rational constant-sheaf cohomology and rational singular cohomology are equivalent as
`ℚ`-vector spaces.  Both sides are `ℚ`-modules, and every additive map between `ℚ`-modules
is automatically `ℚ`-linear, so the additive comparison upgrades to a linear equivalence with
no further work. -/
def rationalCohomologyLinearEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    H^(n : ℤ)(X; ℚ) ≃ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ
        (TopCat.of (ComplexPoint X)) n :=
  (rationalCohomologyAddEquivSingularCohomology X n).toLinearEquiv
    (map_rat_smul (rationalCohomologyAddEquivSingularCohomology X n))

/-- The `ℚ`-linear singular comparison has the same underlying function as the additive one. -/
@[simp]
lemma coe_rationalCohomologyLinearEquivSingularCohomology
    [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (n : ℕ) :
    ⇑(rationalCohomologyLinearEquivSingularCohomology X n) =
      ⇑(rationalCohomologyAddEquivSingularCohomology X n) :=
  rfl

end AlgebraicGeometry.ComplexPoint
