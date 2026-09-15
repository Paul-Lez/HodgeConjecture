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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularComparison

/-!
# Singular and constant-sheaf comparison

On the analytic space of a smooth complex scheme, the rational constant sheaf is resolved by
the sheafified rational singular-cochain complex. Localizing at quasi-isomorphisms gives a
canonical comparison equivalence in every cohomological degree.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance singularComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _

local instance singularComparisonAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

/-- The rational constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def rationalToSingularCochainComplexInt :
    (constantFieldSheafComplexIntPlus ℚ X).obj ⟶
      singularCochainSheafComplexInt X ℚ :=
  constantsToSingularCochainComplexInt X ℚ

/-- The rational constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma rationalToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (rationalToSingularCochainComplexInt X) := by
  exact constantsToSingularCochainComplexInt_quasiIso X ℚ

/-- The rational singular-cochain resolution as a bounded-below complex. -/
abbrev rationalSingularCochainComplexIntPlus :
    CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨singularCochainSheafComplexInt X ℚ, ⟨0, inferInstance⟩⟩

/-- Rational constant-sheaf cohomology is canonically additively equivalent to the
hypercohomology of its singular-cochain resolution. -/
def rationalCohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    H^n(X; ℚ) ≃+
      ↥((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).obj
        (rationalSingularCochainComplexIntPlus X)) :=
  let f : constantFieldSheafComplexIntPlus ℚ X ⟶
      rationalSingularCochainComplexIntPlus X :=
    ⟨rationalToSingularCochainComplexInt X⟩
  letI : QuasiIso f.hom := rationalToSingularCochainComplexInt_quasiIso X
  (asIso
    ((ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map f)).addCommGroupIsoToAddEquiv

@[simp]
lemma rationalCohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : H^n(X; ℚ)) :
    rationalCohomologySingularCochainAddEquiv X n α =
      (ℍ[AddCommGrpCat]^n(TopCat.of (ComplexPoint X))).map
        (⟨rationalToSingularCochainComplexInt X⟩ :
          constantFieldSheafComplexIntPlus ℚ X ⟶
            rationalSingularCochainComplexIntPlus X) α := by
  change ((rationalCohomologySingularCochainAddEquiv X n).toAddMonoidHom α) = _
  rfl

end AlgebraicGeometry.ComplexPoint
