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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexSingularComparison
public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration

/-!
# Betti and constant-sheaf comparison

On the analytic space of a smooth complex scheme, the rational constant sheaf is resolved by
the sheafified rational singular-cochain complex. Localizing at quasi-isomorphisms gives a
canonical comparison equivalence in every cohomological degree.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

local instance bettiSheafComparisonTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

/-- The rational constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def rationalToSingularCochainComplexInt :
    constantRationalSheafComplexInt structureMap ⟶
      singularCochainSheafComplexInt structureMap ℚ :=
  constantsToSingularCochainComplexInt structureMap ℚ

/-- The rational constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma rationalToSingularCochainComplexInt_quasiIso
    [SmoothOfRelativeDimension d structureMap] :
    QuasiIso (rationalToSingularCochainComplexInt structureMap) := by
  change QuasiIso (constantsToSingularCochainComplexInt structureMap ℚ)
  exact constantsToSingularCochainComplexInt_quasiIso structureMap d ℚ

/-- Hypercohomology of the integer-indexed rational singular-cochain sheaf complex. -/
abbrev RationalSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (singularCochainSheafComplexInt structureMap ℚ) n

/-- Rational constant-sheaf cohomology is canonically equivalent to the hypercohomology of its
singular-cochain resolution. -/
def rationalCohomologySingularCochainEquiv
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    RationalCohomology structureMap n ≃
      RationalSingularCochainHypercohomology structureMap n :=
  Localization.SmallShiftedHom.postcompEquiv
    (rationalToSingularCochainComplexInt structureMap)
    (rationalToSingularCochainComplexInt_quasiIso structureMap d)

/-- The comparison equivalence is the map on hypercohomology induced by the canonical
constant-to-singular-cochain morphism. -/
lemma rationalCohomologySingularCochainEquiv_apply
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : RationalCohomology structureMap n) :
    rationalCohomologySingularCochainEquiv structureMap d n α =
      hypercohomologyMap structureMap
        (rationalToSingularCochainComplexInt structureMap) n α :=
  rfl

/-- The rational constant-to-singular comparison is additive. -/
def rationalCohomologySingularCochainAddEquiv
    [SmoothOfRelativeDimension d structureMap] (n : ℤ) :
    RationalCohomology structureMap n ≃+
      RationalSingularCochainHypercohomology structureMap n where
  toEquiv := rationalCohomologySingularCochainEquiv structureMap d n
  map_add' α β :=
    (hypercohomologyMap structureMap
      (rationalToSingularCochainComplexInt structureMap) n).map_add α β

@[simp]
lemma rationalCohomologySingularCochainAddEquiv_apply
    [SmoothOfRelativeDimension d structureMap] (n : ℤ)
    (α : RationalCohomology structureMap n) :
    rationalCohomologySingularCochainAddEquiv structureMap d n α =
      hypercohomologyMap structureMap
        (rationalToSingularCochainComplexInt structureMap) n α :=
  rfl

end AlgebraicGeometry.ComplexPoint
