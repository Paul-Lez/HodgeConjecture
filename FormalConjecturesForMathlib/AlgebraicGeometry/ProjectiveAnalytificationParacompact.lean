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

public import FormalConjecturesForMathlib.AlgebraicGeometry.DimensionedSmoothProjective
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytification
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularSubdivisionCochainSheaf

/-!
# Paracompact open subsets of smooth projective analytifications

A smooth projective complex variety has a compact Hausdorff analytification and algebraic
coordinate charts modeled on a finite-dimensional complex vector space. Every open subset is
therefore paracompact. This supplies the hereditary-paracompactness input for the flasque
singular-cochain resolution.
-/

@[expose] public noncomputable section

open TopologicalSpace
open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

namespace DimensionedSmoothProjectiveComplexVariety

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
instance instOpenParacompactSpace
    (V : DimensionedSmoothProjectiveComplexVariety)
    (U : Opens V.analyticPoint) : ParacompactSpace U := by
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    analyticChartedSpace V.structureMap V.dimension
  exact opens_paracompactSpace_of_compact_chartedSpace
    (H := Fin V.dimension → ℂ) U

/-- Every term of the rational singular-cochain sheaf resolution on a smooth projective
analytification is flasque. -/
instance instRationalSingularCochainSheafIsFlasque
    (V : DimensionedSmoothProjectiveComplexVariety) (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ
        (TopCat.of V.analyticPoint) n) := by
  infer_instance

/-- Ordinary rational singular cochains compute the global sections of the chosen
singular-cochain sheaf complex on a smooth projective analytification. -/
theorem rationalSingularCochain_globalComparison_quasiIso
    (V : DimensionedSmoothProjectiveComplexVariety) :
    QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of V.analyticPoint)) := by
  exact
    AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso

end DimensionedSmoothProjectiveComplexVariety

end AlgebraicGeometry.ComplexPoint
