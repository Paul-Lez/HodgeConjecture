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

public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytification
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Other.AlgebraicTopology.SingularSubdivisionCochainSheaf

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

namespace SmoothProjectiveComplexVariety

variable (V : SmoothProjectiveComplexVariety) (d : ℕ)

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
theorem openParacompactSpace [SmoothOfRelativeDimension d V.structureMap]
    (U : Opens V.analyticPoint) : ParacompactSpace U := by
  let _ : ChartedSpace (Fin d → ℂ) V.analyticPoint :=
    analyticChartedSpace V.structureMap d
  exact opens_paracompactSpace_of_compact_chartedSpace
    (H := Fin d → ℂ) U

/-- Every term of the rational singular-cochain sheaf resolution on a smooth projective
analytification is flasque. -/
theorem rationalSingularCochainSheafIsFlasque [SmoothOfRelativeDimension d V.structureMap]
    (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ
        (TopCat.of V.analyticPoint) n) := by
  let _ : ∀ U : Opens V.analyticPoint, ParacompactSpace U := openParacompactSpace V d
  infer_instance

/-- Ordinary rational singular cochains compute the global sections of the chosen
singular-cochain sheaf complex on a smooth projective analytification. -/
theorem rationalSingularCochain_globalComparison_quasiIso
    [SmoothOfRelativeDimension d V.structureMap] :
    QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of V.analyticPoint)) := by
  let _ : ∀ U : Opens V.analyticPoint, ParacompactSpace U := openParacompactSpace V d
  exact
    AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso

end SmoothProjectiveComplexVariety

end AlgebraicGeometry.ComplexPoint
