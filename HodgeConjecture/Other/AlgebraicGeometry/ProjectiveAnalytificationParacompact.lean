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

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)
  [ProjectiveSpace.IsProjective structureMap]

/-- Every open subset of a smooth projective complex analytification is paracompact. -/
theorem openParacompactSpace [SmoothOfRelativeDimension d structureMap]
    (U : Opens (ComplexPoint X structureMap)) : ParacompactSpace U := by
  let _ : ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
    analyticChartedSpace structureMap d
  exact opens_paracompactSpace_of_compact_chartedSpace (H := Fin d → ℂ) U

/-- Every term of the rational singular-cochain sheaf resolution on a smooth projective
analytification is flasque. -/
theorem rationalSingularCochainSheafIsFlasque [SmoothOfRelativeDimension d structureMap]
    (n : ℕ) :
    TopCat.Sheaf.IsFlasque
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ
        (TopCat.of (ComplexPoint X structureMap)) n) := by
  let _ : ∀ U : Opens (ComplexPoint X structureMap), ParacompactSpace U :=
    openParacompactSpace structureMap d
  infer_instance

/-- Ordinary rational singular cochains compute the global sections of the chosen
singular-cochain sheaf complex on a smooth projective analytification. -/
theorem rationalSingularCochain_globalComparison_quasiIso
    [SmoothOfRelativeDimension d structureMap] :
    QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X structureMap))) := by
  let _ : ∀ U : Opens (ComplexPoint X structureMap), ParacompactSpace U :=
    openParacompactSpace structureMap d
  exact AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex_quasiIso

end AlgebraicGeometry.ComplexPoint
