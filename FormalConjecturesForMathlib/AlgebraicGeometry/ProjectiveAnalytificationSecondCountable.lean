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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationConnected
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Mathlib.Geometry.Manifold.Metrizable

/-!
# Second-countability of projective analytifications

A dimensioned smooth projective complex analytification is compact and has manifold charts
modeled on a finite-dimensional complex vector space. Compactness gives sigma-compactness, so the
charted-space second-countability theorem applies. Standard consequences include separability,
first countability, and the Lindelöf property. The independently proved Hausdorff theorem for
projective analytifications then supplies the remaining hypothesis of Mathlib's manifold
metrizability theorem.
-/

@[expose] public noncomputable section

open Topology

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

/-- A smooth projective complex analytification has a second-countable topology. -/
noncomputable instance instSecondCountableTopology
    (V : DimensionedSmoothProjectiveComplexVariety) :
    SecondCountableTopology V.analyticPoint := by
  let _ : SigmaCompactSpace V.analyticPoint := inferInstance
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    ComplexPoint.analyticChartedSpace V.structureMap V.dimension
  exact ChartedSpace.secondCountable_of_sigmaCompact
    (Fin V.dimension → ℂ) V.analyticPoint

/-- A smooth projective complex analytification is separable. -/
noncomputable instance instSeparableSpace
    (V : DimensionedSmoothProjectiveComplexVariety) :
    TopologicalSpace.SeparableSpace V.analyticPoint := inferInstance

/-- A smooth projective complex analytification is first countable. -/
noncomputable instance instFirstCountableTopology
    (V : DimensionedSmoothProjectiveComplexVariety) :
    FirstCountableTopology V.analyticPoint := inferInstance

/-- A smooth projective complex analytification is Lindelöf. -/
noncomputable instance instLindelofSpace
    (V : DimensionedSmoothProjectiveComplexVariety) :
    LindelofSpace V.analyticPoint := inferInstance

/-- A smooth projective complex analytification is metrizable. -/
noncomputable instance instMetrizableSpace
    (V : DimensionedSmoothProjectiveComplexVariety) :
    TopologicalSpace.MetrizableSpace V.analyticPoint := by
  let _ : SigmaCompactSpace V.analyticPoint := inferInstance
  let _ : ChartedSpace (Fin V.dimension → ℂ) V.analyticPoint :=
    ComplexPoint.analyticChartedSpace V.structureMap V.dimension
  let _ : T2Space V.analyticPoint := inferInstance
  exact Manifold.metrizableSpace
    (modelWithCornersSelf ℝ (Fin V.dimension → ℂ)) V.analyticPoint

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
