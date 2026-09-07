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
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Mathlib.Geometry.Manifold.Metrizable

/-!
# Second-countability of projective analytifications

A smooth projective complex analytification is compact and has manifold charts
modeled on a finite-dimensional complex vector space. Compactness gives sigma-compactness, so the
charted-space second-countability theorem applies. Standard consequences include separability,
first countability, and the Lindelöf property. The independently proved Hausdorff theorem for
projective analytifications then supplies the remaining hypothesis of Mathlib's manifold
metrizability theorem.
-/

@[expose] public noncomputable section

open Topology

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)
  [ProjectiveSpace.IsProjective structureMap]

/-- A smooth projective complex analytification has a second-countable topology. -/
theorem secondCountableTopology [SmoothOfRelativeDimension d structureMap] :
    SecondCountableTopology (ComplexPoint X structureMap) := by
  let _ : SigmaCompactSpace (ComplexPoint X structureMap) := inferInstance
  let _ : ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
    analyticChartedSpace structureMap d
  exact ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℂ) (ComplexPoint X structureMap)

/-- A smooth projective complex analytification is separable. -/
theorem separableSpace [SmoothOfRelativeDimension d structureMap] :
    TopologicalSpace.SeparableSpace (ComplexPoint X structureMap) := by
  let _ : SecondCountableTopology (ComplexPoint X structureMap) :=
    secondCountableTopology structureMap d
  infer_instance

/-- A smooth projective complex analytification is first countable. -/
theorem firstCountableTopology [SmoothOfRelativeDimension d structureMap] :
    FirstCountableTopology (ComplexPoint X structureMap) := by
  let _ : SecondCountableTopology (ComplexPoint X structureMap) :=
    secondCountableTopology structureMap d
  infer_instance

/-- A smooth projective complex analytification is Lindelöf. -/
theorem lindelofSpace [SmoothOfRelativeDimension d structureMap] :
    LindelofSpace (ComplexPoint X structureMap) := by
  let _ : SecondCountableTopology (ComplexPoint X structureMap) :=
    secondCountableTopology structureMap d
  infer_instance

/-- A smooth projective complex analytification is metrizable. -/
theorem metrizableSpace [SmoothOfRelativeDimension d structureMap] :
    TopologicalSpace.MetrizableSpace (ComplexPoint X structureMap) := by
  let _ : SigmaCompactSpace (ComplexPoint X structureMap) := inferInstance
  let _ : ChartedSpace (Fin d → ℂ) (ComplexPoint X structureMap) :=
    analyticChartedSpace structureMap d
  let _ : SecondCountableTopology (ComplexPoint X structureMap) :=
    secondCountableTopology structureMap d
  exact Manifold.metrizableSpace (modelWithCornersSelf ℝ (Fin d → ℂ))
    (ComplexPoint X structureMap)

end AlgebraicGeometry.ComplexPoint
