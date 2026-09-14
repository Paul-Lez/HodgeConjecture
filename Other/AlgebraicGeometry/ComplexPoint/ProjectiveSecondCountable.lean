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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

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

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))
  [IsProjective X.hom]

/-- A smooth projective complex analytification has a second-countable topology. -/
theorem secondCountableTopology [IsIntegral X.left] [Smooth X.hom] :
    SecondCountableTopology (Point ℂ X) := by
  let : SigmaCompactSpace (Point ℂ X) := inferInstance
  exact ChartedSpace.secondCountable_of_sigmaCompact (Fin (dim X.left) → ℂ) (Point ℂ X)

/-- A smooth projective complex analytification is separable. -/
theorem separableSpace [IsIntegral X.left] [Smooth X.hom] :
    TopologicalSpace.SeparableSpace (Point ℂ X) := by
  let : SecondCountableTopology (Point ℂ X) :=
    secondCountableTopology X
  infer_instance

/-- A smooth projective complex analytification is first countable. -/
theorem firstCountableTopology [IsIntegral X.left] [Smooth X.hom] :
    FirstCountableTopology (Point ℂ X) := by
  let : SecondCountableTopology (Point ℂ X) :=
    secondCountableTopology X
  infer_instance

/-- A smooth projective complex analytification is Lindelöf. -/
theorem lindelofSpace [IsIntegral X.left] [Smooth X.hom] :
    LindelofSpace (Point ℂ X) := by
  let : SecondCountableTopology (Point ℂ X) :=
    secondCountableTopology X
  infer_instance

/-- A smooth projective complex analytification is metrizable. -/
theorem metrizableSpace [IsIntegral X.left] [Smooth X.hom] :
    TopologicalSpace.MetrizableSpace (Point ℂ X) := by
  let : SigmaCompactSpace (Point ℂ X) := inferInstance
  let : SecondCountableTopology (Point ℂ X) :=
    secondCountableTopology X
  exact Manifold.metrizableSpace (modelWithCornersSelf ℝ (Fin (dim X.left) → ℂ))
    (Point ℂ X)

end AlgebraicGeometry.ComplexPoint
