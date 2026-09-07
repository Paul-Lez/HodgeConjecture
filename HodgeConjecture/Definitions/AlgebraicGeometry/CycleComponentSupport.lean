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

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoints

/-!
# Analytic support of an irreducible algebraic subset

The support attached to a scheme point is the preimage of its Zariski closure in the analytic
space of complex points. This construction needs neither a cycle nor a Chow-group quotient.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

/-- The complex points supported on the irreducible closed subset with generic point `x`. -/
def cycleComponentSupport
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    Set (ComplexPoint X structureMap) :=
  ComplexPoint.underlying ⁻¹' closure {x}

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (Z : TopologicalSpace.Closeds X) :
    IsClosed ((@ComplexPoint.underlying X structureMap) ⁻¹'
      (Z : Set X)) := by
  rw [← isOpen_compl_iff]
  let U : X.Opens := ⟨(Z : Set X)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  change @IsOpen (ComplexPoint X structureMap) ComplexPoint.analyticTopology
    ((@ComplexPoint.underlying X structureMap) ⁻¹' (Z : Set X))ᶜ
  rw [show ((@ComplexPoint.underlying X structureMap) ⁻¹'
      (Z : Set X))ᶜ = ComplexPoint.overOpen U by
    apply Set.ext
    intro z
    change (¬ComplexPoint.underlying z ∈ Z) ↔
      ComplexPoint.underlying z ∈ (Z : Set X)ᶜ
    rfl]
  exact ComplexPoint.isOpen_overOpen U

lemma isClosed_cycleComponentSupport
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    IsClosed (cycleComponentSupport structureMap x) :=
  isClosed_complexPoint_underlying_preimage structureMap
    ⟨closure {x}, isClosed_closure⟩

end AlgebraicGeometry
