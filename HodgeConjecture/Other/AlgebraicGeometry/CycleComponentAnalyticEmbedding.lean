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
public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytification
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Analytic embedding of a cycle component

The analytification of the reduced closure of a scheme point is homeomorphic to its closed
support in the ambient analytification.  The result follows from the general theorem that a
closed immersion induces a closed topological embedding on complex points, together with the
explicit identification of its range with the component support.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

noncomputable local instance cycleComponentTopology
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    TopologicalSpace
      (ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap)) :=
  analyticTopology

/-- The complex-point map of a reduced cycle component is a closed topological embedding. -/
lemma cycleComponentMap_isClosedEmbedding
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    IsClosedEmbedding (cycleComponentMap structureMap x) := by
  exact isClosedEmbedding_map_of_closedImmersion
    (i := cycleComponentι X x) (structureMapA :=
      cycleComponentι X x ≫ structureMap) (structureMapB := structureMap) rfl

/-- The analytification of a reduced cycle component is canonically homeomorphic to its
analytic support in the ambient variety. -/
def cycleComponentPointHomeomorphSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap) ≃ₜ
      cycleComponentSupport structureMap x :=
  (cycleComponentMap_isClosedEmbedding structureMap x).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_cycleComponentMap structureMap x))

@[simp]
lemma cycleComponentPointHomeomorphSupport_apply
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap)) :
    cycleComponentPointHomeomorphSupport structureMap x z =
      cycleComponentSupportMap structureMap x z := by
  rfl

/-- The underlying equivalence of the component-support homeomorphism is the previously
constructed point equivalence. -/
lemma cycleComponentPointHomeomorphSupport_toEquiv
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    (cycleComponentPointHomeomorphSupport structureMap x).toEquiv =
      cycleComponentPointEquivSupport structureMap x := by
  apply Equiv.ext
  intro z
  rfl

/-- The smooth analytic locus of a component is homeomorphic to its image in the ambient
analytic variety. -/
def cycleComponentSmoothPointHomeomorphSupport
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X) :
    cycleComponentSmoothAnalyticLocus structureMap x ≃ₜ
      cycleComponentSmoothSupport structureMap x :=
  (cycleComponentMap_isClosedEmbedding structureMap x).toIsEmbedding.homeomorphImage
    (cycleComponentSmoothAnalyticLocus structureMap x)

@[simp]
lemma cycleComponentSmoothPointHomeomorphSupport_apply
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (x : X)
    (z : cycleComponentSmoothAnalyticLocus structureMap x) :
    (cycleComponentSmoothPointHomeomorphSupport structureMap x z : (ComplexPoint X structureMap)) =
      cycleComponentMap structureMap x z := by
  rfl

end AlgebraicGeometry.ComplexPoint
