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

open SmoothProjectiveComplexVariety

noncomputable local instance cycleComponentTopology
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    TopologicalSpace
      (ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap)) :=
  analyticTopology

/-- The complex-point map of a reduced cycle component is a closed topological embedding. -/
lemma cycleComponentMap_isClosedEmbedding
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IsClosedEmbedding (cycleComponentMap V x) := by
  exact isClosedEmbedding_map_of_closedImmersion
    (i := cycleComponentι V.scheme x) (structureMapA :=
      cycleComponentι V.scheme x ≫ V.structureMap) (structureMapB := V.structureMap) rfl

/-- The analytification of a reduced cycle component is canonically homeomorphic to its
analytic support in the ambient variety. -/
def cycleComponentPointHomeomorphSupport
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap) ≃ₜ
      cycleComponentSupport V x :=
  (cycleComponentMap_isClosedEmbedding V x).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_cycleComponentMap V x))

@[simp]
lemma cycleComponentPointHomeomorphSupport_apply
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap)) :
    cycleComponentPointHomeomorphSupport V x z = cycleComponentSupportMap V x z := by
  rfl

/-- The underlying equivalence of the component-support homeomorphism is the previously
constructed point equivalence. -/
lemma cycleComponentPointHomeomorphSupport_toEquiv
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    (cycleComponentPointHomeomorphSupport V x).toEquiv =
      cycleComponentPointEquivSupport V x := by
  apply Equiv.ext
  intro z
  rfl

/-- The smooth analytic locus of a component is homeomorphic to its image in the ambient
analytic variety. -/
def cycleComponentSmoothPointHomeomorphSupport
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    cycleComponentSmoothAnalyticLocus V x ≃ₜ
      cycleComponentSmoothSupport V x :=
  (cycleComponentMap_isClosedEmbedding V x).toIsEmbedding.homeomorphImage
    (cycleComponentSmoothAnalyticLocus V x)

@[simp]
lemma cycleComponentSmoothPointHomeomorphSupport_apply
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : cycleComponentSmoothAnalyticLocus V x) :
    (cycleComponentSmoothPointHomeomorphSupport V x z : V.analyticPoint) =
      cycleComponentMap V x z := by
  rfl

end AlgebraicGeometry.ComplexPoint
