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

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Other.AlgebraicGeometry.ProjectiveAnalytification

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

open Point

variable (X : Over (Spec ↧ℂ))

noncomputable local instance cycleComponentTopology
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    TopologicalSpace
      (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :=
  analyticTopology

/-- The complex-point map of a reduced cycle component is a closed topological embedding. -/
lemma cycleComponentMap_isClosedEmbedding
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsClosedEmbedding (cycleComponentMap X x) := by
  let i : Over.mk (cycleComponentι X.left x ≫ X.hom) ⟶ X :=
    Over.homMk (cycleComponentι X.left x) rfl
  let : IsClosedImmersion i.left :=
    inferInstanceAs (IsClosedImmersion (cycleComponentι X.left x))
  exact isClosedEmbedding_map_of_closedImmersion i

/-- The analytification of a reduced cycle component is canonically homeomorphic to its
analytic support in the ambient variety. -/
def cycleComponentPointHomeomorphSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) ≃ₜ
      cycleComponentSupport X x :=
  (cycleComponentMap_isClosedEmbedding X x).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_cycleComponentMap X x))

@[simp]
lemma cycleComponentPointHomeomorphSupport_apply
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :
    cycleComponentPointHomeomorphSupport X x z =
      cycleComponentSupportMap X x z := by
  rfl

/-- The underlying equivalence of the component-support homeomorphism is the previously
constructed point equivalence. -/
lemma cycleComponentPointHomeomorphSupport_toEquiv
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    (cycleComponentPointHomeomorphSupport X x).toEquiv =
      cycleComponentPointEquivSupport X x :=
  Equiv.ext fun _ ↦ rfl

/-- The smooth analytic locus of a component is homeomorphic to its image in the ambient
analytic variety. -/
def cycleComponentSmoothPointHomeomorphSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    cycleComponentSmoothAnalyticLocus X x ≃ₜ
      cycleComponentSmoothSupport X x :=
  (cycleComponentMap_isClosedEmbedding X x).toIsEmbedding.homeomorphImage
    (cycleComponentSmoothAnalyticLocus X x)

@[simp]
lemma cycleComponentSmoothPointHomeomorphSupport_apply
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : cycleComponentSmoothAnalyticLocus X x) :
    (cycleComponentSmoothPointHomeomorphSupport X x z : (ComplexPoint X)) =
      cycleComponentMap X x z := by
  rfl

end AlgebraicGeometry.ComplexPoint
