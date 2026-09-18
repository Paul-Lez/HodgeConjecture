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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
public import Other.AlgebraicGeometry.Cycle.Support

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

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The complex-point map of a closed embedding is a closed topological embedding. -/
lemma closedEmbeddingMap_isClosedEmbedding
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    IsClosedEmbedding (Point.map i) :=
  isClosedEmbedding_map_of_closedImmersion i

/-- The analytification of the source of a closed embedding is homeomorphic to its support in
the ambient variety. -/
def closedEmbeddingPointHomeomorphSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ComplexPoint (Y) ≃ₜ
      closedEmbeddingSupport i :=
  (closedEmbeddingMap_isClosedEmbedding i).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_closedEmbeddingMap i))

@[simp]
lemma closedEmbeddingPointHomeomorphSupport_apply
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left]
    (z : ComplexPoint (Y)) :
    closedEmbeddingPointHomeomorphSupport i z =
      closedEmbeddingSupportMap i z := by
  rfl

/-- The underlying equivalence of the support homeomorphism is the point equivalence. -/
lemma closedEmbeddingPointHomeomorphSupport_toEquiv
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    (closedEmbeddingPointHomeomorphSupport i).toEquiv =
      closedEmbeddingPointEquivSupport i :=
  Equiv.ext fun _ ↦ rfl

/-- The smooth analytic locus of a component is homeomorphic to its image in the ambient
analytic variety. -/
def closedEmbeddingSmoothPointHomeomorphSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    closedEmbeddingSmoothAnalyticLocus i ≃ₜ
      closedEmbeddingSmoothSupport i :=
  (closedEmbeddingMap_isClosedEmbedding i).toIsEmbedding.homeomorphImage
    (closedEmbeddingSmoothAnalyticLocus i)

@[simp]
lemma closedEmbeddingSmoothPointHomeomorphSupport_apply
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left]
    (z : closedEmbeddingSmoothAnalyticLocus i) :
    (closedEmbeddingSmoothPointHomeomorphSupport i z : (ComplexPoint X)) =
      Point.map i z := by
  rfl

end AlgebraicGeometry.ComplexPoint
