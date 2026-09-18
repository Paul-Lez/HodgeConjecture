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
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry
public import Other.AlgebraicGeometry.Cycle.Support

/-!
# NormalGeometry, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The underlying scheme point of a complex point of the source of a closed embedding is
closed. -/
lemma closedEmbedding_complexPoint_underlying_isClosed
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left]
    (z : ComplexPoint (Y)) :
    IsClosed {z.underlying} := by
  let φ : Spec ↧ℂ ⟶ Y.left := z.left
  exact ((pointEquivClosedPoint
    (i.left ≫ X.hom)) ⟨φ, by rw [show i.left ≫ X.hom = Y.hom from Over.w i]; exact Over.w z⟩).2

/-- The image in the ambient variety of a complex point of the source is a closed scheme
point. -/
lemma closedEmbedding_complexPoint_ambient_underlying_isClosed
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left]
    (z : ComplexPoint (Y)) :
    IsClosed {i.left z.underlying} := by
  have hclosed := (i.left).isClosedEmbedding.isClosedMap
    {z.underlying} (closedEmbedding_complexPoint_underlying_isClosed i z)
  simpa only [Set.image_singleton] using hclosed

/-- The source of a closed embedding has a smooth complex point whose underlying scheme point
is closed. -/
lemma exists_closedEmbedding_smooth_closed_complexPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ∃ z : ComplexPoint (Y),
      z.underlying ∈
          (i.left ≫ X.hom).smoothLocus ∧
        IsClosed {z.underlying} := by
  obtain ⟨z, hz⟩ := exists_closedEmbedding_smooth_complexPoint i
  exact ⟨z, hz, closedEmbedding_complexPoint_underlying_isClosed i z⟩

/-- The coheight of the ambient generic point cannot exceed the relative dimension of the
smooth ambient complex scheme. -/
lemma closedEmbedding_codimension_le
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsClosedImmersion i.left] {d p : ℕ}
    [SmoothOfRelativeDimension d X.hom] (hi : Order.coheight (closedEmbeddingGenericPoint i) = p) :
    p ≤ d := by
  have hle := SmoothOfRelativeDimension.coheight_le_complex
    (f := X.hom) (d := d) (closedEmbeddingGenericPoint i)
  rw [hi] at hle
  exact_mod_cast hle

end AlgebraicGeometry
end
