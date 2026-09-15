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
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothLocus
import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
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
variable (X : Over (Spec ↧ℂ))

/-- The underlying scheme point of a complex point of a cycle component is closed. -/
lemma cycleComponent_complexPoint_underlying_isClosed
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : ComplexPoint (cycleComponentOver X x)) :
    IsClosed {z.underlying} := by
  let φ : Spec ↧ℂ ⟶ X.left.pointClosure x := z.left
  exact ((pointEquivClosedPoint
    (X.left.pointClosureι x ≫ X.hom)) ⟨φ, Over.w z⟩).2

/-- The image in the ambient variety of a complex point of a cycle component is a closed scheme
point. -/
lemma cycleComponent_complexPoint_ambient_underlying_isClosed
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : ComplexPoint (cycleComponentOver X x)) :
    IsClosed {X.left.pointClosureι x z.underlying} := by
  have hclosed := (X.left.pointClosureι x).isClosedEmbedding.isClosedMap
    {z.underlying} (cycleComponent_complexPoint_underlying_isClosed X x z)
  simpa only [Set.image_singleton] using hclosed

/-- A reduced cycle component has a smooth complex point whose underlying scheme point is
closed. -/
lemma exists_cycleComponent_smooth_closed_complexPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ∃ z : ComplexPoint (cycleComponentOver X x),
      z.underlying ∈
          cycleComponentSmoothLocus X x ∧
        IsClosed {z.underlying} := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint X x
  exact ⟨z, hz, cycleComponent_complexPoint_underlying_isClosed X x z⟩

/-- The coheight of the generic point of a component cannot exceed the relative dimension of
the smooth ambient complex scheme. -/
lemma cycleComponent_codimension_le
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) {d p : ℕ}
    [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) :
    p ≤ d := by
  have hle := SmoothOfRelativeDimension.coheight_le_complex
    (f := X.hom) (d := d) x
  rw [hx] at hle
  exact_mod_cast hle

end AlgebraicGeometry
end
