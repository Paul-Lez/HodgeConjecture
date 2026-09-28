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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
public import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Geometric support of a closed subvariety

A closed embedding `i : Y ⟶ X` over `Spec ℂ` has a support: the complex points of `X` in the
image of `i`. When the source is irreducible the image is the closure of one ambient point, the
ambient generic point of `i`.

An algebraic cycle in Mathlib is indexed by the generic points of its irreducible components.
This file also constructs the reduced integral closed subscheme attached to such a point, and
the closed embedding it carries.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

namespace CycleComponent

/-- The integral component at a scheme point, bundled over the base. -/
abbrev over (X : Over (Spec ↧ℂ)) (x : X.left) : Over (Spec ↧ℂ) :=
  ComplexPoint.overMk X (X.left.pointClosureι x)

/-- The closed immersion used to evaluate a point-indexed cycle. -/
abbrev ι (X : Over (Spec ↧ℂ)) (x : X.left) : over X x ⟶ X :=
  ComplexPoint.overHomMk X (X.left.pointClosureι x)

end CycleComponent

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The complex points of `X` in the image of a closed embedding. -/
def closedEmbeddingSupport [IsClosedImmersion i.left] : Closeds (ComplexPoint X) :=
  ⟨Set.range (Point.map i), ComplexPoint.isClosed_range_map_of_closedImmersion i⟩

/-- The analytic support can be tested on underlying scheme points. -/
lemma closedEmbeddingSupport_eq_preimage [IsClosedImmersion i.left] :
    (closedEmbeddingSupport i : Set (ComplexPoint X)) =
      Point.underlying ⁻¹' Set.range i.left :=
  ComplexPoint.range_map_of_closedImmersion i

@[simp]
lemma mem_closedEmbeddingSupport [IsClosedImmersion i.left] (z : ComplexPoint X) :
    z ∈ closedEmbeddingSupport i ↔ z.underlying ∈ Set.range i.left := by
  rw [← SetLike.mem_coe, closedEmbeddingSupport_eq_preimage]
  rfl

/-- The ambient point of a closed embedding whose source is irreducible. -/
def closedEmbeddingGenericPoint [IrreducibleSpace Y.left] : X.left :=
  i.left (genericPoint Y.left)

/-- A closed embedding of a projective variety is projective over `ℂ`. -/
theorem closedEmbedding_isProjective [IsProjective X.hom] [IsClosedImmersion i.left] :
    IsProjective Y.hom := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  refine ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := i.left ≫ P.immersion
      isClosedImmersion := by
        let := P.isClosedImmersion
        infer_instance
      immersion_toBase := ?_ }
  ⟩⟩
  rw [Category.assoc, P.immersion_toBase]
  exact Over.w i

end AlgebraicGeometry
