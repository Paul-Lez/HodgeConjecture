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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Geometric support of a closed subvariety

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry

/-- The image of a closed immersion whose source is irreducible is the closure of the image of
the generic point. -/
theorem range_eq_closure_image_genericPoint {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f]
    [IrreducibleSpace Y] :
    Set.range f = closure {f (genericPoint Y)} := by
  rw [← Set.image_singleton, f.isClosedEmbedding.closure_image_eq, genericPoint_closure,
    Set.image_univ]

end AlgebraicGeometry
end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The complex points of the source of a closed embedding that lie in its smooth locus. -/
def closedEmbeddingSmoothAnalyticLocus [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsClosedImmersion i.left] : Set (ComplexPoint Y) :=
  Point.overOpen (i.left ≫ X.hom).smoothLocus

/-- The image in `X(ℂ)` of the smooth locus of the source of a closed embedding. -/
def closedEmbeddingSmoothSupport [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsClosedImmersion i.left] : Set (ComplexPoint X) :=
  Point.map i '' closedEmbeddingSmoothAnalyticLocus i

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The source of a closed embedding of a projective complex variety is Noetherian.

This is not an instance: the source does not determine the embedding carrying the projectivity
hypothesis. -/
theorem closedEmbedding_isNoetherian [IsProjective X.hom] [IsClosedImmersion i.left] :
    IsNoetherian Y.left :=
  @isNoetherian_of_isProjective Y (closedEmbedding_isProjective i)

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage (X : Over (Spec ↧ℂ))
    (Z : TopologicalSpace.Closeds X.left) :
    IsClosed ((@Point.underlying ℂ _ _ X) ⁻¹'
      (Z : Set X.left)) := by
  rw [← isOpen_compl_iff]
  let U : X.left.Opens := ⟨(Z : Set X.left)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  exact Point.isOpen_overOpen (X := X) U

/-- The image of a closed embedding whose source is irreducible is the closure of its ambient
generic point. -/
theorem range_eq_closure_closedEmbeddingGenericPoint [IrreducibleSpace Y.left]
    [IsClosedImmersion i.left] :
    Set.range i.left = closure {closedEmbeddingGenericPoint i} :=
  range_eq_closure_image_genericPoint i.left

/-- The ambient generic point of the closed embedding of the reduced closure of `x` is `x`. -/
@[simp]
theorem CycleComponent.genericPoint_image (X : Over (Spec ↧ℂ)) (x : X.left) :
    closedEmbeddingGenericPoint (CycleComponent.ι X x) = x :=
  X.left.pointClosureι_genericPoint x

/-- A codimension hypothesis on `x` is one on the ambient generic point of the closed embedding
of its reduced closure. -/
theorem CycleComponent.coheight_genericPoint_image
    (X : Over (Spec ↧ℂ)) (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    Order.coheight (closedEmbeddingGenericPoint (CycleComponent.ι X x)) = p := by
  rwa [CycleComponent.genericPoint_image]

/-- The support of the closed embedding of the reduced closure of `x`. -/
@[simp]
theorem CycleComponent.coe_support (X : Over (Spec ↧ℂ)) (x : X.left) :
    (closedEmbeddingSupport (CycleComponent.ι X x) : Set (ComplexPoint X)) = Point.underlying ⁻¹' closure {x} :=
  (closedEmbeddingSupport_eq_preimage _).trans
    (congrArg (Point.underlying ⁻¹' ·) (X.left.range_pointClosureι x))

end AlgebraicGeometry
