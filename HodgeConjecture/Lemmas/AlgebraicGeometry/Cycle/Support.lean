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

@[simp]
lemma range_cycleComponentι (X : Scheme) (x : X) :
    Set.range (cycleComponentι X x) = closure {x} := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι) = closure {x}
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The image of a closed immersion whose source is irreducible is the closure of the image of
the generic point. -/
theorem range_eq_closure_image_genericPoint {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f]
    [IrreducibleSpace Y] :
    Set.range f = closure {f (genericPoint Y)} := by
  rw [← Set.image_singleton, f.isClosedEmbedding.closure_image_eq, genericPoint_closure,
    Set.image_univ]

/-- The generic point of the reduced closure of `x` lies over `x`. -/
@[simp]
theorem cycleComponentι_genericPoint (X : Scheme) (x : X) :
    cycleComponentι X x (genericPoint (cycleComponent X x)) = x := by
  refine IsGenericPoint.eq (S := closure {x}) ?_ isGenericPoint_closure
  show closure {cycleComponentι X x (genericPoint (cycleComponent X x))} = closure {x}
  rw [← range_eq_closure_image_genericPoint, range_cycleComponentι]

end AlgebraicGeometry
end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- The kernel of a complex point is the vanishing ideal of the closure of its underlying scheme
point. -/
private lemma complexPoint_ker_eq_vanishingIdeal_closure
    {X : Over (Spec ↧ℂ)}
    (z : ComplexPoint X) :
    z.left.ker = Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {z.underlying}, isClosed_closure⟩ := by
  let f : Spec ↧ℂ ⟶ X.left := z.left
  have hrange : Set.range f = {z.underlying} := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have hs : s = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      subst s
      rfl
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨IsLocalRing.closedPoint ℂ, rfl⟩
  have h := Scheme.IdealSheafData.map_vanishingIdeal f
    (⊤ : TopologicalSpace.Closeds (Spec ↧ℂ))
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.map_bot] at h
  have himage : f '' (↑(⊤ : TopologicalSpace.Closeds (Spec ↧ℂ)) :
      Set (Spec ↧ℂ)) = {z.underlying} := by
    simpa only [TopologicalSpace.Closeds.coe_top, Set.image_univ] using hrange
  rwa [himage] at h

/-- A complex point in the support of a closed embedding annihilates the kernel of that
embedding. -/
lemma closedEmbedding_ker_le_complexPoint_ker [IsClosedImmersion i.left]
    (z : ComplexPoint X) (hz : z ∈ closedEmbeddingSupport i) :
    i.left.ker ≤ z.left.ker := by
  rw [complexPoint_ker_eq_vanishingIdeal_closure z,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  have h : ((Scheme.Hom.ker i.left).support : Set X.left) = closure (Set.range i.left) :=
    Scheme.Hom.support_ker i.left
  have hz' : z.underlying ∈ Set.range i.left := hz
  exact fun y hy ↦ h.ge (closure_mono (Set.singleton_subset_iff.mpr hz') hy)

/-- Lift a complex point in the support of a closed embedding through that embedding. -/
def closedEmbeddingComplexPointLift [IsClosedImmersion i.left]
    (z : ComplexPoint X) (hz : z ∈ closedEmbeddingSupport i) :
    ComplexPoint Y :=
  Over.homMk (IsClosedImmersion.lift i.left z.left
      (closedEmbedding_ker_le_complexPoint_ker i z hz)) (by
    change _ ≫ Y.hom = 𝟙 _
    rw [← Over.w i, ← Category.assoc, IsClosedImmersion.lift_fac]
    exact Over.w z)

@[simp]
lemma map_closedEmbeddingComplexPointLift [IsClosedImmersion i.left]
    (z : ComplexPoint X) (hz : z ∈ closedEmbeddingSupport i) :
    Point.map i (closedEmbeddingComplexPointLift i z hz) = z :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac i.left z.left _)

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

lemma isClosed_closedEmbeddingSupport [IsClosedImmersion i.left] :
    IsClosed (closedEmbeddingSupport i) :=
  isClosed_complexPoint_underlying_preimage X
    ⟨Set.range i.left, i.left.isClosedEmbedding.isClosed_range⟩

/-- The image of a closed embedding whose source is irreducible is the closure of its ambient
generic point. -/
theorem range_eq_closure_closedEmbeddingGenericPoint [IrreducibleSpace Y.left]
    [IsClosedImmersion i.left] :
    Set.range i.left = closure {closedEmbeddingGenericPoint i} :=
  range_eq_closure_image_genericPoint i.left

/-- The ambient generic point of the closed embedding of the reduced closure of `x` is `x`. -/
@[simp]
theorem closedEmbeddingGenericPoint_cycleComponentOverι (X : Over (Spec ↧ℂ)) (x : X.left) :
    closedEmbeddingGenericPoint (cycleComponentOverι X x) = x :=
  cycleComponentι_genericPoint X.left x

/-- A codimension hypothesis on `x` is one on the ambient generic point of the closed embedding
of its reduced closure. -/
theorem coheight_closedEmbeddingGenericPoint_cycleComponentOverι
    (X : Over (Spec ↧ℂ)) (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    Order.coheight (closedEmbeddingGenericPoint (cycleComponentOverι X x)) = p := by
  rwa [closedEmbeddingGenericPoint_cycleComponentOverι]

/-- The support of the closed embedding of the reduced closure of `x`. -/
@[simp]
theorem closedEmbeddingSupport_cycleComponentOverι (X : Over (Spec ↧ℂ)) (x : X.left) :
    closedEmbeddingSupport (cycleComponentOverι X x) = Point.underlying ⁻¹' closure {x} :=
  congrArg (Point.underlying ⁻¹' ·) (range_cycleComponentι X.left x)

end AlgebraicGeometry
