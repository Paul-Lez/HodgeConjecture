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
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support

/-!
# Support, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

lemma range_closedEmbeddingMap_subset
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    Set.range (Point.map i) ⊆ closedEmbeddingSupport i := by
  rintro z ⟨w, rfl⟩
  exact ⟨w.underlying, rfl⟩

/-- A closed embedding is injective on complex points. -/
lemma closedEmbeddingMap_injective
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    Function.Injective (Point.map i) := fun _ _ hab =>
  Over.OverMorphism.ext ((cancel_mono (i.left)).mp
    (congrArg (fun z => z.left) hab))

/-- Map the complex points of the source of a closed embedding into its support. -/
def closedEmbeddingSupportMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ComplexPoint (Y) →
      closedEmbeddingSupport i :=
  fun z => ⟨Point.map i z,
    range_closedEmbeddingMap_subset i ⟨z, rfl⟩⟩

/-- Complex points of the source of a closed embedding are equivalent to its support. -/
def closedEmbeddingPointEquivSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ComplexPoint (Y) ≃
      closedEmbeddingSupport i :=
  Equiv.ofBijective (closedEmbeddingSupportMap i) ⟨
    fun _ _ h => closedEmbeddingMap_injective i (congrArg Subtype.val h),
    fun z => ⟨closedEmbeddingComplexPointLift i z z.2,
      Subtype.ext (map_closedEmbeddingComplexPointLift i z z.2)⟩⟩

end AlgebraicGeometry
end

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    c.support.Finite := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ

/-- The integral source of a closed embedding has a complex point in its smooth locus. The
smooth locus is dense over the perfect field `ℂ`, and a projective complex variety has a closed
point there. -/
theorem exists_closedEmbedding_smooth_complexPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    ∃ z : ComplexPoint (Y),
      z.underlying ∈
        (i.left ≫ X.hom).smoothLocus := by
  let f := i.left ≫ X.hom
  let : JacobsonSpace (Y.left) :=
    LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty
    f.smoothLocus.2.isLocallyClosed
  let p := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨Over.homMk p.1 (by rw [show Y.hom = f from (Over.w i).symm]; exact p.2), ?_⟩
  have hp := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hp' : p.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hp
  change p.1 (IsLocalRing.closedPoint ℂ) ∈ f.smoothLocus
  rw [hp']
  exact hy

/-- The complex points of the source of a closed embedding map onto its support. -/
lemma range_closedEmbeddingMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsClosedImmersion i.left] :
    Set.range (Point.map i) = closedEmbeddingSupport i := by
  apply Set.Subset.antisymm (range_closedEmbeddingMap_subset i)
  intro z hz
  exact ⟨closedEmbeddingComplexPointLift i z hz,
    map_closedEmbeddingComplexPointLift i z hz⟩

end AlgebraicGeometry
end
