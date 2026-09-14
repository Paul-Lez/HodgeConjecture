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
variable (X : Over (Spec ↧ℂ))

lemma range_cycleComponentMap_subset
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set.range (cycleComponentMap X x) ⊆ cycleComponentSupport X x := by
  rintro z ⟨w, rfl⟩
  change (cycleComponentι X.left x) w.underlying ∈ closure {x}
  rw [← range_cycleComponentι X.left x]
  exact ⟨w.underlying, rfl⟩

/-- A closed immersion of a cycle component is injective on complex points. -/
lemma cycleComponentMap_injective
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Function.Injective (cycleComponentMap X x) := fun _ _ hab =>
  Over.OverMorphism.ext ((cancel_mono (cycleComponentι X.left x)).mp
    (congrArg (fun z => z.left) hab))

/-- Map the complex points of a cycle component into its analytic support. -/
def cycleComponentSupportMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Point ℂ (Over.mk (cycleComponentι X.left x ≫ X.hom)) →
      cycleComponentSupport X x :=
  fun z => ⟨cycleComponentMap X x z,
    range_cycleComponentMap_subset X x ⟨z, rfl⟩⟩

/-- Complex points of the reduced component are equivalent to the points in its analytic
support. -/
def cycleComponentPointEquivSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Point ℂ (Over.mk (cycleComponentι X.left x ≫ X.hom)) ≃
      cycleComponentSupport X x :=
  Equiv.ofBijective (cycleComponentSupportMap X x) ⟨
    fun _ _ h => cycleComponentMap_injective X x (congrArg Subtype.val h),
    fun z => ⟨cycleComponentComplexPointLift X x z z.2,
      Subtype.ext (cycleComponentMap_lift X x z z.2)⟩⟩

end AlgebraicGeometry
end

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable (X : Over (Spec ↧ℂ))

/-- An algebraic cycle on a projective complex variety has finite support. Algebraic cycles are
locally finite by definition, and the underlying Zariski space is compact. -/
lemma algebraicCycle_support_finite {R : Type*} [Zero R]
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (c : AlgebraicCycle X.left R) :
    c.support.Finite := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) isCompact_univ

/-- Every integral cycle component has a complex point in its smooth locus. The smooth locus is
dense over the perfect field `ℂ`, and a projective complex variety has a closed point there. -/
theorem exists_cycleComponent_smooth_complexPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ∃ z : Point ℂ (Over.mk (cycleComponentι X.left x ≫ X.hom)),
      z.underlying ∈
        (cycleComponentι X.left x ≫ X.hom).smoothLocus := by
  let f := cycleComponentι X.left x ≫ X.hom
  let : JacobsonSpace (cycleComponent X.left x) :=
    LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty
    f.smoothLocus.2.isLocallyClosed
  let p := (pointEquivClosedPoint f).symm ⟨y, hyClosed⟩
  refine ⟨Over.homMk p.1 p.2, ?_⟩
  have hp := (pointEquivClosedPoint f).apply_symm_apply ⟨y, hyClosed⟩
  have hp' : p.1 (IsLocalRing.closedPoint ℂ) = y := congrArg Subtype.val hp
  change p.1 (IsLocalRing.closedPoint ℂ) ∈ f.smoothLocus
  rw [hp']
  exact hy

/-- The complex points of a reduced cycle component map onto exactly its closed analytic
support. -/
lemma range_cycleComponentMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set.range (cycleComponentMap X x) = cycleComponentSupport X x := by
  apply Set.Subset.antisymm (range_cycleComponentMap_subset X x)
  intro z hz
  exact ⟨cycleComponentComplexPointLift X x z hz,
    cycleComponentMap_lift X x z hz⟩

end AlgebraicGeometry
end
