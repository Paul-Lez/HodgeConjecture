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
# Geometric support of algebraic cycles

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Support`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section
open CategoryTheory Topology TopologicalSpace
namespace AlgebraicGeometry
variable (X : Over (Spec ↧ℂ))

@[simp]
lemma range_cycleComponentι (X : Scheme) (x : X) :
    Set.range (cycleComponentι X x) = closure {x} := by
  change Set.range
    ((Scheme.IdealSheafData.vanishingIdeal
      (X := X) ⟨closure {x}, isClosed_closure⟩).subschemeι) = closure {x}
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

end AlgebraicGeometry
end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A complex point in the support of a component annihilates the defining ideal of that
component. -/
lemma cycleComponent_vanishingIdeal_le_complexPoint_ker
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z.underlying ∈ closure {x}) :
    (cycleComponentι X.left x).ker ≤ z.left.ker := by
  unfold cycleComponentι
  rw [Scheme.IdealSheafData.ker_subschemeι]
  rw [complexPoint_ker_eq_vanishingIdeal_closure z]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  exact closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure

/-- The map on complex points induced by the canonical inclusion of a cycle component. -/
def cycleComponentMap
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) → (ComplexPoint X) :=
  Point.map (Over.homMk (cycleComponentι X.left x) rfl)

/-- Lift a complex point in a component support through the reduced closed component. -/
def cycleComponentComplexPointLift
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z ∈ cycleComponentSupport X x) :
    ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)) :=
  have hz' : z.underlying ∈ closure {x} := hz
  Over.homMk (IsClosedImmersion.lift (cycleComponentι X.left x) z.left
      (cycleComponent_vanishingIdeal_le_complexPoint_ker X x z hz')) (by
    change _ ≫ (cycleComponentι X.left x ≫ X.hom) = 𝟙 _
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
    exact Over.w z)

@[simp]
lemma cycleComponentMap_lift
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
    (z : (ComplexPoint X)) (hz : z ∈ cycleComponentSupport X x) :
    cycleComponentMap X x (cycleComponentComplexPointLift X x z hz) = z :=
  Over.OverMorphism.ext (IsClosedImmersion.lift_fac (cycleComponentι X.left x) z.left _)

/-- The analytic complex points in the smooth locus of a reduced cycle component. -/
def cycleComponentSmoothAnalyticLocus
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Set (ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom))) :=
  Point.overOpen
    (cycleComponentι X.left x ≫ X.hom).smoothLocus

/-- The image in the ambient analytic space of the smooth locus of a cycle component. -/
def cycleComponentSmoothSupport
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) : Set (ComplexPoint X) :=
  cycleComponentMap X x '' cycleComponentSmoothAnalyticLocus X x

end AlgebraicGeometry

end

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec ↧ℂ))

/-- The reduced closure of a point in a projective complex variety is Noetherian.

This is not an instance: the component does not determine the structure morphism carrying the
projectivity hypothesis. -/
theorem cycleComponent_isNoetherian
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsNoetherian (cycleComponent X.left x) :=
  @isNoetherian_of_isProjective (Over.mk (cycleComponentι X.left x ≫ X.hom))
    (cycleComponent_projective X x)

/-- The smooth locus of an integral cycle component is a smooth complex scheme. -/
theorem cycleComponent_smoothLocus_smooth
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    Smooth
      ((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
        (cycleComponentι X.left x ≫ X.hom)) :=
  (cycleComponentι X.left x ≫ X.hom).smooth_restrict_smoothLocus

/-- The complex points over a Zariski-closed subset form an analytically closed set. -/
lemma isClosed_complexPoint_underlying_preimage
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (Z : TopologicalSpace.Closeds X.left) :
    IsClosed ((@Point.underlying ℂ _ _ X) ⁻¹'
      (Z : Set X.left)) := by
  rw [← isOpen_compl_iff]
  let U : X.left.Opens := ⟨(Z : Set X.left)ᶜ,
    isOpen_compl_iff.mpr Z.2⟩
  exact Point.isOpen_overOpen (X := X) U

lemma isClosed_cycleComponentSupport
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left) :
    IsClosed (cycleComponentSupport X x) :=
  isClosed_complexPoint_underlying_preimage X
    ⟨closure {x}, isClosed_closure⟩

end AlgebraicGeometry
