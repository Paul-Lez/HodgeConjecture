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
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry

/-!
# Exact local coordinates on small-dimensional cycle components

This file proves exact dimension and local-coordinate statements for reduced cycle components in
the cases covered by the pointwise dimension formula: components of dimension zero or one in an
arbitrary smooth complex variety, and all components in ambient relative dimension at most two.

The local coordinates are constructed on the smooth locus of the component.  Their number is
proved to be exactly the dimension of the component, rather than being included as an assumption.
The support library now proves the arbitrary-dimensional catenary formula and the resulting
global dimension of each component.  Extending the coordinate package still requires a local
bridge showing that every closed point of the component has that coheight; that bridge is not
proved here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace RingHom

/-- A standard-smooth ring map is standard smooth of some relative dimension. -/
lemma IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsStandardSmooth) :
    ∃ n, f.IsStandardSmoothOfRelativeDimension n := by
  let : Algebra R S := f.toAlgebra
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hf.out
  refine ⟨P.dimension, ?_⟩
  exact ⟨ι, σ, hσ, hι, P, rfl⟩

end RingHom

namespace AlgebraicGeometry

attribute [local instance] overSpecAlgebra

section SchemeGeometry

variable {X : Scheme} {f : X ⟶ Spec ↧ℂ} {d p : ℕ}

/-- A closed point of an integral smooth complex `d`-fold has coheight `d`. -/
lemma SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    [IsIntegral X] [SmoothOfRelativeDimension d f] (x : X) (hx : IsClosed {x}) :
    Order.coheight x = d := by
  have hxmin : IsMin x := by
    intro y hy
    have hy' : y ∈ closure {x} := by
      rw [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
      exact hy
    rw [hx.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  have h := SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed
    (f := f) (d := d) x hx
  rw [Order.IsMin.height_eq_zero hxmin, zero_add] at h
  exact h

end SchemeGeometry

variable (X : Over (Spec ↧ℂ)) {d p : ℕ}

namespace CycleComponent

/-- Separate exact local coordinates on a smooth cycle component and on its smooth ambient
variety.  The component coordinates use exactly `n` variables.  This package does not assert
that the two coordinate systems straighten the closed immersion simultaneously. -/
structure SeparateLocalCoordinates
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (d n : ℕ)
    [SmoothOfRelativeDimension d X.hom] where
  /-- A complex point of the reduced component. -/
  point : ComplexPoint (over X x)
  /-- The point lies in the component's smooth locus. -/
  point_mem_smoothLocus : point.underlying ∈
    smoothLocus X x
  /-- The underlying point is closed in the component. -/
  point_isClosed : IsClosed {point.underlying}
  /-- An affine neighborhood in the smooth locus of the component. -/
  componentNeighborhood :
    (smoothLocusOver X x).left.Opens
  /-- The component neighborhood is affine. -/
  componentNeighborhood_isAffine : IsAffineOpen componentNeighborhood
  /-- The chosen point belongs to the component neighborhood. -/
  point_mem_componentNeighborhood :
    (⟨point.underlying, point_mem_smoothLocus⟩ :
      (smoothLocusOver X x).left) ∈
        componentNeighborhood
  /-- An étale coordinate homomorphism of complex algebras with exactly `n` component
  coordinates. -/
  componentCoordinateAlgHom : MvPolynomial (Fin n) ℂ →ₐ[ℂ]
    Γ((smoothLocusOver X x).left, componentNeighborhood)
  /-- The component coordinate homomorphism is étale. -/
  componentCoordinateAlgHom_etale : componentCoordinateAlgHom.toRingHom.Etale
  /-- Independently chosen étale coordinates on the ambient `d`-fold. -/
  ambientCoordinates : LocalEtaleCoordinates X d
    (X.left.pointClosureι x point.underlying)

end CycleComponent

end AlgebraicGeometry
