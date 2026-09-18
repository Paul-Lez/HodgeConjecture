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
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.NormalGeometry

/-!
# Exact local coordinates on small-dimensional closed subvarieties

This file proves exact dimension and local-coordinate statements for closed subvarieties in the
cases covered by the pointwise dimension formula: subvarieties of dimension zero or one in an
arbitrary smooth complex variety, and all subvarieties in ambient relative dimension at most two.

The local coordinates are constructed on the smooth locus of the subvariety.  Their number is
proved to be exactly its dimension, rather than being included as an assumption.
The support library now proves the arbitrary-dimensional catenary formula and the resulting
global dimension of each subvariety.  Extending the coordinate package still requires a local
bridge showing that every closed point of the subvariety has that coheight; that bridge is not
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

variable {X : Over (Spec ↧ℂ)} {d p : ℕ}

namespace ClosedEmbeddingSeparateLocalCoordinates

/-- The smooth locus of the source of a closed embedding underlying an exact coordinate
package. -/
abbrev sourceSmoothLocus {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [Smooth X.hom]
    [IsProjective X.hom] [IsClosedImmersion i.left] :=
  (i.left ≫ X.hom).smoothLocus

/-- That smooth locus, bundled over the complex base. -/
abbrev sourceSmoothScheme {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X) [Smooth X.hom]
    [IsProjective X.hom] [IsClosedImmersion i.left] : Over (Spec ↧ℂ) :=
  Over.mk ((sourceSmoothLocus i).ι ≫ Y.hom)

end ClosedEmbeddingSeparateLocalCoordinates

/-- Separate exact local coordinates on the smooth locus of a closed subvariety and on its
smooth ambient variety. The source coordinates use exactly `n` variables. This package does not
assert that the two coordinate systems straighten the closed embedding simultaneously. -/
structure ClosedEmbeddingSeparateLocalCoordinates {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsClosedImmersion i.left] (d n : ℕ)
    [SmoothOfRelativeDimension d X.hom] where
  /-- A complex point of the source. -/
  point : ComplexPoint Y
  /-- The point lies in the smooth locus of the source. -/
  point_mem_smoothLocus : point.underlying ∈
    (i.left ≫ X.hom).smoothLocus
  /-- The underlying point is closed in the source. -/
  point_isClosed : IsClosed {point.underlying}
  /-- An affine neighborhood in the smooth locus of the source. -/
  sourceNeighborhood :
    (ClosedEmbeddingSeparateLocalCoordinates.sourceSmoothScheme i).left.Opens
  /-- The source neighborhood is affine. -/
  sourceNeighborhood_isAffine : IsAffineOpen sourceNeighborhood
  /-- The chosen point belongs to the source neighborhood. -/
  point_mem_sourceNeighborhood :
    (⟨point.underlying, point_mem_smoothLocus⟩ :
      (ClosedEmbeddingSeparateLocalCoordinates.sourceSmoothScheme i).left) ∈
        sourceNeighborhood
  /-- An étale coordinate homomorphism of complex algebras with exactly `n` source
  coordinates. -/
  sourceCoordinateAlgHom : MvPolynomial (Fin n) ℂ →ₐ[ℂ]
    Γ((ClosedEmbeddingSeparateLocalCoordinates.sourceSmoothScheme i).left, sourceNeighborhood)
  /-- The source coordinate homomorphism is étale. -/
  sourceCoordinateAlgHom_etale : sourceCoordinateAlgHom.toRingHom.Etale
  /-- Independently chosen étale coordinates on the ambient `d`-fold. -/
  ambientCoordinates : LocalEtaleCoordinates X d (i.left point.underlying)

