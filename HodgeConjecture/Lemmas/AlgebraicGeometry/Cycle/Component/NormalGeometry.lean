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
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Smooth geometry of cycle components

The reduced closure of a point in a smooth projective complex variety is an integral projective
scheme.  This file records that its smooth locus is dense, that its smooth closed points are
dense, and that a smooth closed complex point can be chosen together with ambient étale
coordinates.

For an ambient scheme smooth of relative dimension `d`, a component whose generic point has
coheight `p` has dimension at most `d - p`. The later module `Smooth.CatenaryDimension` upgrades
this bound to equality. A simultaneous coordinate normal form of exact codimension `p` is still
not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry.CycleComponent

variable (X : Over (Spec ↧ℂ)) (x : X.left)

section FiniteType

variable [LocallyOfFiniteType X.hom]

/-- The smooth locus of a cycle component is Zariski dense. -/
lemma dense_smoothLocus :
    Dense (smoothLocus X x : Set (X.left.pointClosure x)) :=
  (X.left.pointClosureι x ≫ X.hom).dense_smoothLocus_of_perfectField

/-- The smooth locus of a cycle component is irreducible. -/
instance : IrreducibleSpace (smoothLocus X x) := by
  obtain ⟨y, hy⟩ := (dense_smoothLocus X x).nonempty
  let : Nonempty (smoothLocus X x) := ⟨⟨y, hy⟩⟩
  exact (smoothLocus X x).ι.isOpenEmbedding.irreducibleSpace

/-- The closed points of the smooth locus are dense in a cycle component. -/
lemma dense_smoothLocus_closedPoints :
    Dense ((smoothLocus X x : Set (X.left.pointClosure x)) ∩
      closedPoints (X.left.pointClosure x)) := by
  let f := X.left.pointClosureι x ≫ X.hom
  exact dense_iff_closure_eq.mpr ((JacobsonSpace.closure_inter_closedPoints_eq_closure
    f.smoothLocus.2.isLocallyClosed).trans
      (dense_iff_closure_eq.mp (dense_smoothLocus X x)))

end FiniteType

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has
topological Krull dimension at most `d - p`. -/
lemma topologicalKrullDim_le_sub
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] {d p : ℕ}
    [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) :
    topologicalKrullDim (X.left.pointClosure x) ≤ d - p := by
  rw [Scheme.topologicalKrullDim_pointClosure]
  exact WithBot.coe_le_coe.mpr
    (SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := X.hom) (d := d) x hx)

end AlgebraicGeometry.CycleComponent
