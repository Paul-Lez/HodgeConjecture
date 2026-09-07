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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothDimensionFormula
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Smooth geometry of cycle components

The reduced closure of a point in a smooth projective complex variety is an integral projective
scheme.  This file records that its smooth locus is dense, that its smooth closed points are
dense, and that a smooth closed complex point can be chosen together with ambient étale
coordinates.

For an ambient scheme smooth of relative dimension `d`, a component whose generic point has
coheight `p` has dimension at most `d - p`. The later module `SmoothCatenaryDimension` upgrades
this bound to equality. A simultaneous coordinate normal form of exact codimension `p` is still
not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- The smooth locus of a reduced cycle component is Zariski dense. -/
lemma dense_cycleComponent_smoothLocus
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    Dense
      ((cycleComponentι X x ≫ structureMap).smoothLocus :
        Set (cycleComponent X x)) :=
  (cycleComponentι X x ≫ structureMap).dense_smoothLocus_of_perfectField

/-- The smooth locus of an integral cycle component is irreducible. -/
noncomputable instance cycleComponent_smoothLocus_irreducibleSpace
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    IrreducibleSpace
      (cycleComponentι X x ≫ structureMap).smoothLocus := by
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus structureMap x).nonempty
  let _ : Nonempty
      (cycleComponentι X x ≫ structureMap).smoothLocus :=
    ⟨⟨y, hy⟩⟩
  exact
    (cycleComponentι X x ≫ structureMap).smoothLocus.ι.isOpenEmbedding.irreducibleSpace

/-- The smooth locus of an integral cycle component is itself an integral scheme. -/
noncomputable instance cycleComponent_smoothLocus_isIntegral
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    IsIntegral (cycleComponentι X x ≫ structureMap).smoothLocus :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The scheme points that are both smooth and closed are dense in a reduced cycle component. -/
lemma dense_cycleComponent_smooth_closedPoints
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    Dense
      (((cycleComponentι X x ≫ structureMap).smoothLocus :
          Set (cycleComponent X x)) ∩
        closedPoints (cycleComponent X x)) := by
  let f := cycleComponentι X x ≫ structureMap
  let _ : JacobsonSpace (cycleComponent X x) :=
    LocallyOfFiniteType.jacobsonSpace f
  change Dense ((f.smoothLocus : Set (cycleComponent X x)) ∩
    closedPoints (cycleComponent X x))
  apply dense_iff_closure_eq.mpr
  exact (JacobsonSpace.closure_inter_closedPoints_eq_closure
    f.smoothLocus.2.isLocallyClosed).trans
      (dense_iff_closure_eq.mp (dense_cycleComponent_smoothLocus structureMap x))

/-- The underlying scheme point of a complex point of a cycle component is closed. -/
lemma cycleComponent_complexPoint_underlying_isClosed
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X)
    (z : ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap)) :
    IsClosed {z.underlying} := by
  change IsClosed {z.1 (IsLocalRing.closedPoint ℂ)}
  exact ((pointEquivClosedPoint
    (cycleComponentι X x ≫ structureMap)) z).2

/-- The image in the ambient variety of a complex point of a cycle component is a closed scheme
point. -/
lemma cycleComponent_complexPoint_ambient_underlying_isClosed
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X)
    (z : ComplexPoint (cycleComponent X x)
      (cycleComponentι X x ≫ structureMap)) :
    IsClosed {cycleComponentι X x z.underlying} := by
  have hclosed := (cycleComponentι X x).isClosedEmbedding.isClosedMap
    {z.underlying} (cycleComponent_complexPoint_underlying_isClosed structureMap x z)
  simpa only [Set.image_singleton] using hclosed

/-- A reduced cycle component has a smooth complex point whose underlying scheme point is
closed. -/
lemma exists_cycleComponent_smooth_closed_complexPoint
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (x : X) :
    ∃ z : ComplexPoint (cycleComponent X x)
        (cycleComponentι X x ≫ structureMap),
      z.underlying ∈
          (cycleComponentι X x ≫ structureMap).smoothLocus ∧
        IsClosed {z.underlying} := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint structureMap x
  exact ⟨z, hz, cycleComponent_complexPoint_underlying_isClosed structureMap x z⟩

/-- The coheight of the generic point of a component cannot exceed the relative dimension of
the smooth ambient complex scheme. -/
lemma cycleComponent_codimension_le
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (x : X) {d p : ℕ}
    [SmoothOfRelativeDimension d structureMap] (hx : Order.coheight x = p) :
    p ≤ d := by
  have hle := SmoothOfRelativeDimension.coheight_le_complex
    (f := structureMap) (d := d) x
  rw [hx] at hle
  exact_mod_cast hle

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has order
Krull dimension at most `d - p`. -/
lemma orderKrullDim_cycleComponent_le_sub
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (x : X) {d p : ℕ}
    [SmoothOfRelativeDimension d structureMap] (hx : Order.coheight x = p) :
    Order.krullDim (cycleComponent X x) ≤ d - p := by
  rw [orderKrullDim_cycleComponent]
  exact WithBot.coe_le_coe.mpr
    (SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := structureMap) (d := d) x hx)

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has
topological Krull dimension at most `d - p`. -/
lemma topologicalKrullDim_cycleComponent_le_sub
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (x : X) {d p : ℕ}
    [SmoothOfRelativeDimension d structureMap] (hx : Order.coheight x = p) :
    topologicalKrullDim (cycleComponent X x) ≤ d - p := by
  rw [topologicalKrullDim_cycleComponent]
  exact WithBot.coe_le_coe.mpr
    (SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := structureMap) (d := d) x hx)

end AlgebraicGeometry
