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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothDimensionFormula
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

/-- The smooth locus of a reduced cycle component is Zariski dense. -/
lemma dense_cycleComponent_smoothLocus
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Dense
      ((cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus :
        Set (cycleComponent V.scheme x)) :=
  (cycleComponentι V.scheme x ≫ V.structureMap).dense_smoothLocus_of_perfectField

/-- The smooth locus of an integral cycle component is irreducible. -/
noncomputable instance cycleComponent_smoothLocus_irreducibleSpace
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IrreducibleSpace
      (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus := by
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus V x).nonempty
  let _ : Nonempty
      (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus :=
    ⟨⟨y, hy⟩⟩
  exact
    (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus.ι.isOpenEmbedding.irreducibleSpace

/-- The smooth locus of an integral cycle component is itself an integral scheme. -/
noncomputable instance cycleComponent_smoothLocus_isIntegral
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    IsIntegral (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The scheme points that are both smooth and closed are dense in a reduced cycle component. -/
lemma dense_cycleComponent_smooth_closedPoints
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    Dense
      (((cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus :
          Set (cycleComponent V.scheme x)) ∩
        closedPoints (cycleComponent V.scheme x)) := by
  let f := cycleComponentι V.scheme x ≫ V.structureMap
  let _ : JacobsonSpace (cycleComponent V.scheme x) :=
    LocallyOfFiniteType.jacobsonSpace f
  change Dense ((f.smoothLocus : Set (cycleComponent V.scheme x)) ∩
    closedPoints (cycleComponent V.scheme x))
  apply dense_iff_closure_eq.mpr
  exact (JacobsonSpace.closure_inter_closedPoints_eq_closure
    f.smoothLocus.2.isLocallyClosed).trans
      (dense_iff_closure_eq.mp (dense_cycleComponent_smoothLocus V x))

/-- The underlying scheme point of a complex point of a cycle component is closed. -/
lemma cycleComponent_complexPoint_underlying_isClosed
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap)) :
    IsClosed {z.underlying} := by
  change IsClosed {z.1 (IsLocalRing.closedPoint ℂ)}
  exact ((pointEquivClosedPoint
    (cycleComponentι V.scheme x ≫ V.structureMap)) z).2

/-- The image in the ambient variety of a complex point of a cycle component is a closed scheme
point. -/
lemma cycleComponent_complexPoint_ambient_underlying_isClosed
    (V : SmoothProjectiveComplexVariety) (x : V.scheme)
    (z : ComplexPoint (cycleComponent V.scheme x)
      (cycleComponentι V.scheme x ≫ V.structureMap)) :
    IsClosed {cycleComponentι V.scheme x z.underlying} := by
  have hclosed := (cycleComponentι V.scheme x).isClosedEmbedding.isClosedMap
    {z.underlying} (cycleComponent_complexPoint_underlying_isClosed V x z)
  simpa only [Set.image_singleton] using hclosed

/-- A reduced cycle component has a smooth complex point whose underlying scheme point is
closed. -/
lemma exists_cycleComponent_smooth_closed_complexPoint
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) :
    ∃ z : ComplexPoint (cycleComponent V.scheme x)
        (cycleComponentι V.scheme x ≫ V.structureMap),
      z.underlying ∈
          (cycleComponentι V.scheme x ≫ V.structureMap).smoothLocus ∧
        IsClosed {z.underlying} := by
  obtain ⟨z, hz⟩ := exists_cycleComponent_smooth_complexPoint V x
  exact ⟨z, hz, cycleComponent_complexPoint_underlying_isClosed V x z⟩

/-- The coheight of the generic point of a component cannot exceed the relative dimension of
the smooth ambient complex scheme. -/
lemma cycleComponent_codimension_le
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] (hx : Order.coheight x = p) :
    p ≤ d := by
  have hle := SmoothOfRelativeDimension.coheight_le_complex
    (f := V.structureMap) (d := d) x
  rw [hx] at hle
  exact_mod_cast hle

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has order
Krull dimension at most `d - p`. -/
lemma orderKrullDim_cycleComponent_le_sub
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] (hx : Order.coheight x = p) :
    Order.krullDim (cycleComponent V.scheme x) ≤ d - p := by
  rw [orderKrullDim_cycleComponent]
  exact WithBot.coe_le_coe.mpr
    (SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := V.structureMap) (d := d) x hx)

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has
topological Krull dimension at most `d - p`. -/
lemma topologicalKrullDim_cycleComponent_le_sub
    (V : SmoothProjectiveComplexVariety) (x : V.scheme) {d p : ℕ}
    [SmoothOfRelativeDimension d V.structureMap] (hx : Order.coheight x = p) :
    topologicalKrullDim (cycleComponent V.scheme x) ≤ d - p := by
  rw [topologicalKrullDim_cycleComponent]
  exact WithBot.coe_le_coe.mpr
    (SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := V.structureMap) (d := d) x hx)

end AlgebraicGeometry
