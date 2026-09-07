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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
public import FormalConjecturesForMathlib.AlgebraicGeometry.DimensionedSmoothProjective
public import FormalConjecturesForMathlib.AlgebraicGeometry.ProjectiveAnalytification
public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Connected components of projective analytifications

The analytification of a dimensioned smooth projective complex variety is nonempty, compact,
and locally path connected.  Consequently it has finitely many connected and path components,
and connectedness is equivalent to path connectedness.  In complex dimension zero, integrality
also proves that the analytification is a singleton, hence connected and path connected.

The local-to-path-connected reduction follows the distinction made in
[sphere-six-complex PR #192](https://github.com/deancureton/sphere-six-complex/pull/192): manifold
charts supply local path connectedness, but a separate global argument must supply connectedness.
That pull request proves global connectedness only for its particular quotient family.  It does
not prove the positive-dimensional algebraic analytification theorem needed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety

/-- A dimensioned smooth projective complex analytification is locally path connected. -/
noncomputable instance instLocallyPathConnectedSpace
    (V : DimensionedSmoothProjectiveComplexVariety) :
    LocallyPathConnectedSpace V.analyticPoint :=
  ComplexPoint.locallyPathConnectedSpace V.structureMap V.dimension

/-- A dimensioned smooth projective complex variety has a complex point. -/
noncomputable instance instNonemptyAnalyticPoint
    (V : DimensionedSmoothProjectiveComplexVariety) : Nonempty V.analyticPoint := by
  let _ : LocallyOfFiniteType V.structureMap := inferInstance
  let _ : JacobsonSpace V.scheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := V.scheme) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact ⟨(pointEquivClosedPoint V.structureMap).symm ⟨x, hx⟩⟩

/-- A compact, locally path connected projective analytification has finitely many connected
components. -/
theorem finiteConnectedComponents
    (V : DimensionedSmoothProjectiveComplexVariety) :
    Finite (ConnectedComponents V.analyticPoint) := by
  let _ : LocallyConnectedSpace V.analyticPoint := inferInstance
  let _ : CompactSpace V.analyticPoint := inferInstance
  infer_instance

/-- A compact, locally path connected projective analytification has finitely many path
components. -/
theorem finiteZerothHomotopy
    (V : DimensionedSmoothProjectiveComplexVariety) :
    Finite (ZerothHomotopy V.analyticPoint) := by
  let _ : CompactSpace V.analyticPoint := inferInstance
  infer_instance

/-- For a dimensioned smooth projective complex analytification, connectedness is equivalent to
path connectedness.  This theorem does not supply the global connectedness premise. -/
theorem pathConnectedSpace_iff_connectedSpace
    (V : DimensionedSmoothProjectiveComplexVariety) :
    PathConnectedSpace V.analyticPoint ↔ ConnectedSpace V.analyticPoint :=
  _root_.pathConnectedSpace_iff_connectedSpace

/-- Every complex point of an integral smooth zero-dimensional variety lies over its generic
point. -/
lemma underlying_eq_genericPoint_of_dimension_eq_zero
    (V : DimensionedSmoothProjectiveComplexVariety) (hV : V.dimension = 0)
    (z : V.analyticPoint) : z.underlying = genericPoint V.scheme := by
  have hzle : Order.coheight z.underlying ≤ (0 : ℕ) := by
    rw [← hV]
    exact SmoothOfRelativeDimension.coheight_le_complex
      (f := V.structureMap) (d := V.dimension) z.underlying
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨(Order.coheight_eq_zero.mp (bot_unique hzle)) le_top,
    genericPoint_specializes z.underlying⟩

/-- The analytification of an integral smooth projective complex variety of dimension zero has at
most one point. -/
noncomputable instance instSubsingletonAnalyticPointOfDimensionEqZero
    (V : DimensionedSmoothProjectiveComplexVariety) [Fact (V.dimension = 0)] :
    Subsingleton V.analyticPoint := by
  constructor
  intro z w
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  rw [underlying_eq_genericPoint_of_dimension_eq_zero V Fact.out z,
    underlying_eq_genericPoint_of_dimension_eq_zero V Fact.out w]

/-- The analytification of an integral smooth projective complex variety of dimension zero is
connected. -/
theorem connectedSpaceOfDimensionEqZero
    (V : DimensionedSmoothProjectiveComplexVariety) (hV : V.dimension = 0) :
    ConnectedSpace V.analyticPoint := by
  let _ : Fact (V.dimension = 0) := ⟨hV⟩
  exact
    { toNonempty := inferInstance
      isPreconnected_univ := Set.Subsingleton.isPreconnected Set.subsingleton_univ }

/-- The analytification of an integral smooth projective complex variety of dimension zero is path
connected. -/
theorem pathConnectedSpaceOfDimensionEqZero
    (V : DimensionedSmoothProjectiveComplexVariety) (hV : V.dimension = 0) :
    PathConnectedSpace V.analyticPoint := by
  let _ : ConnectedSpace V.analyticPoint := connectedSpaceOfDimensionEqZero V hV
  exact (pathConnectedSpace_iff_connectedSpace V).mpr inferInstance

end AlgebraicGeometry.ComplexPoint.DimensionedSmoothProjectiveComplexVariety
