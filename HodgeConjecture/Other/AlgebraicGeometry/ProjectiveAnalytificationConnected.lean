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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
public import HodgeConjecture.Other.AlgebraicGeometry.ProjectiveAnalytification
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothDimensionFormula

/-!
# Connected components of projective analytifications

The analytification of a smooth projective complex variety of complex dimension `d` is nonempty,
compact, and locally path connected.  Consequently it has finitely many connected and path
components, and connectedness is equivalent to path connectedness.  In complex dimension zero,
integrality also proves that the analytification is a singleton, hence connected and path
connected.

The local-to-path-connected reduction follows the distinction made in
[sphere-six-complex PR #192](https://github.com/deancureton/sphere-six-complex/pull/192): manifold
charts supply local path connectedness, but a separate global argument must supply connectedness.
That pull request proves global connectedness only for its particular quotient family.  It does
not prove the positive-dimensional algebraic analytification theorem needed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint.SmoothProjectiveComplexVariety

variable (V : SmoothProjectiveComplexVariety) (d : ℕ)

/-- A smooth projective complex analytification is locally path connected. -/
theorem locallyPathConnectedSpace [SmoothOfRelativeDimension d V.structureMap] :
    LocallyPathConnectedSpace V.analyticPoint :=
  ComplexPoint.locallyPathConnectedSpace V.structureMap d

/-- A smooth projective complex variety has a complex point. -/
noncomputable instance instNonemptyAnalyticPoint : Nonempty V.analyticPoint := by
  let _ : LocallyOfFiniteType V.structureMap := inferInstance
  let _ : JacobsonSpace V.scheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := V.scheme) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact ⟨(pointEquivClosedPoint V.structureMap).symm ⟨x, hx⟩⟩

/-- A compact, locally path connected projective analytification has finitely many connected
components. -/
theorem finiteConnectedComponents [SmoothOfRelativeDimension d V.structureMap] :
    Finite (ConnectedComponents V.analyticPoint) := by
  let _ : LocallyPathConnectedSpace V.analyticPoint := locallyPathConnectedSpace V d
  let _ : LocallyConnectedSpace V.analyticPoint := inferInstance
  let _ : CompactSpace V.analyticPoint := inferInstance
  infer_instance

/-- A compact, locally path connected projective analytification has finitely many path
components. -/
theorem finiteZerothHomotopy [SmoothOfRelativeDimension d V.structureMap] :
    Finite (ZerothHomotopy V.analyticPoint) := by
  let _ : LocallyPathConnectedSpace V.analyticPoint := locallyPathConnectedSpace V d
  let _ : CompactSpace V.analyticPoint := inferInstance
  infer_instance

/-- For a smooth projective complex analytification, connectedness is equivalent to path
connectedness.  This theorem does not supply the global connectedness premise. -/
theorem pathConnectedSpace_iff_connectedSpace [SmoothOfRelativeDimension d V.structureMap] :
    PathConnectedSpace V.analyticPoint ↔ ConnectedSpace V.analyticPoint := by
  let _ : LocallyPathConnectedSpace V.analyticPoint := locallyPathConnectedSpace V d
  exact _root_.pathConnectedSpace_iff_connectedSpace

/-- Every complex point of an integral smooth zero-dimensional variety lies over its generic
point. -/
lemma underlying_eq_genericPoint_of_dimension_eq_zero
    [SmoothOfRelativeDimension d V.structureMap] (hd : d = 0) (z : V.analyticPoint) :
    z.underlying = genericPoint V.scheme := by
  have hzle : Order.coheight z.underlying ≤ (0 : ℕ) := by
    rw [← hd]
    exact SmoothOfRelativeDimension.coheight_le_complex
      (f := V.structureMap) (d := d) z.underlying
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨(Order.coheight_eq_zero.mp (bot_unique hzle)) le_top,
    genericPoint_specializes z.underlying⟩

/-- The analytification of an integral smooth projective complex variety of dimension zero has at
most one point. -/
theorem subsingletonAnalyticPointOfDimensionEqZero
    [SmoothOfRelativeDimension d V.structureMap] (hd : d = 0) :
    Subsingleton V.analyticPoint := by
  constructor
  intro z w
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  rw [underlying_eq_genericPoint_of_dimension_eq_zero V d hd z,
    underlying_eq_genericPoint_of_dimension_eq_zero V d hd w]

/-- The analytification of an integral smooth projective complex variety of dimension zero is
connected. -/
theorem connectedSpaceOfDimensionEqZero
    [SmoothOfRelativeDimension d V.structureMap] (hd : d = 0) :
    ConnectedSpace V.analyticPoint := by
  let _ : Subsingleton V.analyticPoint := subsingletonAnalyticPointOfDimensionEqZero V d hd
  exact
    { toNonempty := inferInstance
      isPreconnected_univ := Set.Subsingleton.isPreconnected Set.subsingleton_univ }

/-- The analytification of an integral smooth projective complex variety of dimension zero is path
connected. -/
theorem pathConnectedSpaceOfDimensionEqZero
    [SmoothOfRelativeDimension d V.structureMap] (hd : d = 0) :
    PathConnectedSpace V.analyticPoint := by
  let _ : ConnectedSpace V.analyticPoint := connectedSpaceOfDimensionEqZero V d hd
  exact (pathConnectedSpace_iff_connectedSpace V d).mpr inferInstance

end AlgebraicGeometry.ComplexPoint.SmoothProjectiveComplexVariety
