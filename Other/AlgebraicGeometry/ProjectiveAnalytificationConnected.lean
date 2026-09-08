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

public import HodgeConjecture.Definitions.AlgebraicGeometry.Points
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.PathConnected

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexManifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothDimensionFormula
import Other.AlgebraicGeometry.ProjectiveAnalytification
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

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

namespace AlgebraicGeometry.ComplexPoint

open Point

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ) (d : ℕ)

/-- A smooth projective complex variety has a complex point. -/
noncomputable instance instNonemptyComplexPoint [IsIntegral X] [Smooth structureMap] :
    Nonempty (ComplexPoint (Over.mk structureMap)) := by
  let : LocallyOfFiniteType structureMap := inferInstance
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace structureMap
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := X) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let z := (pointEquivClosedPoint structureMap).symm ⟨x, hx⟩
  exact ⟨Over.homMk z.1 z.2⟩

/-- A compact, locally path connected projective analytification has finitely many connected
components. -/
theorem finiteConnectedComponents [IsProjective structureMap]
    [IsIntegral X] [Smooth structureMap] :
    Finite (ConnectedComponents (ComplexPoint (Over.mk structureMap))) := by
  let : LocallyPathConnectedSpace (ComplexPoint (Over.mk structureMap)) :=
    locallyPathConnectedSpace structureMap
  let : LocallyConnectedSpace (ComplexPoint (Over.mk structureMap)) := inferInstance
  infer_instance

/-- A compact, locally path connected projective analytification has finitely many path
components. -/
theorem finiteZerothHomotopy [IsProjective structureMap]
    [IsIntegral X] [Smooth structureMap] :
    Finite (ZerothHomotopy (ComplexPoint (Over.mk structureMap))) := by
  let : LocallyPathConnectedSpace (ComplexPoint (Over.mk structureMap)) :=
    locallyPathConnectedSpace structureMap
  infer_instance

/-- For a smooth projective complex analytification, connectedness is equivalent to path
connectedness.  This theorem does not supply the global connectedness premise. -/
theorem pathConnectedSpace_iff_connectedSpace [IsIntegral X] [Smooth structureMap] :
    PathConnectedSpace (ComplexPoint (Over.mk structureMap)) ↔
      ConnectedSpace (ComplexPoint (Over.mk structureMap)) := by
  let : LocallyPathConnectedSpace (ComplexPoint (Over.mk structureMap)) :=
    locallyPathConnectedSpace structureMap
  exact _root_.pathConnectedSpace_iff_connectedSpace

/-- Every complex point of an integral smooth zero-dimensional variety lies over its generic
point. -/
lemma underlying_eq_genericPoint_of_dimension_eq_zero [IsIntegral X]
    [SmoothOfRelativeDimension d structureMap] (hd : d = 0)
    (z : ComplexPoint (Over.mk structureMap)) : z.underlying = genericPoint X := by
  let x : X := z.underlying
  change x = genericPoint X
  have hzle : Order.coheight x ≤ (0 : ℕ) := by
    rw [← hd]
    exact SmoothOfRelativeDimension.coheight_le_complex
      (f := structureMap) (d := d) x
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨(Order.coheight_eq_zero.mp (bot_unique hzle)) le_top,
    genericPoint_specializes x⟩

/-- The analytification of an integral smooth projective complex variety of dimension zero has at
most one point. -/
theorem subsingletonComplexPointOfDimensionEqZero [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap]
    [SmoothOfRelativeDimension d structureMap] (hd : d = 0) :
    Subsingleton (ComplexPoint (Over.mk structureMap)) := by
  constructor
  intro z w
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  rw [underlying_eq_genericPoint_of_dimension_eq_zero structureMap d hd z,
    underlying_eq_genericPoint_of_dimension_eq_zero structureMap d hd w]

/-- The analytification of an integral smooth projective complex variety of dimension zero is
connected. -/
theorem connectedSpaceOfDimensionEqZero [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap]
    [SmoothOfRelativeDimension d structureMap] (hd : d = 0) :
    ConnectedSpace (ComplexPoint (Over.mk structureMap)) := by
  let : Subsingleton (ComplexPoint (Over.mk structureMap)) :=
    subsingletonComplexPointOfDimensionEqZero structureMap d hd
  exact
    { toNonempty := inferInstance
      isPreconnected_univ := Set.Subsingleton.isPreconnected Set.subsingleton_univ }

/-- The analytification of an integral smooth projective complex variety of dimension zero is path
connected. -/
theorem pathConnectedSpaceOfDimensionEqZero [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap]
    [SmoothOfRelativeDimension d structureMap] (hd : d = 0) :
    PathConnectedSpace (ComplexPoint (Over.mk structureMap)) := by
  let : ConnectedSpace (ComplexPoint (Over.mk structureMap)) :=
    connectedSpaceOfDimensionEqZero structureMap d hd
  exact (pathConnectedSpace_iff_connectedSpace structureMap).mpr inferInstance

end AlgebraicGeometry.ComplexPoint
