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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.PathConnected

import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact
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

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- An integral complex scheme locally of finite type has a complex point: its space is Jacobson,
so it has a closed point, and the Nullstellensatz makes the residue field there `ℂ`. -/
noncomputable instance instNonemptyComplexPoint [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] : Nonempty (ComplexPoint X) := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (X := X.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let z := (pointEquivClosedPoint X.hom).symm ⟨x, hx⟩
  exact ⟨Over.homMk z.1 z.2⟩

/-- A compact, locally path connected projective analytification has finitely many connected
components. -/
theorem finiteConnectedComponents [IsProjective X.hom]
    [IsIntegral X.left] [Smooth X.hom] :
    Finite (ConnectedComponents (ComplexPoint X)) := by
  let : LocallyPathConnectedSpace (ComplexPoint X) :=
    locallyPathConnectedSpace X
  let : LocallyConnectedSpace (ComplexPoint X) := inferInstance
  infer_instance

/-- A compact, locally path connected projective analytification has finitely many path
components. -/
theorem finiteZerothHomotopy [IsProjective X.hom]
    [IsIntegral X.left] [Smooth X.hom] :
    Finite (ZerothHomotopy (ComplexPoint X)) := by
  let : LocallyPathConnectedSpace (ComplexPoint X) :=
    locallyPathConnectedSpace X
  infer_instance

/-- For a smooth projective complex analytification, connectedness is equivalent to path
connectedness.  This theorem does not supply the global connectedness premise. -/
theorem pathConnectedSpace_iff_connectedSpace [IsIntegral X.left] [Smooth X.hom] :
    PathConnectedSpace (ComplexPoint X) ↔
      ConnectedSpace (ComplexPoint X) := by
  let : LocallyPathConnectedSpace (ComplexPoint X) :=
    locallyPathConnectedSpace X
  exact _root_.pathConnectedSpace_iff_connectedSpace

/-- Every complex point of an integral smooth zero-dimensional variety lies over its generic
point. -/
lemma underlying_eq_genericPoint_of_dimension_eq_zero [IsIntegral X.left]
    [SmoothOfRelativeDimension d X.hom] (hd : d = 0)
    (z : ComplexPoint X) : z.underlying = genericPoint X.left := by
  let x : X.left := z.underlying
  change x = genericPoint X.left
  have hzle : Order.coheight x ≤ (0 : ℕ) := by
    rw [← hd]
    exact SmoothOfRelativeDimension.coheight_le_complex
      (f := X.hom) (d := d) x
  apply inseparable_iff_eq.mp
  rw [inseparable_iff_specializes_and]
  exact ⟨(Order.coheight_eq_zero.mp (bot_unique hzle)) le_top,
    genericPoint_specializes x⟩

/-- The analytification of an integral smooth projective complex variety of dimension zero has at
most one point. -/
theorem subsingletonComplexPointOfDimensionEqZero [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    [SmoothOfRelativeDimension d X.hom] (hd : d = 0) :
    Subsingleton (ComplexPoint X) := by
  constructor
  intro z w
  apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
  rw [underlying_eq_genericPoint_of_dimension_eq_zero X d hd z,
    underlying_eq_genericPoint_of_dimension_eq_zero X d hd w]

/-- The analytification of an integral smooth projective complex variety of dimension zero is
connected. -/
theorem connectedSpaceOfDimensionEqZero [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    [SmoothOfRelativeDimension d X.hom] (hd : d = 0) :
    ConnectedSpace (ComplexPoint X) := by
  let : Subsingleton (ComplexPoint X) :=
    subsingletonComplexPointOfDimensionEqZero X d hd
  exact
    { toNonempty := inferInstance
      isPreconnected_univ := Set.Subsingleton.isPreconnected Set.subsingleton_univ }

/-- The analytification of an integral smooth projective complex variety of dimension zero is path
connected. -/
theorem pathConnectedSpaceOfDimensionEqZero [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom]
    [SmoothOfRelativeDimension d X.hom] (hd : d = 0) :
    PathConnectedSpace (ComplexPoint X) := by
  let : ConnectedSpace (ComplexPoint X) :=
    connectedSpaceOfDimensionEqZero X d hd
  exact (pathConnectedSpace_iff_connectedSpace X).mpr inferInstance

end AlgebraicGeometry.ComplexPoint
