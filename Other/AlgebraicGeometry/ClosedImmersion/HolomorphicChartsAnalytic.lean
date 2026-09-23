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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.HolomorphicCharts

/-!
# Analytic provenance of the canonical flattening chart

The canonical closed-immersion flattening chart is stored downstream as an
`OpenPartialHomeomorph`.  Its construction nevertheless comes with a stronger
fact: the normal-coordinate change and its inverse are analytic at every point
of the selected source.  This file exposes that fact without changing the
chart data structure, so analytic ideal-factorisation arguments can retain the
provenance of the canonical chart.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The canonical flattening chart's normal-coordinate change is analytic at every
ambient source point, together with its inverse at the corresponding image. -/
theorem analyticAt_closedImmersionHolomorphicFlatteningChart_normalCoordinateChange
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z)
      (localChart X d (Point.map i z) y) ∧
    AnalyticAt ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) :=
  ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hy.1.2).2

/-- A regular function remains analytic after pullback by the canonical flattening chart. -/
theorem analyticAt_closedImmersionHolomorphicFlatteningChart_evaluate
    (V : X.left.Opens) (s : Γ(X.left, V))
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hV : (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) ∈ Point.overOpen V) :
    AnalyticAt ℂ
      (fun v ↦ Point.evaluate V s
        ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v))
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  have hA : AnalyticAt ℂ A.symm (e y) := by
    exact (analyticAt_closedImmersionHolomorphicFlatteningChart_normalCoordinateChange
      X Y i m d z y hy).2
  have htarget : A.symm (e y) ∈ (localChart X d (Point.map i z)).target := by
    have hleft : A.symm (e y) = localChart X d (Point.map i z) y := by
      change A.symm (A (localChart X d (Point.map i z) y)) = _
      exact A.left_inv hy.1.2.1
    rw [hleft]
    exact (localChart X d (Point.map i z)).map_source hy.1.1
  have hV' : (localChart X d (Point.map i z)).symm (A.symm (e y)) ∈
      Point.overOpen V := by
    simpa only [e, closedImmersionHolomorphicFlatteningChart_symm_apply] using hV
  have heval := analyticAt_localChart_symm_evaluate X d (Point.map i z) htarget V s hV'
  have hcomp := heval.comp hA
  apply hcomp.congr
  filter_upwards [] with v
  simp only [Function.comp_apply, A, closedImmersionHolomorphicFlatteningChart_symm_apply]

end AlgebraicGeometry.ComplexPoint
