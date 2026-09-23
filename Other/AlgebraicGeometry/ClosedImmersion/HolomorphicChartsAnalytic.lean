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
public import Other.Analysis.Complex.NormalDerivative

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

/-- The first jet of a regular function in the canonical flattening coordinates is obtained by
composing its jet in the ambient local chart with the derivative of the inverse normal-coordinate
change.  This is the analytic bridge used to turn a nonzero algebraic cotangent class into the
nonzero normal derivative required by normal division. -/
theorem fderiv_closedImmersionHolomorphicFlatteningChart_evaluate
    (V : X.left.Opens) (s : Γ(X.left, V))
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hV : (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) ∈ Point.overOpen V) :
    fderiv ℂ (fun v ↦ Point.evaluate V s
        ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v))
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) =
      (fderiv ℂ (fun w ↦ Point.evaluate V s
        ((localChart X d (Point.map i z)).symm w))
        (localChart X d (Point.map i z) y)).comp
      (fderiv ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
        (closedImmersionHolomorphicFlatteningChart X Y i m d z y)) := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  let C := localChart X d (Point.map i z)
  let g := fun w ↦ Point.evaluate V s (C.symm w)
  have hA : AnalyticAt ℂ A.symm (e y) :=
    (analyticAt_closedImmersionHolomorphicFlatteningChart_normalCoordinateChange
      X Y i m d z y hy).2
  have hleft : A.symm (e y) = C y := by
    change A.symm (A (C y)) = _
    exact A.left_inv hy.1.2.1
  have htarget : A.symm (e y) ∈ C.target := by
    rw [hleft]
    exact C.map_source hy.1.1
  have hC : AnalyticAt ℂ g (A.symm (e y)) := by
    have h := analyticAt_localChart_symm_evaluate X d (Point.map i z) htarget V s
      (by simpa [e, A, C] using hV)
    exact h
  have hcomp := hC.hasStrictFDerivAt.hasFDerivAt.comp (e y)
    hA.hasStrictFDerivAt.hasFDerivAt
  have hcomp' : HasFDerivAt (g ∘ A.symm)
      ((fderiv ℂ g (A.symm (e y))).comp (fderiv ℂ A.symm (e y))) (e y) := by
    simpa only [hC.hasStrictFDerivAt.hasFDerivAt.fderiv,
      hA.hasStrictFDerivAt.hasFDerivAt.fderiv, Function.comp_apply] using hcomp
  have hEq : (fun v ↦ Point.evaluate V s (e.symm v)) = g ∘ A.symm := by
    funext v
    simp only [g, Function.comp_apply, e, A, C,
      closedImmersionHolomorphicFlatteningChart_symm_apply]
  calc
    fderiv ℂ (fun v ↦ Point.evaluate V s (e.symm v)) (e y) =
        fderiv ℂ (g ∘ A.symm) (e y) := by rw [hEq]
    _ = (fderiv ℂ g (A.symm (e y))).comp (fderiv ℂ A.symm (e y)) := hcomp'.fderiv
    _ = (fderiv ℂ (fun w ↦ Point.evaluate V s (C.symm w)) (C y)).comp
        (fderiv ℂ A.symm (e y)) := by rw [hleft]

/-- The preceding chain rule evaluated on the distinguished normal basis vector. -/
theorem fderiv_closedImmersionHolomorphicFlatteningChart_evaluate_normal
    (V : X.left.Opens) (s : Γ(X.left, V))
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hV : (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) ∈ Point.overOpen V) :
    fderiv ℂ (fun v ↦ Point.evaluate V s
        ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v))
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y)
      (0, fun _ : Fin (d - m) ↦ (1 : ℂ)) =
      fderiv ℂ (fun w ↦ Point.evaluate V s
        ((localChart X d (Point.map i z)).symm w))
        (localChart X d (Point.map i z) y)
        (fderiv ℂ (closedImmersionNormalCoordinateChange X Y i m d z).symm
          (closedImmersionHolomorphicFlatteningChart X Y i m d z y)
          (0, fun _ : Fin (d - m) ↦ (1 : ℂ))) := by
  rw [fderiv_closedImmersionHolomorphicFlatteningChart_evaluate
    X Y i m d z V s y hy hV]
  rfl

/-! A nonzero ambient jet remains nonzero after the canonical analytic coordinate change. -/
theorem fderiv_closedImmersionHolomorphicFlatteningChart_evaluate_ne_zero
    (V : X.left.Opens) (s : Γ(X.left, V))
    (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hV : (closedImmersionHolomorphicFlatteningChart X Y i m d z).symm
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) ∈ Point.overOpen V)
    (hambient : fderiv ℂ (fun w ↦ Point.evaluate V s
        ((localChart X d (Point.map i z)).symm w))
        (localChart X d (Point.map i z) y) ≠ 0) :
    fderiv ℂ (fun v ↦ Point.evaluate V s
        ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm v))
      (closedImmersionHolomorphicFlatteningChart X Y i m d z y) ≠ 0 := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  let C := localChart X d (Point.map i z)
  let g := fun w ↦ Point.evaluate V s (C.symm w)
  have hA : AnalyticAt ℂ A (C y) ∧ AnalyticAt ℂ A.symm (e y) :=
    analyticAt_closedImmersionHolomorphicFlatteningChart_normalCoordinateChange
      X Y i m d z y hy
  have hCtarget : C y ∈ C.target := C.map_source hy.1.1
  have hV' : C.symm (C y) ∈ Point.overOpen V := by
    have hyV : y ∈ Point.overOpen V := by
      change e.symm (e y) ∈ Point.overOpen V at hV
      rw [e.left_inv hy] at hV
      exact hV
    rw [C.left_inv hy.1.1]
    exact hyV
  have hg : AnalyticAt ℂ g (C y) := by
    exact analyticAt_localChart_symm_evaluate X d (Point.map i z) hCtarget V s hV'
  have hpull := Complex.fderiv_comp_symm_ne_zero_of_openPartialHomeomorph
    (e := A) (g := g) (p := C y) hy.1.2.1 hg hA.1 hA.2 hambient
  have hAC : A (C y) = e y := by
    rfl
  rw [hAC] at hpull
  simpa only [e, A, C, g, closedImmersionHolomorphicFlatteningChart_symm_apply] using hpull

/-! The pointwise result above is most useful after restricting the chart source to the
local-form domain.  This packages the resulting analyticity on the *whole* coordinate target of
that restricted chart, so a normal-division argument can be applied without extending a chart
function by an arbitrary value outside its provenance domain. -/

theorem analyticOnNhd_closedImmersionHolomorphicFlatteningChart_restrict_evaluate
    (V : X.left.Opens) (s : Γ(X.left, V))
    (A : Set (ComplexPoint X)) (hA : IsOpen A)
    (hAs : A ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hAV : A ⊆ Point.overOpen V) :
    AnalyticOnNhd ℂ
      (fun v ↦ Point.evaluate V s
        (((closedImmersionHolomorphicFlatteningChart X Y i m d z).restrOpen A hA).symm v))
      ((closedImmersionHolomorphicFlatteningChart X Y i m d z).restrOpen A hA).target := by
  intro v hv
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let eA := e.restrOpen A hA
  have hy : (eA.symm v) ∈ eA.source := eA.map_target hv
  have hyA : (eA.symm v) ∈ A := by
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hy.2
  have hye : (eA.symm v) ∈ e.source := hAs hyA
  have hV : e.symm (e (eA.symm v)) ∈ Point.overOpen V := by
    rw [e.left_inv hye]
    exact hAV hyA
  have hat := analyticAt_closedImmersionHolomorphicFlatteningChart_evaluate
    X Y i m d z V s (eA.symm v) hye hV
  have heq : eA (eA.symm v) = v := eA.right_inv hv
  rw [← heq]
  apply hat.congr
  filter_upwards [eA.open_target.mem_nhds (eA.map_source hy)] with w hw
  change Point.evaluate V s (e.symm w) = Point.evaluate V s (eA.symm w)
  congr 1

end AlgebraicGeometry.ComplexPoint
