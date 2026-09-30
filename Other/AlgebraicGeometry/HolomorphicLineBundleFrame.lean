/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicSheafGenerators

/-!
# The canonical local frames of the line bundle of a unit-sheaf extension

Over the lifting neighbourhood `E.localLifts.opens i` the line bundle of a unit-sheaf extension
has the canonical frame corresponding to the constant coordinate `1` in the `i`-th
trivialization. Its fibre coordinates are the transition values `x ↦ E.transitionValue i x x`,
and two such frames differ by the transition function of the extension. This is the geometric
input relating an isomorphism of section sheaves to the transition cocycles.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Bundle
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicLineBundleFrameTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)

theorem localTriv_continuousLinearEquivAt_apply (i : ComplexPoint X) (x : ComplexPoint X)
    (hx : x ∈ (E.lineBundleCore.localTriv i).baseSet) (v : E.lineBundleCore.Fiber x) :
    (E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ x hx v =
      E.transitionValue x i x • v := rfl

/-- The canonical local frame of the line bundle at `i`, over an open subset of the `i`-th
lifting neighbourhood. -/
def frame (i : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens i) : E.HolomorphicSections U :=
  E.sectionOfLocalCoordinate i U hU 1

set_option backward.isDefEq.respectTransparency false in
theorem frame_val (i : ComplexPoint X) (U : Opens (TopCat.of (ComplexPoint X)))
    (hU : U ≤ E.localLifts.opens i) (x : U) :
    (E.frame i U hU).val x = E.transitionValue i x x := by
  have hbase : (x : ComplexPoint X) ∈ (E.lineBundleCore.localTriv i).baseSet := hU x.property
  have hmem : (x : ComplexPoint X) ∈
      (E.localLifts.opens x ⊓ E.localLifts.opens i) ⊓ E.localLifts.opens x :=
    ⟨⟨E.localLifts.mem_opens x, hU x.property⟩, E.localLifts.mem_opens x⟩
  have h : ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ (x : ComplexPoint X) hbase)
      (E.transitionValue i x x : E.lineBundleCore.Fiber x) = (1 : ℂ) := by
    show E.transitionValue x i x * E.transitionValue i x x = 1
    rw [E.transitionValue_mul x i x x hmem, E.transitionValue_self x x (E.localLifts.mem_opens x)]
  show ((E.lineBundleCore.localTriv i).continuousLinearEquivAt ℂ (x : ComplexPoint X)
    hbase).symm (1 : ℂ) = E.transitionValue i x x
  rw [← h]
  exact ContinuousLinearEquiv.symm_apply_apply _ _

set_option backward.isDefEq.respectTransparency false in
theorem holRes_frame (i : ComplexPoint X) {U V : Opens (TopCat.of (ComplexPoint X))}
    (hU : U ≤ E.localLifts.opens i) (hVU : V ≤ U) :
    holRes E.sectionSheafOfModules hVU (E.frame i U hU) = E.frame i V (hVU.trans hU) := by
  apply Subtype.ext
  funext x
  show (E.frame i U hU).val ⟨x, hVU x.property⟩ = (E.frame i V (hVU.trans hU)).val x
  rw [frame_val, frame_val]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical local frame generates the sheaf of sections. -/
theorem holomorphicGenerates_frame (i : ComplexPoint X)
    (U : Opens (TopCat.of (ComplexPoint X))) (hU : U ≤ E.localLifts.opens i) :
    HolomorphicGenerates (M := E.sectionSheafOfModules) (E.frame i U hU) := by
  intro V hV
  have hfun : (fun r : (holomorphicRingSheaf X d).obj.obj (op V) =>
      r • holRes E.sectionSheafOfModules hV (E.frame i U hU)) =
      fun r => (E.localCoordinateEquiv i V (hV.trans hU)).symm r := by
    funext r
    rw [E.holRes_frame i hU hV]
    have h := (E.localCoordinateEquiv i V (hV.trans hU)).symm.map_smul r
      (1 : C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯)
    rw [smul_eq_mul, mul_one] at h
    exact h.symm
  rw [hfun]
  exact (E.localCoordinateEquiv i V (hV.trans hU)).symm.bijective

set_option backward.isDefEq.respectTransparency false in
/-- Two canonical local frames differ by the transition function of the extension. -/
theorem smul_frame (i j : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hi : V ≤ E.localLifts.opens i) (hj : V ≤ E.localLifts.opens j) :
    ((E.transitionUnit j i V hj hi).val : (holomorphicRingSheaf X d).obj.obj (op V)) •
        E.frame i V hi = E.frame j V hj := by
  apply Subtype.ext
  funext x
  show (E.transitionUnit j i V hj hi).val x * (E.frame i V hi).val x = (E.frame j V hj).val x
  rw [frame_val, frame_val]
  have hji : (x : ComplexPoint X) ∈ E.localLifts.opens j ⊓ E.localLifts.opens i :=
    ⟨hj x.property, hi x.property⟩
  have h1 : (E.transitionUnit j i V hj hi).val x = E.transitionValue j i x := by
    rw [transitionValue, dif_pos hji]
    exact E.transitionUnit_restrict_apply j i inf_le_left inf_le_right (le_inf hj hi) x
  rw [h1]
  exact E.transitionValue_mul j i x x ⟨hji, E.localLifts.mem_opens x⟩

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
