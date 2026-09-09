/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticAnalyticNonvanishing
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import all Mathlib.Data.Complex.Basic

/-!
# Regular functions detect every tangent direction

On a smooth affine open, regular functions recover each canonical analytic coordinate
locally as a fraction. Consequently the derivatives of any algebra generators have trivial
common kernel. This is a rank statement about the actual analytification atlas.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Topology Filter
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance (priority := 10000) rankComplexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup
local instance (priority := 10000) rankComplexModule : Module ℂ ℂ :=
  (inferInstance : NormedSpace ℂ ℂ).toModule
local instance (priority := 10000) rankPiAddCommGroup : AddCommGroup (Fin d → ℂ) :=
  (inferInstance : NormedAddCommGroup (Fin d → ℂ)).toAddCommGroup
local instance (priority := 10000) rankPiModule : Module ℂ (Fin d → ℂ) :=
  (inferInstance : NormedSpace ℂ (Fin d → ℂ)).toModule
local instance (priority := 10000) rankPiTopology : TopologicalSpace (Fin d → ℂ) :=
  (inferInstance : PseudoMetricSpace (Fin d → ℂ)).toUniformSpace.toTopologicalSpace

/-- Every tangent direction is detected by the derivative of a regular function on an affine open. -/
theorem regular_fderiv_separates_tangent (U : X.left.Opens) (hU : IsAffineOpen U)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) (v : Fin d → ℂ)
    (hv : ∀ s : Γ(X.left, U),
      fderiv ℂ (regularInLocalChart X d U s z) (localChart X d z z) v = 0) : v = 0 := by
  funext j
  let D := localEtaleCoordinates X d z
  let e := localChart X d z
  let w := e z
  have hzsource : z ∈ e.source := mem_localChart_source X d z
  have hztarget : w ∈ e.target := e.map_source hzsource
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      Point.overOpen, Set.mem_ofPred_eq] using mem_localEtaleCoordinates X d z
  obtain ⟨f, hfD, hzf⟩ := hU.exists_basicOpen_le ⟨z.underlying, hzD⟩ hz
  let t := X.left.presheaf.map (homOfLE hfD).op (D.ambientCoordinateSection j)
  obtain ⟨k, a, ha⟩ := Point.exists_evaluate_basicOpen_eq_div (X := X) hU f t
  have hnonzero : regularInLocalChart X d U f z w ≠ 0 := by
    change Point.evaluate U f (e.symm (e z)) ≠ 0
    rw [e.left_inv hzsource]
    exact (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero f z hz).mp hzf
  have hderiv (s : Γ(X.left, U)) :=
    (analyticAt_regularInLocalChart X d U s z hz).differentiableAt.hasFDerivAt
  have hInv := (hasFDerivAt_inv' (𝕜 := ℂ) (pow_ne_zero k hnonzero)).comp w ((hderiv f).pow k)
  have hQuot := (hderiv a).mul hInv
  have hzeroQuot : fderiv ℂ
      (fun q => regularInLocalChart X d U a z q * (regularInLocalChart X d U f z q ^ k)⁻¹)
      w v = 0 := by
    exact (congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v) hQuot.fderiv).trans
      (by simp [hv, ContinuousLinearMap.comp_apply])
  have hmem : ∀ᶠ q in 𝓝 w, e.symm q ∈ Point.overOpen (X.left.basicOpen f) := by
    apply e.continuousAt_symm hztarget
      ((Point.isOpen_overOpen (X.left.basicOpen f)).mem_nhds _)
    rw [e.left_inv hzsource]
    exact hzf
  have hcoord : (fun q => regularInLocalChart X d U a z q *
      (regularInLocalChart X d U f z q ^ k)⁻¹) =ᶠ[𝓝 w] (fun q => q j) := by
    filter_upwards [hmem, e.open_target.mem_nhds hztarget] with q hq hqt
    change Point.evaluate U a (e.symm q) * (Point.evaluate U f (e.symm q) ^ k)⁻¹ = q j
    rw [← div_eq_mul_inv, ← ha (e.symm q) hq]
    rw [← Point.evaluate_res hfD (D.ambientCoordinateSection j) (e.symm q) hq]
    rw [← localChart_apply_component_eq_evaluate X d z (e.symm q) (e.map_target hqt) j]
    exact congrFun (e.right_inv hqt) j
  have hprojection : HasFDerivAt (fun q : Fin d → ℂ => q j)
      (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ) w :=
    (ContinuousLinearMap.proj j : (Fin d → ℂ) →L[ℂ] ℂ).hasFDerivAt
  have hd := congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v)
    (hcoord.fderiv_eq.trans hprojection.fderiv)
  exact hd.symm.trans hzeroQuot

attribute [local instance] regularSectionAlgebra

/-- Derivatives of any actual algebra generators have trivial common tangent kernel. -/
theorem generator_fderiv_separates_tangent (U : X.left.Opens) (hU : IsAffineOpen U)
    (z : ComplexPoint X) (hz : z ∈ Point.overOpen U) {σ : Type*}
    (φ : MvPolynomial σ ℂ →ₐ[ℂ] Γ(X.left, U)) (hφ : Function.Surjective φ)
    (v : Fin d → ℂ)
    (hv : ∀ j : σ, fderiv ℂ (regularInLocalChart X d U (φ (MvPolynomial.X j)) z)
      (localChart X d z z) v = 0) : v = 0 := by
  apply regular_fderiv_separates_tangent X d U hU z hz v
  intro s
  obtain ⟨p, rfl⟩ := hφ s
  induction p using MvPolynomial.induction_on with
  | C c =>
      have he := regularInLocalChart_scalar_eventually X d U c z hz
      have hφc : φ (MvPolynomial.C c) = regularSectionScalar X U c := φ.commutes c
      rw [hφc, he.fderiv_eq]
      exact congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v)
        (hasFDerivAt_const c (localChart X d z z)).fderiv
  | add p q hp hq =>
      rw [map_add, regularInLocalChart_add]
      have hD := ((analyticAt_regularInLocalChart X d U (φ p) z hz).differentiableAt.hasFDerivAt.add
        (analyticAt_regularInLocalChart X d U (φ q) z hz).differentiableAt.hasFDerivAt).fderiv
      exact (congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v) hD).trans
        (by simp only [add_apply, hp, hq, add_zero])
  | mul_X p j hp =>
      rw [map_mul, regularInLocalChart_mul]
      have hD := ((analyticAt_regularInLocalChart X d U (φ p) z hz).differentiableAt.hasFDerivAt.mul
        (analyticAt_regularInLocalChart X d U (φ (MvPolynomial.X j)) z hz).differentiableAt.hasFDerivAt).fderiv
      exact (congrArg (fun L : (Fin d → ℂ) →L[ℂ] ℂ => L v) hD).trans
        (by simp [hp, hv j])

/-- Two covectors separating the tangent plane have a nonzero actual analytic wedge. -/
theorem wedgeCovectors_two_ne_zero_of_separates
    (L : Fin 2 → (Fin 2 → ℂ) →L[ℂ] ℂ)
    (hL : ∀ v : Fin 2 → ℂ, (∀ i, L i v = 0) → v = 0) :
    wedgeCovectors (Fin 2 → ℂ) 2 L ≠ 0 := by
  let T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
    LinearMap.pi (fun i => (L i).toLinearMap)
  have hi : Function.Injective T := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hL
    intro i
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hvw i)
  have hs : Function.Surjective T := LinearMap.surjective_of_injective hi
  obtain ⟨v, hv⟩ := hs ![1, 0]
  obtain ⟨w, hw⟩ := hs ![0, 1]
  have hv' (i : Fin 2) : L i v = ![1, 0] i := congrFun hv i
  have hw' (i : Fin 2) : L i w = ![0, 1] i := congrFun hw i
  have hvalue : wedgeCovectors (Fin 2 → ℂ) 2 L ![v, w] = 1 := by
    rw [wedgeCovectors_apply_eq_det, Matrix.det_fin_two]
    simp [hv', hw']
  intro hz
  rw [hz] at hvalue
  exact zero_ne_one hvalue

end AlgebraicGeometry.ComplexPoint
