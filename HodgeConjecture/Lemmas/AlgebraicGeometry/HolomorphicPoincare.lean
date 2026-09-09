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

public import HodgeConjecture.Definitions.AlgebraicGeometry.AnalyticDifferentialForms
public import HodgeConjecture.Lemmas.Analysis.Calculus.DifferentialForm.Poincare

import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The holomorphic Poincare operator

This file connects the radial homotopy operator on complex differential forms to analytic power
series and to fixed-chart evaluations of raw holomorphic forms. The key point is that integration
over the real radial parameter preserves complex analyticity. We prove this directly by integrating
the homogeneous terms of a convergent formal multilinear series.
-/

@[expose] public noncomputable section

open ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Interval

namespace DifferentialForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]

/-- The formal power series of the radial primitive. -/
def radialPrimitiveSeries (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    FormalMultilinearSeries ℂ E (E [⋀^Fin n]→L[ℂ] ℂ) :=
  letI : SeminormedAddCommGroup (E →L[ℂ] E [⋀^Fin n]→L[ℂ] ℂ) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  fun
  | 0 => 0
  | k + 1 =>
      (continuousMultilinearCurryRightEquiv' ℂ k E (E [⋀^Fin n]→L[ℂ] ℂ)).symm
        (((k + n + 1 : ℕ) : ℂ)⁻¹ •
          ContinuousLinearMap.compContinuousMultilinearMap
            (ContinuousAlternatingMap.curryLeftLI
              (n := n) (𝕜 := ℂ) (E := E) (F := ℂ)).toContinuousLinearMap (p k))

omit [Nontrivial E] in
@[simp] lemma radialPrimitiveSeries_zero (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    radialPrimitiveSeries n p 0 = 0 := rfl

omit [Nontrivial E] in
@[simp] lemma radialPrimitiveSeries_succ_apply (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (k : ℕ) (x : E) :
    radialPrimitiveSeries n p (k + 1) (fun _ ↦ x) =
      ((k + n + 1 : ℕ) : ℂ)⁻¹ • (p k (fun _ ↦ x)).curryLeft x := by
  simp [radialPrimitiveSeries]
  congr 2

set_option maxHeartbeats 2000000 in
omit [Nontrivial E] in
lemma norm_radialPrimitiveSeries_succ_le (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) (k : ℕ) :
    ‖radialPrimitiveSeries n p (k + 1)‖ ≤ ‖p k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg (p k)) fun v ↦ ?_
  rw [radialPrimitiveSeries, continuousMultilinearCurryRightEquiv_symm_apply']
  simp only [_root_.smul_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply]
  calc
    ‖(((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (Fin.init v)).curryLeft (v (Fin.last k))‖ ≤
        ‖((k + n + 1 : ℕ) : ℂ)⁻¹‖ *
          ‖(p k (Fin.init v)).curryLeft (v (Fin.last k))‖ := by
      change ‖((((k + n + 1 : ℕ) : ℂ)⁻¹) •
          (p k (Fin.init v)).curryLeft (v (Fin.last k))).toContinuousMultilinearMap‖ ≤
        ‖((k + n + 1 : ℕ) : ℂ)⁻¹‖ *
          ‖((p k (Fin.init v)).curryLeft (v (Fin.last k))).toContinuousMultilinearMap‖
      rw [ContinuousAlternatingMap.toContinuousMultilinearMap_smul]
      exact ContinuousMultilinearMap.opNorm_smul_le _ _
    _ ≤ 1 * (‖p k (Fin.init v)‖ * ‖v (Fin.last k)‖) := by
      refine mul_le_mul ?_ ?_ (norm_nonneg _) zero_le_one
      · rw [norm_inv, norm_natCast]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (k + n)))
      · simpa only [ContinuousAlternatingMap.norm_curryLeft] using
          (p k (Fin.init v)).curryLeft.le_opNorm (v (Fin.last k))
    _ ≤ ‖p k‖ * ((∏ i : Fin k, ‖v (Fin.castSucc i)‖) * ‖v (Fin.last k)‖) := by
      rw [one_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      simpa only [Fin.init_def] using ContinuousMultilinearMap.le_opNorm (p k) (Fin.init v)
    _ = ‖p k‖ * ∏ i : Fin (k + 1), ‖v i‖ := by
      rw [Fin.prod_univ_castSucc]

omit [Nontrivial E] in
lemma radius_le_radius_radialPrimitiveSeries (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) :
    p.radius ≤ (radialPrimitiveSeries n p).radius := by
  refine ENNReal.le_of_forall_pos_nnreal_lt fun r hr₀ hr ↦ ?_
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  refine (summable_nat_add_iff
    (f := fun m ↦ ‖radialPrimitiveSeries n p m‖ * (r : ℝ) ^ m) 1).mp ?_
  exact ((p.summable_norm_mul_pow hr).mul_left (r : ℝ)).of_nonneg_of_le
    (fun _ ↦ by positivity) (fun k ↦ by
      change ‖radialPrimitiveSeries n p (k + 1)‖ * (r : ℝ) ^ (k + 1) ≤
        (r : ℝ) * (‖p k‖ * (r : ℝ) ^ k)
      rw [pow_succ]
      calc
        ‖radialPrimitiveSeries n p (k + 1)‖ * ((r : ℝ) ^ k * r) ≤
            ‖p k‖ * ((r : ℝ) ^ k * r) := by
              gcongr
              exact norm_radialPrimitiveSeries_succ_le n p k
        _ = (r : ℝ) * (‖p k‖ * (r : ℝ) ^ k) := by ring)

omit [Nontrivial E] in
/-- The formal radial primitive has positive convergence radius whenever the original series does. -/
lemma radialPrimitiveSeries_radius_pos (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (hp : 0 < p.radius) : 0 < (radialPrimitiveSeries n p).radius :=
  hp.trans_le (radius_le_radius_radialPrimitiveSeries n p)

omit [Nontrivial E] in
/-- The sum of the formal radial primitive is analytic throughout the convergence ball of the
original differential form. -/
theorem analyticOnNhd_radialPrimitiveSeries_sum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (hp : 0 < p.radius) :
    AnalyticOnNhd ℂ (radialPrimitiveSeries n p).sum (Metric.eball 0 p.radius) :=
  ((radialPrimitiveSeries n p).hasFPowerSeriesOnBall
    (radialPrimitiveSeries_radius_pos n p hp)).analyticOnNhd.mono
    (Metric.eball_subset_eball (radius_le_radius_radialPrimitiveSeries n p))

/-- The real interval integral of a complex monomial. -/
lemma intervalIntegral_ofReal_pow (m : ℕ) :
    (∫ t : ℝ in 0..1, (t : ℂ) ^ m) = (((m + 1 : ℕ) : ℂ)⁻¹) := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun s : ℝ ↦ (((m + 1 : ℕ) : ℂ)⁻¹) * (s : ℂ) ^ (m + 1))
      ((t : ℂ) ^ m) t := by
    have h : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using!
        Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    have hn : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    convert (h.pow (m + 1)).const_mul (((m + 1 : ℕ) : ℂ)⁻¹) using 1
    all_goals first | rfl | (rw [Nat.add_sub_cancel, mul_one, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul])
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ ↦ hderiv t)
    ((Complex.continuous_ofReal.pow m).intervalIntegrable 0 1)

/-- Integrating a complex monomial times a fixed vector gives the same scalar factor. -/
lemma intervalIntegral_ofReal_pow_smul
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (m : ℕ) (v : G) :
    (∫ t : ℝ in 0..1, ((t : ℂ) ^ m) • v) = (((m + 1 : ℕ) : ℂ)⁻¹) • v := by
  rw [intervalIntegral.integral_smul_const, intervalIntegral_ofReal_pow]

omit [Nontrivial E] in
/-- On the convergence ball, the sum of the primitive series is the expected series of contracted
homogeneous coefficients. -/
lemma radialPrimitiveSeries_sum_eq_tsum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    {x : E} (hx : x ∈ Metric.eball 0 p.radius) :
    (radialPrimitiveSeries n p).sum x =
      ∑' k : ℕ, ((k + n + 1 : ℕ) : ℂ)⁻¹ • (p k (fun _ ↦ x)).curryLeft x := by
  have hx' : x ∈ Metric.eball 0 (radialPrimitiveSeries n p).radius :=
    Metric.eball_subset_eball (radius_le_radius_radialPrimitiveSeries n p) hx
  have hsum := (radialPrimitiveSeries n p).summable hx'
  rw [FormalMultilinearSeries.sum, ← hsum.sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, radialPrimitiveSeries_zero,
    zero_apply, zero_add]
  exact tsum_congr fun k ↦ radialPrimitiveSeries_succ_apply n p k x

omit [Nontrivial E] in
/-- The homogeneous expansion of a form can be contracted term by term along a real radial
segment. -/
lemma hasSum_radialIntegrand_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ ↦ ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x)
      (radialIntegrand n η t x) := by
  have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  have htx : (t : ℂ) • x ∈ Metric.eball (0 : E) R := by
    rw [mem_eball_zero_iff] at hx ⊢
    rw [enorm_smul]
    have htEnorm : ‖(t : ℂ)‖ₑ ≤ 1 := by
      rw [enorm_eq_nnnorm, ENNReal.coe_le_one_iff]
      exact NNReal.coe_le_coe.mp (by simpa using htNorm)
    exact (by simpa [mul_comm] using
      (mul_le_mul_right htEnorm ‖x‖ₑ).trans_lt (by simpa using hx))
  let contraction : (E [⋀^Fin (n + 1)]→L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) :=
    (ContinuousLinearMap.apply ℂ (E [⋀^Fin n]→L[ℂ] ℂ) x).comp
      (ContinuousAlternatingMap.curryLeftLI
        (n := n) (𝕜 := ℂ) (E := E) (F := ℂ)).toContinuousLinearMap
  have hs := (hp.hasSum htx).mapL contraction
  have hst := hs.const_smul ((t : ℂ) ^ n)
  have hst' : HasSum (fun k ↦ ((t : ℂ) ^ n) •
      contraction (p k (fun _ ↦ (t : ℂ) • x)))
      (((t : ℂ) ^ n) • (η ((t : ℂ) • x)).curryLeft x) := by
    simpa [contraction] using hst
  refine HasSum.congr_fun hst' (fun k ↦ ?_)
  change ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x =
    ((t : ℂ) ^ n) • (p k (fun _ ↦ (t : ℂ) • x)).curryLeft x
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  change (t : ℂ) ^ (k + n) * (p k (fun _ ↦ x)).curryLeft x v =
    (t : ℂ) ^ n * ((t : ℂ) ^ k * (p k (fun _ ↦ x)).curryLeft x v)
  rw [← mul_assoc, ← pow_add, add_comm n k]

omit [Nontrivial E] in
/-- The homogeneous expansion of a form may be integrated term by term along a real radial
segment. -/
lemma hasSum_intervalIntegral_radialTerms_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R) :
    HasSum (fun k : ℕ ↦ ∫ t : ℝ in 0..1,
        ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x)
      (radialHomotopy n η x) := by
  let F : ℕ → ℝ → (E [⋀^Fin n]→L[ℂ] ℂ) := fun k t ↦
    ((t : ℂ) ^ (k + n)) • (p k (fun _ ↦ x)).curryLeft x
  let bound : ℕ → ℝ → ℝ := fun k _ ↦ ‖p k (fun _ ↦ x)‖ * ‖x‖
  refine intervalIntegral.hasSum_integral_of_dominated_convergence bound (fun k ↦ ?_)
    (fun k ↦ ?_) ?_ ?_ ?_
  · exact ((Complex.continuous_ofReal.pow (k + n)).smul continuous_const).aestronglyMeasurable
  · filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have htNorm : ‖(t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
      exact ht.2
    have hpow : ‖(t : ℂ) ^ (k + n)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) htNorm
    have hsmul : ‖((t : ℂ) ^ (k + n) • (p k (fun _ ↦ x)).curryLeft x)‖ ≤
        ‖(t : ℂ) ^ (k + n)‖ * ‖(p k (fun _ ↦ x)).curryLeft x‖ := by
      change ‖(((t : ℂ) ^ (k + n) •
          (p k (fun _ ↦ x)).curryLeft x).toContinuousMultilinearMap)‖ ≤
        ‖(t : ℂ) ^ (k + n)‖ *
          ‖((p k (fun _ ↦ x)).curryLeft x).toContinuousMultilinearMap‖
      rw [ContinuousAlternatingMap.toContinuousMultilinearMap_smul]
      exact ContinuousMultilinearMap.opNorm_smul_le _ _
    exact hsmul.trans <| calc
      ‖(t : ℂ) ^ (k + n)‖ * ‖(p k (fun _ ↦ x)).curryLeft x‖ ≤
          1 * (‖p k (fun _ ↦ x)‖ * ‖x‖) := by
        refine mul_le_mul hpow ?_ (norm_nonneg _) zero_le_one
        simpa only [ContinuousAlternatingMap.norm_curryLeft] using
          (p k (fun _ ↦ x)).curryLeft.le_opNorm x
      _ = bound k t := by simp [bound]
  · filter_upwards [] with t ht
    exact ((p.summable_norm_apply
      (Metric.eball_subset_eball hp.r_le hx)).mul_right ‖x‖)
  · simp [bound]
  · filter_upwards [] with t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact hasSum_radialIntegrand_of_hasFPowerSeriesOnBall n p η hp hx ⟨ht.1.le, ht.2⟩

omit [Nontrivial E] in
/-- On a power-series ball, the radial homotopy is exactly the sum of the formal primitive series. -/
theorem radialHomotopy_eq_radialPrimitiveSeries_sum (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) {x : E} (hx : x ∈ Metric.eball 0 R) :
    radialHomotopy n η x = (radialPrimitiveSeries n p).sum x := by
  have hs := hasSum_intervalIntegral_radialTerms_of_hasFPowerSeriesOnBall n p η hp hx
  have hs' : HasSum (fun k : ℕ ↦
      (((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (fun _ ↦ x)).curryLeft x)
      (radialHomotopy n η x) := HasSum.congr_fun hs fun k ↦
    (intervalIntegral_ofReal_pow_smul (k + n) ((p k (fun _ ↦ x)).curryLeft x)).symm
  calc
    radialHomotopy n η x = ∑' k : ℕ,
        (((k + n + 1 : ℕ) : ℂ)⁻¹) • (p k (fun _ ↦ x)).curryLeft x := hs'.tsum_eq.symm
    _ = (radialPrimitiveSeries n p).sum x :=
      (radialPrimitiveSeries_sum_eq_tsum n p
        (Metric.eball_subset_eball hp.r_le hx)).symm

omit [Nontrivial E] in
/-- Integrating a complex-analytic differential form over the real radial parameter preserves
complex analyticity. -/
theorem analyticOnNhd_radialHomotopy_of_hasFPowerSeriesOnBall (n : ℕ)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) {R : ENNReal}
    (hp : HasFPowerSeriesOnBall η p 0 R) :
    AnalyticOnNhd ℂ (radialHomotopy n η) (Metric.eball 0 R) :=
  AnalyticOnNhd.congr Metric.isOpen_eball
    ((analyticOnNhd_radialPrimitiveSeries_sum n p hp.radius_pos).mono
      (Metric.eball_subset_eball hp.r_le))
    fun _ hx ↦ (radialHomotopy_eq_radialPrimitiveSeries_sum n p η hp hx).symm

omit [Nontrivial E] in
/-- The analytic Poincaré lemma on a complex normed-space ball. The primitive is the explicit
radial homotopy, and no exactness assumption is used. -/
theorem exists_analyticOnNhd_primitive_on_ball_of_hasFPowerSeriesOnBall
    [FiniteDimensional ℂ E] (n : ℕ) {r : NNReal} (hr : 0 < r)
    (p : FormalMultilinearSeries ℂ E (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hp : HasFPowerSeriesOnBall η p 0 (r : ENNReal))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball 0 (r : ℝ))) :
    ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
      AnalyticOnNhd ℂ θ (Metric.ball 0 (r : ℝ)) ∧
        Set.EqOn (extDeriv θ) η (Metric.ball 0 (r : ℝ)) := by
  have hηanalytic : AnalyticOnNhd ℂ η (Metric.ball 0 (r : ℝ)) := by
    simpa only [Metric.eball_coe] using hp.analyticOnNhd
  have hη : ContDiffOn ℂ 1 η (Metric.ball 0 (r : ℝ)) :=
    hηanalytic.contDiffOn Metric.isOpen_ball.uniqueDiffOn
  refine ⟨radialHomotopy n η, ?_,
    extDeriv_radialHomotopy_of_closedOn n η Metric.isOpen_ball
      ((convex_ball (0 : E) (r : ℝ)).starConvex (Metric.mem_ball_self (by exact_mod_cast hr)))
      hη hclosed⟩
  simpa only [Metric.eball_coe] using
    analyticOnNhd_radialHomotopy_of_hasFPowerSeriesOnBall n p η hp

omit [Nontrivial E] in
/-- The analytic Poincaré lemma after shrinking an arbitrary analytic ball around the origin.
The smaller radius is chosen inside both the original ball and the convergence ball of the power
series of the form at the origin. -/
theorem exists_analyticOnNhd_primitive_on_smaller_ball
    [FiniteDimensional ℂ E] (n : ℕ) {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball 0 r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball 0 r)) :
    ∃ ρ : NNReal, 0 < ρ ∧ (ρ : ℝ) < r ∧
      ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
        AnalyticOnNhd ℂ θ (Metric.ball 0 (ρ : ℝ)) ∧
          Set.EqOn (extDeriv θ) η (Metric.ball 0 (ρ : ℝ)) := by
  have hzero : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  obtain ⟨p, R, hp⟩ := hη 0 hzero
  have hrENN : 0 < (Real.toNNReal r : ENNReal) := by
    simpa only [ENNReal.coe_pos, Real.toNNReal_pos] using hr
  have hmin : 0 < min (Real.toNNReal r : ENNReal) R := lt_min hrENN hp.r_pos
  obtain ⟨ρ, hρpos, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hmin
  have hρR : (ρ : ENNReal) ≤ R :=
    le_trans hρ.le (min_le_right (Real.toNNReal r : ENNReal) R)
  have hρr : (ρ : ℝ) < r := by
    have hlt : (ρ : ENNReal) < (Real.toNNReal r : ENNReal) :=
      hρ.trans_le (min_le_left (Real.toNNReal r : ENNReal) R)
    have hlt' : (ρ : ℝ) < (Real.toNNReal r : ℝ) := by exact_mod_cast ENNReal.coe_lt_coe.mp hlt
    simpa only [Real.coe_toNNReal r hr.le] using hlt'
  exact ⟨ρ, by exact_mod_cast hρpos, hρr,
    exists_analyticOnNhd_primitive_on_ball_of_hasFPowerSeriesOnBall n
      (by exact_mod_cast hρpos) p η (hp.mono (by exact_mod_cast hρpos) hρR)
      (hclosed.mono (Metric.ball_subset_ball hρr.le))⟩

omit [Nontrivial E] in
/-- Translate the base point of a differential form field to the origin. -/
def translateForm {p : ℕ} (c : E) (A : E → E [⋀^Fin p]→L[ℂ] ℂ) :
    E → E [⋀^Fin p]→L[ℂ] ℂ := fun x ↦ A (c + x)

omit [Nontrivial E] in
lemma fderiv_translateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (c + x)) :
    fderiv ℂ (translateForm c A) x = fderiv ℂ A (c + x) := by
  have ht : HasFDerivAt (fun y : E ↦ c + y) (ContinuousLinearMap.id ℂ E) x :=
    (hasFDerivAt_id x).const_add c
  exact (hA.hasFDerivAt.comp x ht).fderiv.trans (ContinuousLinearMap.comp_id _)

omit [Nontrivial E] in
lemma extDeriv_translateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (c + x)) :
    extDeriv (translateForm c A) x = extDeriv A (c + x) := by
  rw [extDeriv, extDeriv, fderiv_translateForm c A x hA]

omit [Nontrivial E] [NormedSpace ℂ E] in
lemma add_mem_ball_iff (c x : E) (r : ℝ) :
    c + x ∈ Metric.ball c r ↔ x ∈ Metric.ball 0 r := by
  simp [Metric.mem_ball, dist_eq_norm]

omit [Nontrivial E] in
lemma analyticOnNhd_translateForm {p : ℕ} (c : E) (r : ℝ)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ)
    (hA : AnalyticOnNhd ℂ A (Metric.ball c r)) :
    AnalyticOnNhd ℂ (translateForm c A) (Metric.ball 0 r) :=
  hA.comp (analyticOnNhd_const.add analyticOnNhd_id) fun x hx ↦
    (add_mem_ball_iff c x r).2 hx

omit [Nontrivial E] in
/-- Translate a differential form field from origin-centered coordinates back to a center. -/
def untranslateForm {p : ℕ} (c : E) (A : E → E [⋀^Fin p]→L[ℂ] ℂ) :
    E → E [⋀^Fin p]→L[ℂ] ℂ := fun x ↦ A (x - c)

omit [Nontrivial E] in
lemma fderiv_untranslateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (x - c)) :
    fderiv ℂ (untranslateForm c A) x = fderiv ℂ A (x - c) := by
  have ht : HasFDerivAt (fun y : E ↦ y - c) (ContinuousLinearMap.id ℂ E) x :=
    hasFDerivAt_sub_const c
  exact (hA.hasFDerivAt.comp x ht).fderiv.trans (ContinuousLinearMap.comp_id _)

omit [Nontrivial E] in
lemma extDeriv_untranslateForm {p : ℕ} (c : E)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ) (x : E)
    (hA : DifferentiableAt ℂ A (x - c)) :
    extDeriv (untranslateForm c A) x = extDeriv A (x - c) := by
  rw [extDeriv, extDeriv, fderiv_untranslateForm c A x hA]

omit [Nontrivial E] [NormedSpace ℂ E] in
lemma mem_ball_iff_sub_mem_ball (c x : E) (r : ℝ) :
    x ∈ Metric.ball c r ↔ x - c ∈ Metric.ball 0 r := by
  simp [Metric.mem_ball, dist_eq_norm]

omit [Nontrivial E] in
lemma analyticOnNhd_untranslateForm {p : ℕ} (c : E) (r : ℝ)
    (A : E → E [⋀^Fin p]→L[ℂ] ℂ)
    (hA : AnalyticOnNhd ℂ A (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (untranslateForm c A) (Metric.ball c r) :=
  hA.comp (analyticOnNhd_id.sub analyticOnNhd_const) fun x hx ↦
    (mem_ball_iff_sub_mem_ball c x r).1 hx

omit [Nontrivial E] in
/-- The analytic Poincaré lemma on a ball with arbitrary center, after shrinking the radius. -/
theorem exists_analyticOnNhd_primitive_on_smaller_centered_ball
    [FiniteDimensional ℂ E] (n : ℕ) {c : E} {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball c r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball c r)) :
    ∃ ρ : NNReal, 0 < ρ ∧ (ρ : ℝ) < r ∧
      ∃ θ : E → E [⋀^Fin n]→L[ℂ] ℂ,
        AnalyticOnNhd ℂ θ (Metric.ball c (ρ : ℝ)) ∧
          Set.EqOn (extDeriv θ) η (Metric.ball c (ρ : ℝ)) := by
  let η₀ := translateForm c η
  have hη₀ : AnalyticOnNhd ℂ η₀ (Metric.ball 0 r) :=
    analyticOnNhd_translateForm c r η hη
  have hclosed₀ : Set.EqOn (extDeriv η₀) 0 (Metric.ball 0 r) := by
    intro x hx
    rw [extDeriv_translateForm c η x
      ((hη (c + x) ((add_mem_ball_iff c x r).2 hx)).differentiableAt)]
    exact hclosed ((add_mem_ball_iff c x r).2 hx)
  obtain ⟨ρ, hρ, hρr, θ₀, hθ₀, hprim⟩ :=
    exists_analyticOnNhd_primitive_on_smaller_ball n hr η₀ hη₀ hclosed₀
  refine ⟨ρ, hρ, hρr, untranslateForm c θ₀,
    analyticOnNhd_untranslateForm c (ρ : ℝ) θ₀ hθ₀, ?_⟩
  intro y hy
  have hy₀ : y - c ∈ Metric.ball 0 (ρ : ℝ) :=
    (mem_ball_iff_sub_mem_ball c y (ρ : ℝ)).1 hy
  rw [extDeriv_untranslateForm c θ₀ y ((hθ₀ (y - c) hy₀).differentiableAt),
    hprim hy₀]
  change η (c + (y - c)) = η y
  congr 1
  abel

omit [Nontrivial E] in
/-- A closed analytic zero-form is constant on a ball with arbitrary center. -/
theorem zeroForm_eq_at_center_of_closedOn_ball {c : E} {r : ℝ} (hr : 0 < r)
    (η : E → E [⋀^Fin 0]→L[ℂ] ℂ)
    (hη : AnalyticOnNhd ℂ η (Metric.ball c r))
    (hclosed : Set.EqOn (extDeriv η) 0 (Metric.ball c r)) :
    Set.EqOn η (fun _ ↦ η c) (Metric.ball c r) := by
  let η₀ := translateForm c η
  have hη₀ : AnalyticOnNhd ℂ η₀ (Metric.ball 0 r) :=
    analyticOnNhd_translateForm c r η hη
  have hclosed₀ : Set.EqOn (extDeriv η₀) 0 (Metric.ball 0 r) := by
    intro x hx
    rw [extDeriv_translateForm c η x
      ((hη (c + x) ((add_mem_ball_iff c x r).2 hx)).differentiableAt)]
    exact hclosed ((add_mem_ball_iff c x r).2 hx)
  have hconst := zeroForm_eq_at_zero_of_closedOn η₀ Metric.isOpen_ball
    ((convex_ball (0 : E) r).starConvex (Metric.mem_ball_self hr))
    (hη₀.contDiffOn Metric.isOpen_ball.uniqueDiffOn : ContDiffOn ℂ 1 η₀ _) hclosed₀
  intro y hy
  have hy₀ : y - c ∈ Metric.ball 0 r := (mem_ball_iff_sub_mem_ball c y r).1 hy
  have h := hconst hy₀
  change η (c + (y - c)) = η (c + 0) at h
  simpa using h

end DifferentialForm

namespace AlgebraicGeometry.ComplexPoint

open Point

open CategoryTheory TopologicalSpace
open scoped Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

local instance holomorphicPoincareIsManifold [SmoothOfRelativeDimension d X.hom] :
    IsManifold (modelWithCornersSelf ℂ (Fin d → ℂ)) ω
      (ComplexPoint X) :=
  isManifold_omega X d

/-- Restricting a holomorphic function does not change its value in a fixed chart. -/
lemma chartSection_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d V z) :
    chartSection X d V z (holomorphicRestrictionAlgHom X d i f) y =
      chartSection X d U z f y := by
  have hyU : y ∈ chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  rw [chartSection_apply_of_mem X d V z _ hy,
    chartSection_apply_of_mem X d U z _ hyU]
  rfl

/-- Restricting a holomorphic function does not change its derivative in a fixed chart. -/
lemma chartSectionDifferential_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d V z) :
    chartSectionDifferential X d V z
        (holomorphicRestrictionAlgHom X d i f) y =
      chartSectionDifferential X d U z f y := by
  have hyU : y ∈ chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  have heq : Filter.EventuallyEq (nhds y)
      (chartSection X d V z
        (holomorphicRestrictionAlgHom X d i f))
      (chartSection X d U z f) := by
    filter_upwards [(isOpen_chartSectionDomain X d V z).mem_nhds hy] with w hw
    exact chartSection_holomorphicRestrictionAlgHom X d i z f hw
  rw [chartSectionDifferential, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V z) hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hyU]
  exact heq.fderiv_eq

/-- Fixed-chart evaluation of a raw form commutes with restriction. -/
lemma chartRawEvaluation_rawRestriction
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d V z) :
    chartRawEvaluation X d V z p
        (rawRestriction X d i p x) y =
      chartRawEvaluation X d U z p x y := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g c x hg hc ih =>
      rw [map_add, map_add, Pi.add_apply, map_add, Pi.add_apply, ih]
      simp only [rawRestriction, Algebra.DeRham.rawMap_single,
        chartRawEvaluation_single, Pi.smul_apply]
      simp only [chartGeneratorEvaluation, Algebra.DeRham.generatorMap]
      rw [chartSection_holomorphicRestrictionAlgHom X d i z g.1 hy]
      have hd :
          (fun j ↦ chartSectionDifferential X d V z
            (holomorphicRestrictionAlgHom X d i (g.2 j)) y) =
          (fun j ↦ chartSectionDifferential X d U z (g.2 j) y) := by
        funext j
        exact chartSectionDifferential_holomorphicRestrictionAlgHom
          X d i z (g.2 j) hy
      rw [hd]

/-- For the analytic charted-space instance, `chartAt` is the algebraically constructed local
chart. -/
lemma chartAt_eq_localChart [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    chartAt (Fin d → ℂ) z = localChart X d z := rfl

/-- The change of coordinates from the chart at `z'` to the chart at `z`. -/
def fixedChartTransition [SmoothOfRelativeDimension d X.hom]
    (z z' : ComplexPoint X) : (Fin d → ℂ) → (Fin d → ℂ) :=
  fun y ↦ (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y)

/-- A fixed-chart transition is complex analytic wherever the two charts overlap. -/
lemma analyticAt_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (z z' : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ ((localChart X d z').symm.trans
      (localChart X d z)).source) :
    AnalyticAt ℂ (fixedChartTransition X d z z') y := by
  change AnalyticAt ℂ
    (fun v ↦ localChart X d z ((localChart X d z').symm v)) y
  exact analyticAt_localChart_transition X d z' z hy

/-- Expressions of a section in two overlapping fixed charts are related by the chart
transition. -/
lemma chartSection_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartSection X d U z' f y =
      chartSection X d U z f (fixedChartTransition X d z z' y) := by
  simp only [chartSection, Function.comp_apply, fixedChartTransition]
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hy]

/-- The coordinate derivatives of a section obey the chain rule under a fixed-chart
transition. -/
lemma chartSectionDifferential_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartSectionDifferential X d U z' f y =
      (chartSectionDifferential X d U z f
        (fixedChartTransition X d z z' y)).comp
          (fderiv ℂ (fixedChartTransition X d z z') y) := by
  have htransLocal : y ∈ ((localChart X d z').symm.trans
      (localChart X d z)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change y ∈ (localChart X d z').target
      simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
        ModelWithCorners.range_eq_univ, Set.inter_univ,
        chartAt_eq_localChart X d] using hy.1
    · change (localChart X d z').symm y ∈
        (localChart X d z).source
      simpa only [extChartAt_coe_symm, extChartAt_source,
        modelWithCornersSelf_coe_symm, Function.comp_id,
        chartAt_eq_localChart X d] using hyz
  have hT : DifferentiableAt ℂ (fixedChartTransition X d z z') y :=
    (analyticAt_fixedChartTransition X d z z' htransLocal).differentiableAt
  have hTy : fixedChartTransition X d z z' y ∈
      chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [show fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hy.2
  have hf : DifferentiableAt ℂ (chartSection X d U z f)
      (fixedChartTransition X d z z' y) :=
    ((chartSection_contDiffWithinAt X d U z f hTy).contDiffAt
      ((isOpen_chartSectionDomain X d U z).mem_nhds hTy)).differentiableAt (by simp)
  have heq : Filter.EventuallyEq (nhds y)
      (chartSection X d U z' f)
      (chartSection X d U z f ∘ fixedChartTransition X d z z') := by
    filter_upwards [((localChart X d z').symm.trans
      (localChart X d z)).open_source.mem_nhds htransLocal] with w hw
    apply chartSection_fixedChartTransition X d U z z' f
    rw [OpenPartialHomeomorph.trans_source] at hw
    have hw2 := hw.2
    change (localChart X d z').symm w ∈
      (localChart X d z).source at hw2
    simpa only [extChartAt_coe_symm, extChartAt_source,
      modelWithCornersSelf_coe_symm, Function.comp_id,
      chartAt_eq_localChart X d] using hw2
  rw [chartSectionDifferential, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z') hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hTy,
    heq.fderiv_eq]
  exact fderiv_fun_comp y hf hT

/-- Wedges of covectors commute with pullback along a continuous linear map. -/
lemma wedgeCovectors_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ℕ) (L : Fin p → F →L[ℂ] ℂ) (T : E →L[ℂ] F) :
    wedgeCovectors E p (fun i ↦ (L i).comp T) =
      (wedgeCovectors F p L).compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    wedgeCovectors_apply_eq_det]
  rfl

lemma add_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (a b : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (a + b).compContinuousLinearMap T =
      a.compContinuousLinearMap T + b.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma smul_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (c : ℂ) (a : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (c • a).compContinuousLinearMap T = c • a.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Evaluation of a raw form is covariant under a holomorphic fixed-chart transition. -/
lemma chartRawEvaluation_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartRawEvaluation X d U z' p x y =
      (chartRawEvaluation X d U z p x
        (fixedChartTransition X d z z' y)).compContinuousLinearMap
          (fderiv ℂ (fixedChartTransition X d z z') y) := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [_root_.map_zero, Pi.zero_apply]
      refine ContinuousAlternatingMap.ext fun v ↦ ?_
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  | single_add g c x hg hc ih =>
      rw [map_add, Pi.add_apply, map_add, Pi.add_apply,
        add_compContinuousLinearMap, ih]
      simp only [chartRawEvaluation_single, Pi.smul_apply,
        chartGeneratorEvaluation]
      rw [chartSection_fixedChartTransition X d U z z' g.1 hyz]
      have hd :
          (fun j ↦ chartSectionDifferential X d U z' (g.2 j) y) =
          (fun j ↦ (chartSectionDifferential X d U z (g.2 j)
            (fixedChartTransition X d z z' y)).comp
              (fderiv ℂ (fixedChartTransition X d z z') y)) := by
        funext j
        exact chartSectionDifferential_fixedChartTransition
          X d U z z' (g.2 j) hy hyz
      rw [hd, wedgeCovectors_compContinuousLinearMap]
      rw [smul_compContinuousLinearMap, smul_compContinuousLinearMap]

/-- Vanishing throughout one fixed chart detects a restriction-stable analytic relation, provided
the open set lies in the source of that chart. -/
lemma mem_restrictionStableAnalyticKernel_of_chartRawEvaluation_eq_zero
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) :
      Set (ComplexPoint X)) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    (hx : Set.EqOn (chartRawEvaluation X d U z p x) 0
      (chartSectionDomain X d U z)) :
    x ∈ restrictionStableAnalyticKernel X d U p := by
  rw [restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  apply (mem_chartEvaluationKernel_iff X d V p _).2
  intro z' y hy
  rw [chartRawEvaluation_rawRestriction X d i z' p x hy]
  have hyU :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
        ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) :=
    leOfHom i.unop hy.2
  have hyz :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source :=
    hsource hyU
  rw [chartRawEvaluation_fixedChartTransition X d U z z' p x
    ⟨hy.1, hyU⟩ hyz]
  have hTy : fixedChartTransition X d z z' y ∈
      chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [show fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hyU
  rw [hx hTy]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma contMDiffAt_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {q : ComplexPoint X} (hq : q ∈ Opposite.unop U) :
    ContMDiffAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x)) q := by
  have hqsource := hsource hq
  have hcoord :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q ∈
        chartSectionDomain X d U z := by
    refine ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).map_source hqsource, ?_⟩
    change (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q) ∈
        ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hqsource]
    exact hq
  exact (ha _ hcoord).contDiffAt.contMDiffAt.comp q
    (contMDiffAt_extChartAt' (by
      rwa [← extChartAt_source (modelWithCornersSelf ℂ (Fin d → ℂ))]))

lemma contMDiff_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z)) :
    ContMDiff (modelWithCornersSelf ℂ (Fin d → ℂ)) (modelWithCornersSelf ℂ ℂ) ω
      (fun q : (Opposite.unop U : Opens (ComplexPoint X)) ↦
        a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q)) :=
  fun q ↦ (contMDiffAt_subtype_iff
    (I := modelWithCornersSelf ℂ (Fin d → ℂ))
    (I' := modelWithCornersSelf ℂ ℂ)
    (U := (Opposite.unop U : Opens (ComplexPoint X)))
    (f := fun x : ComplexPoint X ↦
      a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x))
    (x := q)).mpr (contMDiffAt_chartFunction X d U z hsource a ha q.2)

/-- An analytic scalar function in one chart, regarded as a holomorphic section on the chart
source. -/
def holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z)) :
    OpenHolomorphicFunctions X d U := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯
  exact ⟨fun q ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q),
    contMDiff_chartFunction X d U z hsource a ha⟩

lemma chartSection_holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z
        (holomorphicSectionOfChart X d U z hsource a ha) y = a y := by
  rw [chartSection_apply_of_mem X d U z _ hy]
  change a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) = a y
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).right_inv hy.1]

lemma chartSectionDifferential_holomorphicSectionOfChart
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
        (holomorphicSectionOfChart X d U z hsource a ha) y =
      fderivWithin ℂ a (chartSectionDomain X d U z) y := by
  rw [chartSectionDifferential]
  exact fderivWithin_congr'
    (fun w hw ↦ chartSection_holomorphicSectionOfChart X d U z hsource a ha hw) hy

/-- The `i`-th fixed-chart coordinate as a holomorphic section. -/
def chartCoordinateSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) : OpenHolomorphicFunctions X d U :=
  holomorphicSectionOfChart X d U z hsource
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticOnNhd _)

lemma chartSection_chartCoordinateSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z (chartCoordinateSection X d U z hsource i) y =
      y i := by
  unfold chartCoordinateSection
  exact chartSection_holomorphicSectionOfChart X d U z hsource _ _ hy

lemma chartSectionDifferential_chartCoordinateSection
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
        (chartCoordinateSection X d U z hsource i) y =
      ContinuousLinearMap.proj i := by
  unfold chartCoordinateSection
  rw [chartSectionDifferential_holomorphicSectionOfChart X d U z hsource _ _ hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hy]
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).hasFDerivAt.fderiv

/-- The product of a tuple of coordinate covectors. -/
def covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compContinuousLinearMap
    (fun j ↦ ContinuousLinearMap.proj (I j))

@[simp] lemma covectorProduct_apply (d p : ℕ) (I : Fin p → Fin d)
    (v : Fin p → Fin d → ℂ) :
    covectorProduct d p I v = ∏ j, v j (I j) := by
  simp [covectorProduct, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- A multilinear form on a finite product is the sum of its coordinate monomials. -/
lemma multilinear_eq_sum_covectorProduct (d p : ℕ)
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    A = ∑ I : Fin p → Fin d,
      A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  change A.toMultilinearMap =
    ContinuousMultilinearMap.toMultilinearMapLinear
      (R' := ℂ) (∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I)
  rw [_root_.map_sum]
  simp_rw [_root_.map_smul]
  refine Module.Basis.ext_multilinear (fun _ : Fin p ↦ Pi.basisFun ℂ (Fin d)) fun v ↦ ?_
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single v]
  · simp [Pi.basisFun_apply]
  · intro I hI hne
    change A (fun j ↦ Pi.single (I j) 1) *
      covectorProduct d p I (fun j ↦ Pi.basisFun ℂ (Fin d) (v j)) = 0
    rw [covectorProduct_apply]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hz : (Pi.basisFun ℂ (Fin d) (v j)) (I j) = 0 := by
      simp [Pi.basisFun_apply, hj.symm]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
  · simp

/-- Alternatizing a coordinate monomial gives the wedge of its coordinate covectors. -/
lemma alternatization_covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap.alternatization (covectorProduct d p I) =
      wedgeCovectors (Fin d → ℂ) p (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeCovectors_apply_eq_det, ← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [covectorProduct_apply]
  congr 1

lemma alternatization_smul (d p : ℕ) (c : ℂ)
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    ContinuousMultilinearMap.alternatization (c • M) =
      c • ContinuousMultilinearMap.alternatization M := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [ContinuousMultilinearMap.alternatization_apply_apply, _root_.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [smul_comm]

lemma alternatization_toContinuousMultilinearMap (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    ContinuousMultilinearMap.alternatization A.toContinuousMultilinearMap =
      (p.factorial : ℂ) • A := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  change MultilinearMap.alternatization A.toAlternatingMap.toMultilinearMap =
    (p.factorial : ℂ) • A.toAlternatingMap
  simpa only [Fintype.card_fin, Nat.cast_smul_eq_nsmul] using
    AlternatingMap.coe_alternatization A.toAlternatingMap

/-- A continuous alternating form on `Fin d → ℂ` is the finite coordinate-wedge expansion
of its values on the standard coordinate vectors. -/
lemma alternating_eq_sum_wedgeCovectors (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    A = ∑ I : Fin p → Fin d,
      ((p.factorial : ℂ)⁻¹ * A (fun j ↦ Pi.single (I j) 1)) •
        wedgeCovectors (Fin d → ℂ) p
          (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  classical
  have hM := multilinear_eq_sum_covectorProduct d p A.toContinuousMultilinearMap
  have hAlt := congrArg ContinuousMultilinearMap.alternatization hM
  rw [alternatization_toContinuousMultilinearMap d p A] at hAlt
  simp only [_root_.map_sum] at hAlt
  simp_rw [alternatization_smul, alternatization_covectorProduct] at hAlt
  change (p.factorial : ℂ) • A =
    ∑ I : Fin p → Fin d, A (fun j ↦ Pi.single (I j) 1) •
      wedgeCovectors (Fin d → ℂ) p
        (fun j ↦ ContinuousLinearMap.proj (I j)) at hAlt
  have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  calc
    A = (p.factorial : ℂ)⁻¹ • ((p.factorial : ℂ) • A) := by
      rw [← mul_smul, inv_mul_cancel₀ hfac, one_smul]
    _ = (p.factorial : ℂ)⁻¹ • ∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) •
          wedgeCovectors (Fin d → ℂ) p
            (fun j ↦ ContinuousLinearMap.proj (I j)) := by rw [hAlt]
    _ = _ := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun I _ ↦ smul_smul _ _ _

/-- Evaluation at a fixed tuple is a continuous linear functional on continuous alternating
forms. -/
def alternatingFormEvaluation (d p : ℕ) (v : Fin p → Fin d → ℂ) :
    ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  let L : ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun A ↦ A v
      map_add' := fun A B ↦ by simp
      map_smul' := fun a A ↦ by simp [ContinuousAlternatingMap.smul_apply] }
  LinearMap.mkContinuous L (∏ j, ‖v j‖) (fun A ↦ by
    change ‖A v‖ ≤ (∏ j, ‖v j‖) * ‖A‖
    simpa only [mul_comm] using A.le_opNorm v)

/-- The coefficient of an alternating form field in its finite coordinate-wedge expansion. -/
def coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (I : Fin p → Fin d) (y : Fin d → ℂ) : ℂ :=
  (p.factorial : ℂ)⁻¹ * θ y (fun j ↦ Pi.single (I j) 1)

lemma analyticOnNhd_coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    {s : Set (Fin d → ℂ)} (hθ : AnalyticOnNhd ℂ θ s) (I : Fin p → Fin d) :
    AnalyticOnNhd ℂ (coordinateCoefficient d p θ I) s := by
  let e : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  exact ((alternatingFormEvaluation d p e).comp_analyticOnNhd hθ).const_smul
    (c := (p.factorial : ℂ)⁻¹)

/-- A finite raw form whose fixed-chart evaluation is a given analytic alternating-form field. -/
def rawFormOfAnalyticField [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (chartSectionDomain X d U z)) :
    Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p :=
  ∑ I : Fin p → Fin d,
    Finsupp.single
      (holomorphicSectionOfChart X d U z hsource
          (coordinateCoefficient d p θ I)
          (analyticOnNhd_coordinateCoefficient d p θ hθ I),
        fun j ↦ chartCoordinateSection X d U z hsource (I j)) 1

/-- The finite raw realization of an analytic alternating-form field evaluates to that field in
the chosen chart. -/
lemma chartRawEvaluation_rawFormOfAnalyticField
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (chartSectionDomain X d U z)) :
    Set.EqOn (chartRawEvaluation X d U z p
      (rawFormOfAnalyticField X d U z hsource p θ hθ)) θ
      (chartSectionDomain X d U z) := by
  intro y hy
  rw [rawFormOfAnalyticField, _root_.map_sum]
  simp_rw [chartRawEvaluation_single]
  simp only [one_smul]
  rw [Finset.sum_apply y Finset.univ]
  simp only [chartGeneratorEvaluation]
  simp_rw [chartSection_holomorphicSectionOfChart X d U z hsource _ _ hy,
    chartSectionDifferential_chartCoordinateSection X d U z hsource _ hy]
  exact (alternating_eq_sum_wedgeCovectors d p (θ y)).symm

/-- A holomorphic section is complex analytic in every fixed chart. -/
lemma analyticOnNhd_chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (chartSection X d U z f)
      (chartSectionDomain X d U z) :=
  (isOpen_chartSectionDomain X d U z).analyticOn_iff_analyticOnNhd.mp
    (chartSection_contDiffOn X d U z f).analyticOn

/-- The coordinate differential of a holomorphic section is analytic. -/
lemma analyticOnNhd_chartSectionDifferential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (chartSectionDifferential X d U z f)
      (chartSectionDomain X d U z) := by
  refine AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z)
    (analyticOnNhd_chartSection X d U z f).fderiv fun y hy ↦ ?_
  rw [chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hy]

lemma analyticOnNhd_chartGeneratorEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (g : Algebra.DeRham.Generator (OpenHolomorphicFunctions X d U) p)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ
      (fun y ↦ chartGeneratorEvaluation X d U z p g y v)
      (chartSectionDomain X d U z) := by
  let s := chartSectionDomain X d U z
  have hentry (i j : Fin p) : AnalyticOnNhd ℂ
      (fun y ↦ chartSectionDifferential X d U z (g.2 j) y (v i)) s :=
    (ContinuousLinearMap.apply ℂ ℂ (v i)).comp_analyticOnNhd
      (analyticOnNhd_chartSectionDifferential X d U z (g.2 j))
  have hprod (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ ∏ j : Fin p,
        chartSectionDifferential X d U z (g.2 (e j)) y (v j)) s :=
    Finset.univ.analyticOnNhd_fun_prod (fun j hj ↦ hentry j (e j))
  have hterm (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        chartSectionDifferential X d U z (g.2 (e j)) y (v j))) s := by
    convert (hprod e).const_smul (c := ((e.sign : ℤ) : ℂ)) using 1
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  have hdet : AnalyticOnNhd ℂ
      (fun y ↦ ∑ e : Equiv.Perm (Fin p), (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        chartSectionDifferential X d U z (g.2 (e j)) y (v j))) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun e he ↦ hterm e)
  have hmul := (analyticOnNhd_chartSection X d U z g.1).mul hdet
  refine AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z) hmul fun y _ ↦ ?_
  simp only [chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    wedgeCovectors_apply_eq_det, Matrix.det_apply]
  apply congrArg (chartSection X d U z g.1 y * ·)
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  rfl

lemma analyticOnNhd_chartRawEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun y ↦ chartRawEvaluation X d U z p x y v)
      (chartSectionDomain X d U z) := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [_root_.map_zero]
      exact analyticOnNhd_const
  | single_add g a x hg ha ih =>
      rw [map_add, chartRawEvaluation_single]
      have h := ((analyticOnNhd_chartGeneratorEvaluation_apply X d U z p g v).const_smul
        (c := a)).add ih
      convert h using 1
      funext y
      simp [Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]

/-- A raw holomorphic form has an analytic fixed-chart evaluation. -/
lemma analyticOnNhd_chartRawEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (x : Algebra.DeRham.RawForm ℂ (OpenHolomorphicFunctions X d U) p) :
    AnalyticOnNhd ℂ (chartRawEvaluation X d U z p x)
      (chartSectionDomain X d U z) := by
  classical
  let s := chartSectionDomain X d U z
  let e (I : Fin p → Fin d) : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  let W (I : Fin p → Fin d) :=
    wedgeCovectors (Fin d → ℂ) p (fun j ↦ ContinuousLinearMap.proj (I j))
  have hc (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ (p.factorial : ℂ)⁻¹ * chartRawEvaluation X d U z p x y (e I)) s := by
    convert (analyticOnNhd_chartRawEvaluation_apply X d U z p x (e I)).const_smul
      (c := (p.factorial : ℂ)⁻¹) using 1
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  have hterm (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ ((p.factorial : ℂ)⁻¹ *
        chartRawEvaluation X d U z p x y (e I)) • W I) s :=
    (hc I).smul analyticOnNhd_const
  have hsum : AnalyticOnNhd ℂ
      (fun y ↦ ∑ I : Fin p → Fin d,
        ((p.factorial : ℂ)⁻¹ * chartRawEvaluation X d U z p x y (e I)) • W I) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun I hI ↦ hterm I)
  exact AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z) hsum fun y _ ↦
    (alternating_eq_sum_wedgeCovectors d p (chartRawEvaluation X d U z p x y)).symm

/-- Every open neighborhood contains a smaller neighborhood that is exactly a Euclidean ball in
the fixed chart at the chosen point. -/
lemma exists_chartBall_le [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U) :
    ∃ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (_i : U ⟶ V)
      (r : ℝ),
      x ∈ Opposite.unop V ∧ 0 < r ∧
      ((Opposite.unop V : Opens (ComplexPoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      chartSectionDomain X d V x =
        Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := by
  let e := localChart X d x
  have hxsource : x ∈ e.source := mem_localChart_source X d x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _)) :=
    e.isOpen_inter_preimage_symm (Opposite.unop U).2
  have hximage : e x ∈ e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _) := by
    refine ⟨e.map_source hxsource, ?_⟩
    rw [Set.mem_preimage, e.left_inv hxsource]
    exact hxU
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp (hopen.mem_nhds hximage)
  let Vo : Opens (ComplexPoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxV : x ∈ Vo := ⟨hxsource, Metric.mem_ball_self hr⟩
  have hVU : Vo ≤ Opposite.unop U := by
    intro z hz
    have hzU : e.symm (e z) ∈ ((Opposite.unop U : Opens _) : Set _) := (hball hz.2).2
    rw [e.left_inv hz.1] at hzU
    exact hzU
  let V := Opposite.op Vo
  let i : U ⟶ V := (homOfLE hVU).op
  refine ⟨V, i, r, hxV, hr, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, chartAt_eq_localChart X d] using hz.1
  · unfold chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [V, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Vo : Set _) = Metric.ball (e x) r
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hytarget : y ∈ e.target := (hball hy).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Shrink a fixed chart ball to any smaller positive radius. -/
lemma exists_smaller_chartBall [SmoothOfRelativeDimension d X.hom]
    (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (r : ℝ)
    (hdom : chartSectionDomain X d V x =
      Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r)
    (ρ : NNReal) (hρ : 0 < ρ) (hρr : (ρ : ℝ) < r) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (_j : V ⟶ W),
      x ∈ Opposite.unop W ∧
      ((Opposite.unop W : Opens (ComplexPoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      chartSectionDomain X d W x = Metric.ball
        ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := by
  let e := localChart X d x
  have hdom' : e.target ∩ e.symm ⁻¹' ((Opposite.unop V : Opens _) : Set _) =
      Metric.ball (e x) r := by
    unfold chartSectionDomain at hdom
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe] at hdom
    exact hdom
  have hxsource : x ∈ e.source := mem_localChart_source X d x
  let Wo : Opens (ComplexPoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) (ρ : ℝ),
      e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxW : x ∈ Wo := ⟨hxsource, Metric.mem_ball_self (by exact_mod_cast hρ)⟩
  have hWV : Wo ≤ Opposite.unop V := by
    intro z hz
    have hezdom : e z ∈ e.target ∩ e.symm ⁻¹'
        ((Opposite.unop V : Opens _) : Set _) :=
      hdom'.symm ▸ Metric.ball_subset_ball hρr.le hz.2
    have hzV := hezdom.2
    rw [Set.mem_preimage, e.left_inv hz.1] at hzV
    exact hzV
  let W := Opposite.op Wo
  let j : V ⟶ W := (homOfLE hWV).op
  refine ⟨W, j, hxW, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, chartAt_eq_localChart X d] using hz.1
  · unfold chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [W, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Wo : Set _) = Metric.ball (e x) (ρ : ℝ)
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hyr : y ∈ Metric.ball (e x) r := Metric.ball_subset_ball hρr.le hy
      have hytarget : y ∈ e.target := (hdom'.symm ▸ hyr).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Every closed holomorphic form of positive degree is locally exact. -/
theorem exists_local_holomorphicForm_primitive [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U) (p : ℕ)
    (form : HolomorphicForm X d U (p + 1))
    (hclosed : holomorphicFormDifferential X d U (p + 1) form = 0) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (k : U ⟶ W)
      (θ : HolomorphicForm X d W p),
      x ∈ Opposite.unop W ∧
      holomorphicFormDifferential X d W p θ =
        holomorphicFormRestriction X d k (p + 1) form := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U (p + 1)) form
  have hrel : Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) (p + 1) a ∈
      holomorphicFormRelations X d U (p + 2) := by
    change Submodule.Quotient.mk (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) (p + 1) a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    exists_chartBall_le X d U x hxU
  let aV := rawRestriction X d i (p + 1) a
  let η := chartRawEvaluation X d V x (p + 1) aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact analyticOnNhd_chartRawEvaluation X d V x (p + 1) aV
  have hrelV : Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d V) (p + 1) aV ∈
      holomorphicFormRelations X d V (p + 2) := by
    have h := rawRestriction_mem_holomorphicFormRelations X d i (p + 2) hrel
    rwa [rawRestriction, Algebra.DeRham.rawMap_rawDifferential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hkernel : Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d V) (p + 1) aV ∈
        restrictionStableAnalyticKernel X d V (p + 2) := by
      rw [← holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
      exact hrelV
    have hchart : chartRawEvaluation X d V x (p + 2)
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions X d V) (p + 1) aV) y = 0 := by
      have hk := hkernel
      rw [restrictionStableAnalyticKernel] at hk
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hk
      specialize hk V (𝟙 V)
      rw [rawRestriction_id, LinearMap.id_apply] at hk
      exact (mem_chartEvaluationKernel_iff X d V (p + 2) _).1 hk x y hyV
    rw [chartRawEvaluation_rawDifferential X d V x (p + 1) aV hyV] at hchart
    have hwithin : extDerivWithin η (chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  obtain ⟨ρ, hρ, hρr, θfield, hθfield, hprim⟩ :=
    DifferentialForm.exists_analyticOnNhd_primitive_on_smaller_centered_ball p hr η hη hclosedη
  obtain ⟨W, j, hxW, hsourceW, hdomW⟩ :=
    exists_smaller_chartBall X d V x r hdomV ρ hρ hρr
  have hθW : AnalyticOnNhd ℂ θfield (chartSectionDomain X d W x) := by
    rw [hdomW]
    exact hθfield
  let b := rawFormOfAnalyticField X d W x hsourceW p θfield hθW
  let θ : HolomorphicForm X d W p := Submodule.Quotient.mk b
  refine ⟨W, i ≫ j, θ, hxW, ?_⟩
  change Submodule.Quotient.mk (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d W) p b) =
    Submodule.Quotient.mk (rawRestriction X d (i ≫ j) (p + 1) a)
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d W (p + 1))).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply mem_restrictionStableAnalyticKernel_of_chartRawEvaluation_eq_zero
    X d W x (p + 1) hsourceW
  intro y hy
  rw [_root_.map_sub, Pi.sub_apply,
    chartRawEvaluation_rawDifferential X d W x p b hy,
    extDerivWithin_congr'
      (chartRawEvaluation_rawFormOfAnalyticField X d W x hsourceW p θfield hθW) hy]
  have hwithin : extDerivWithin θfield (chartSectionDomain X d W x) y =
      extDeriv θfield y := by
    rw [extDerivWithin, extDeriv,
      fderivWithin_of_isOpen (isOpen_chartSectionDomain X d W x) hy]
  rw [hwithin]
  have hyball : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := hdomW ▸ hy
  rw [hprim hyball, rawRestriction_comp, LinearMap.comp_apply,
    chartRawEvaluation_rawRestriction X d j x (p + 1) aV hy]
  simp [η]

/-- In degree zero, the raw Kähler representative of a scalar evaluates to the constant
alternating map with that scalar value. -/
lemma chartRawEvaluation_rawConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U x) :
    chartRawEvaluation X d U x 0
        (Finsupp.single
          (algebraMap ℂ (OpenHolomorphicFunctions X d U) c, Fin.elim0) 1) y =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c := by
  rw [chartRawEvaluation_single, one_smul]
  simp only [chartGeneratorEvaluation, chartSection_apply_of_mem X d U x _ hy]
  change c • wedgeCovectors (Fin d → ℂ) 0 Fin.elim0 = _
  ext v
  simp [wedgeCovectors]

/-- A closed holomorphic zero-form is locally the image of a complex constant. -/
theorem exists_local_holomorphicForm_eq_constant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U)
    (form : HolomorphicForm X d U 0)
    (hclosed : holomorphicFormDifferential X d U 0 form = 0) :
    ∃ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (i : U ⟶ V) (c : ℂ),
      x ∈ Opposite.unop V ∧
      holomorphicFormRestriction X d i 0 form =
        holomorphicFormOfConstant X d V c := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U 0) form
  have hrel : Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) 0 a ∈
      holomorphicFormRelations X d U 1 := by
    change Submodule.Quotient.mk (Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d U) 0 a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    exists_chartBall_le X d U x hxU
  let aV := rawRestriction X d i 0 a
  let η := chartRawEvaluation X d V x 0 aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact analyticOnNhd_chartRawEvaluation X d V x 0 aV
  have hrelV : Algebra.DeRham.rawDifferential ℂ
      (OpenHolomorphicFunctions X d V) 0 aV ∈
      holomorphicFormRelations X d V 1 := by
    have h := rawRestriction_mem_holomorphicFormRelations X d i 1 hrel
    rwa [rawRestriction, Algebra.DeRham.rawMap_rawDifferential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hkernel : Algebra.DeRham.rawDifferential ℂ
        (OpenHolomorphicFunctions X d V) 0 aV ∈
        restrictionStableAnalyticKernel X d V 1 := by
      rw [← holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
      exact hrelV
    have hchart : chartRawEvaluation X d V x 1
        (Algebra.DeRham.rawDifferential ℂ
          (OpenHolomorphicFunctions X d V) 0 aV) y = 0 := by
      have hk := hkernel
      rw [restrictionStableAnalyticKernel] at hk
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hk
      specialize hk V (𝟙 V)
      rw [rawRestriction_id, LinearMap.id_apply] at hk
      exact (mem_chartEvaluationKernel_iff X d V 1 _).1 hk x y hyV
    rw [chartRawEvaluation_rawDifferential X d V x 0 aV hyV] at hchart
    have hwithin : extDerivWithin η (chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  have hconst :=
    DifferentialForm.zeroForm_eq_at_center_of_closedOn_ball hr η hη hclosedη
  let center := (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x
  let c := DifferentialForm.zeroFormCoeff η center
  refine ⟨V, i, c, hxV, ?_⟩
  change Submodule.Quotient.mk aV = Submodule.Quotient.mk
    (Finsupp.single
      (algebraMap ℂ (OpenHolomorphicFunctions X d V) c, Fin.elim0) 1)
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d V 0)).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply mem_restrictionStableAnalyticKernel_of_chartRawEvaluation_eq_zero
    X d V x 0 hsourceV
  intro y hy
  rw [_root_.map_sub, Pi.sub_apply]
  have hyball' : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := hdomV ▸ hy
  have hyball : y ∈ Metric.ball center r := by simpa only [center] using hyball'
  rw [show chartRawEvaluation X d V x 0 aV y = η center from hconst hyball]
  rw [chartRawEvaluation_rawConstant X d V x c hy]
  have hrepr := congrFun (DifferentialForm.zeroForm_eq_constOfIsEmpty η) center
  change η center =
    ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c at hrepr
  rw [hrepr]
  exact sub_self _

end AlgebraicGeometry.ComplexPoint
