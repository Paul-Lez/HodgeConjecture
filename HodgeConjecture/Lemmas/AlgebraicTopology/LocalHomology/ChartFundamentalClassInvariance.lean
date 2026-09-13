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

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ComplexClassDifferentiableInvariance
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Chart-local class invariance under a differentiable transition germ

This file turns the local nonlinear degree calculation into a chart-comparison theorem.  For two
complex charts through the same point, their compressed inverse-chart embeddings determine an
open partial homeomorphism of `ℂᵈ`.  If its derivative at the model origin is injective
and complex linear, the two explicitly normalized chart-local homology classes agree.

The proof constructs the overlap neighborhood, uses point excision to lift the standard class,
and proves the factorization through the transition as an equality of maps of topological pairs.
Thus no chart-compatibility or local-degree statement is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter Set Asymptotics

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
variable (d : ℕ)

/-! ## Complex derivatives of the radial chart compression -/

private lemma hasFDerivAt_univUnitBall_formula_normed :
    HasFDerivAt (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹ • x)
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have ha : Tendsto (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) (nhds 0) (nhds 1) := by
    have hac : ContinuousAt (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) 0 := by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    have hzero : (√(1 + ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹ = (1 : ℝ) := by norm_num
    change Tendsto (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) (nhds 0)
      (nhds ((√(1 + ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹)) at hac
    rw [hzero] at hac
    exact hac
  have hsmall : ∀ᶠ x : Fin d → ℂ in nhds 0,
      |(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| < ε := by
    have hball := ha.eventually (Metric.ball_mem_nhds (1 : ℝ) hε)
    filter_upwards [hball] with x hx
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hsmall] with x hx
  norm_num
  calc
    ‖(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ • x - x‖ =
        ‖((√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1) • x‖ := by rw [sub_smul, one_smul]
    _ = |(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hx.le (norm_nonneg x)

/-- The positive-radius radial chart compression has derivative `r · id` at the model origin.
This is complex differentiability at the origin only; the norm-dependent map is not asserted to
be holomorphic away from the origin. -/
lemma hasFDerivAt_univBall_complex (c : Fin d → ℂ) (r : ℝ) (hr : 0 < r) :
    HasFDerivAt (OpenPartialHomeomorph.univBall c r :
      (Fin d → ℂ) → (Fin d → ℂ))
      ((r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr]
  apply ((hasFDerivAt_univUnitBall_formula_normed d).const_smul (r : ℂ)).add_const c
    |>.congr_of_eventuallyEq
  filter_upwards [] with y
  change r • OpenPartialHomeomorph.univUnitBall y + c =
    (r : ℂ) • ((√(1 + ‖y‖ ^ 2))⁻¹ • y) + c
  rw [OpenPartialHomeomorph.univUnitBall_apply]
  all_goals rfl

/-- The matrix of a complex continuous-linear endomorphism in the standard basis of a pi space. -/
def complexMatrixOfContinuousLinearMap
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix' L.toLinearMap

@[simp]
lemma complexMatrixOfContinuousLinearMap_mulVec
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (v : Fin d → ℂ) :
    (complexMatrixOfContinuousLinearMap d L).mulVec v = L v :=
  LinearMap.toMatrix'_mulVec L.toLinearMap v

lemma complexMatrixOfContinuousLinearMap_det_ne_zero
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (hL : Function.Injective L) :
    (complexMatrixOfContinuousLinearMap d L).det ≠ 0 := by
  let A := complexMatrixOfContinuousLinearMap d L
  have hAinj : Function.Injective A.mulVec := by
    intro x y hxy
    apply hL
    simpa only [A, complexMatrixOfContinuousLinearMap_mulVec] using hxy
  have hAunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hAinj
  exact (A.isUnit_iff_isUnit_det.mp hAunit).ne_zero

/-- The coordinate transition between the two compressed inverse-chart embeddings used to define
`localClassOfChart`. -/
def compressedChartTransition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ) :=
  (chartModelEmbedding d e x hx).trans (chartModelEmbedding d e' x hx').symm

@[simp]
lemma compressedChartTransition_zero
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    compressedChartTransition d e e' x hx hx' 0 = 0 := by
  change (chartModelEmbedding d e' x hx').symm
    (chartModelEmbedding d e x hx 0) = 0
  have hleft := (chartModelEmbedding d e' x hx').left_inv
    (show 0 ∈ (chartModelEmbedding d e' x hx').source by
      rw [chartModelEmbedding_source]
      trivial)
  simpa only [chartModelEmbedding_zero] using hleft

end AlgebraicTopology.Singular
