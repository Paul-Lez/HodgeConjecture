/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCotangentTrivialization
public import Other.AlgebraicGeometry.RegularHolomorphicFormEvaluation
public import Other.AlgebraicGeometry.ExplicitEllipticHolomorphicDifferentials

/-!
# Pointwise nonvanishing of the elliptic invariant differential

The algebraic rank-one trivialization of each affine cotangent module persists under analytic
evaluation.  Since regular functions detect a nonzero tangent direction at every point of a
positive-dimensional smooth affine chart, the invariant differential has nonzero analytic
evaluation at every point of both charts.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

attribute [local instance] regularSectionAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- Evaluation of a regular Kahler one-form at the center of the analytic chart at `z`. -/
def regularKaehlerFormEvaluation (U : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ U) :
    KaehlerDifferential ℂ Γ(X.left, U) →ₗ[ℂ]
      (Fin d → ℂ) [⋀^Fin 1]→L[ℂ] ℂ :=
  (holomorphicFormEvaluation X d (.op (regularAnalyticOpen X U)) z 1
      (localChart X d z z)
      (localChart_center_mem_regularChartSectionDomain X d U z hz)).comp
    ((regularFormToHolomorphicForm X d U 1).comp
      (Algebra.DeRham.kaehlerToForm ℂ Γ(X.left, U)))

/-- Analytic evaluation respects multiplication of a regular one-form by a regular function. -/
theorem regularKaehlerFormEvaluation_smul (U : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ U) (a : Γ(X.left, U))
    (w : KaehlerDifferential ℂ Γ(X.left, U)) :
    regularKaehlerFormEvaluation X (d := d) U z hz (a • w) =
      Point.evaluate U a z • regularKaehlerFormEvaluation X (d := d) U z hz w := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective
    ℂ Γ(X.left, U) w
  induction v using Finsupp.induction with
  | zero =>
      rw [map_zero]
      change (0 : (Fin d → ℂ) [⋀^Fin 1]→L[ℂ] ℂ) =
        Point.evaluate U a z • (0 : (Fin d → ℂ) [⋀^Fin 1]→L[ℂ] ℂ)
      ext q
      simp [ContinuousAlternatingMap.smul_apply]
  | single_add b c v hb hc ih =>
      simp only [map_add, smul_add, ih, smul_add]
      congr 1
      simp only [Finsupp.linearCombination_single, smul_smul,
        regularKaehlerFormEvaluation, LinearMap.comp_apply,
        Algebra.DeRham.kaehlerToForm_smul_D]
      ext q
      have hq : (fun _ : Fin 1 => q 0) = q := by
        funext i
        exact congrArg q (Fin.eq_zero i).symm
      rw [← hq, ContinuousAlternatingMap.smul_apply,
        holomorphicFormEvaluation_regular_mk_one X d U (a * c) b z hz (q 0),
        holomorphicFormEvaluation_regular_mk_one X d U c b z hz (q 0)]
      simp only [Point.evaluate, dif_pos hz, map_mul]
      ring

/-- Evaluation of `ds` is the analytic derivative of the regular function `s`. -/
theorem regularKaehlerFormEvaluation_D_apply (U : X.left.Opens) (z : ComplexPoint X)
    (hz : z.underlying ∈ U) (s : Γ(X.left, U)) (v : Fin d → ℂ) :
    regularKaehlerFormEvaluation X (d := d) U z hz
        (KaehlerDifferential.D ℂ Γ(X.left, U) s) (fun _ => v) =
      fderiv ℂ (regularInLocalChart X d U s z) (localChart X d z z) v := by
  simp only [regularKaehlerFormEvaluation, LinearMap.comp_apply,
    Algebra.DeRham.kaehlerToForm_D]
  simpa only [Point.evaluate, dif_pos hz, map_one, one_mul] using
    holomorphicFormEvaluation_regular_mk_one X d U 1 s z hz v

/-- A regular generator of the cotangent module has nonzero analytic evaluation at every point
when the affine chart has positive complex dimension. -/
theorem regularKaehlerFormEvaluation_ne_zero_of_generator
    (U : X.left.Opens) (hU : IsAffineOpen U) (hd : 0 < d)
    (ω : KaehlerDifferential ℂ Γ(X.left, U))
    (hgen : ∀ w : KaehlerDifferential ℂ Γ(X.left, U),
      ∃ a : Γ(X.left, U), a • ω = w)
    (z : ComplexPoint X) (hz : z.underlying ∈ U) :
    regularKaehlerFormEvaluation X (d := d) U z hz ω ≠ 0 := by
  intro hω
  obtain ⟨s, hs⟩ := exists_regularInLocalChart_fderiv_ne_zero X d U hU z hz hd
  obtain ⟨a, ha⟩ := hgen (KaehlerDifferential.D ℂ Γ(X.left, U) s)
  have hD : regularKaehlerFormEvaluation X (d := d) U z hz
      (KaehlerDifferential.D ℂ Γ(X.left, U) s) = 0 := by
    rw [← ha, regularKaehlerFormEvaluation_smul, hω]
    module
  apply hs
  ext v
  have hv := congrArg
    (fun η : (Fin d → ℂ) [⋀^Fin 1]→L[ℂ] ℂ => η (fun _ => v)) hD
  rw [regularKaehlerFormEvaluation_D_apply] at hv
  simpa using hv

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The invariant differential has nonzero analytic value at every point of the `Z` chart. -/
theorem curveZDifferential_evaluation_ne_zero
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ chart 2) :
    regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) (chart 2) z hz
      curveZDifferential ≠ 0 := by
  apply regularKaehlerFormEvaluation_ne_zero_of_generator
    (Over.mk curveToBase) (d := 1) (chart 2) (chart_isAffineOpen 2) (by decide)
  intro w
  let a := curveZCotangentLinearEquiv.symm w
  refine ⟨a, ?_⟩
  change curveZCotangentLinearEquiv a = w
  exact curveZCotangentLinearEquiv.apply_symm_apply w

/-- The invariant differential has nonzero analytic value at every point of the chart containing
infinity. -/
theorem curveYDifferential_evaluation_ne_zero
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ chart 1) :
    regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) (chart 1) z hz
      curveYDifferential ≠ 0 := by
  apply regularKaehlerFormEvaluation_ne_zero_of_generator
    (Over.mk curveToBase) (d := 1) (chart 1) (chart_isAffineOpen 1) (by decide)
  intro w
  let a := curveYCotangentLinearEquiv.symm w
  refine ⟨a, ?_⟩
  rw [← curveYCotangentLinearEquiv_apply]
  exact curveYCotangentLinearEquiv.apply_symm_apply w

/-- Every complex point lies in one of the two affine charts, where the global invariant
differential is represented by a form with nonzero analytic evaluation. -/
theorem curveGlobalHolomorphicDifferential_locally_evaluation_ne_zero
    (z : ComplexPoint (Over.mk curveToBase)) :
    (∃ hz : z.underlying ∈ chart 2,
      regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) (chart 2) z hz
        curveZDifferential ≠ 0) ∨
    (∃ hz : z.underlying ∈ chart 1,
      regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) (chart 1) z hz
        curveYDifferential ≠ 0) := by
  have hz : z.underlying ∈ chart 1 ⊔ chart 2 := by
    rw [chart_one_sup_chart_two]
    trivial
  rcases hz with hz | hz
  · exact Or.inr ⟨hz, curveYDifferential_evaluation_ne_zero z hz⟩
  · exact Or.inl ⟨hz, curveZDifferential_evaluation_ne_zero z hz⟩

end AlgebraicGeometry.ExplicitEllipticCandidate
