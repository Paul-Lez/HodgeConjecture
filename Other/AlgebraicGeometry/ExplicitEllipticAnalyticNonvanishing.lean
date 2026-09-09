/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RegularHolomorphicFormEvaluation
public import Other.AlgebraicGeometry.ExplicitEllipticInfinityCoordinates
public import Other.AlgebraicGeometry.ExplicitEllipticHolomorphicDifferentials
public import Other.AlgebraicGeometry.HolomorphicFormSheafification
import HodgeConjecture.Lemmas.AlgebraicGeometry.HolomorphicPoincare

import all Mathlib.Data.Complex.Basic

/-!
# Analytic nonvanishing of the explicit elliptic differential

The actual cubic equation forces `dv = 0` at infinity. Since the affine coordinate ring
generators detect the positive-dimensional analytic tangent space, `du` is nonzero there.
Evaluation through the regular-to-holomorphic comparison identifies the invariant form
with `-du`, proving nonvanishing of its actual glued holomorphic sheaf section.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Topology Filter
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

/-- The actual polynomial coordinate map of the Y chart. -/
abbrev curveYCoordinateMap : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Γ(curve, chart 1) :=
  hypersurfaceCoordinateMap (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)

/-- The two affine coordinates, expressed in the canonical analytic chart at infinity. -/
def curveYCoordinateInLocalChart (j : Fin 2) : (Fin 1 → ℂ) → ℂ :=
  regularInLocalChart (Over.mk curveToBase) 1 (chart 1)
    (curveYCoordinateMap (MvPolynomial.X j)) infinity

/-- The center of the canonical analytic chart at infinity. -/
def curveInfinityChartCenter : Fin 1 → ℂ :=
  localChart (Over.mk curveToBase) 1 infinity infinity

@[simp] theorem curveYCoordinateInLocalChart_center (j : Fin 2) :
    curveYCoordinateInLocalChart j curveInfinityChartCenter = 0 := by
  change Point.evaluate (chart 1) (curveYCoordinateMap (MvPolynomial.X j))
    ((localChart (Over.mk curveToBase) 1 infinity).symm
      (localChart (Over.mk curveToBase) 1 infinity infinity)) = 0
  rw [(localChart (Over.mk curveToBase) 1 infinity).left_inv
    (mem_localChart_source (Over.mk curveToBase) 1 infinity)]
  exact evaluate_curveYCoordinate_infinity j

theorem analyticAt_curveYCoordinateInLocalChart (j : Fin 2) :
    AnalyticAt ℂ (curveYCoordinateInLocalChart j) curveInfinityChartCenter :=
  analyticAt_regularInLocalChart (Over.mk curveToBase) 1 (chart 1) _ infinity
    infinity_mem_chart_one

/-- The affine equation holds throughout the chart-written coordinate functions. -/
theorem curveYCoordinateInLocalChart_equation :
    (fun w => curveYCoordinateInLocalChart 1 w - curveYCoordinateInLocalChart 0 w ^ 3 +
      curveYCoordinateInLocalChart 0 w * curveYCoordinateInLocalChart 1 w ^ 2) = 0 := by
  funext w
  let z := (localChart (Over.mk curveToBase) 1 infinity).symm w
  have heq := hypersurfaceCoordinateMap_equation
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
  have hv := congrArg (fun s => Point.evaluate (chart 1) s z) heq
  change Point.evaluate (chart 1) (curveYCoordinateMap (MvPolynomial.X 1)) z -
      Point.evaluate (chart 1) (curveYCoordinateMap (MvPolynomial.X 0)) z ^ 3 +
    Point.evaluate (chart 1) (curveYCoordinateMap (MvPolynomial.X 0)) z *
      Point.evaluate (chart 1) (curveYCoordinateMap (MvPolynomial.X 1)) z ^ 2 = 0
  by_cases hz : z.underlying ∈ chart 1
  · simp only [curveYCoordinateMap, chartEquation_y, map_add, map_sub, map_mul, map_pow,
      Point.evaluate, dif_pos hz, map_zero] at hv ⊢
    convert hv using 1
    rfl
  · simp only [Point.evaluate, dif_neg hz, zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), sub_zero, zero_mul, add_zero]

/-- The derivative of the second affine coordinate vanishes at infinity, by differentiating
the actual cubic equation there. -/
theorem fderiv_curveYCoordinateInLocalChart_one :
    fderiv ℂ (curveYCoordinateInLocalChart 1) curveInfinityChartCenter = 0 := by
  have hu := (analyticAt_curveYCoordinateInLocalChart 0).differentiableAt.hasFDerivAt
  have hv := (analyticAt_curveYCoordinateInLocalChart 1).differentiableAt.hasFDerivAt
  have heq := (hv.sub (hu.pow 3)).add (hu.mul (hv.pow 2))
  have hfun : ((curveYCoordinateInLocalChart 1 - fun x => curveYCoordinateInLocalChart 0 x ^ 3) +
      curveYCoordinateInLocalChart 0 * fun x => curveYCoordinateInLocalChart 1 x ^ 2) =
        (fun _ => 0) := curveYCoordinateInLocalChart_equation
  rw [hfun] at heq
  have hzero := heq
  have h := hzero.unique (hasFDerivAt_const 0 curveInfinityChartCenter)
  ext w
  have hw := congrArg (fun L => L w) h
  simpa [smul_apply, smul_eq_mul] using hw

/-- The first affine coordinate has nonzero analytic differential at infinity. This follows
from smooth positive dimension and generation of the actual affine section ring. -/
theorem fderiv_curveYCoordinateInLocalChart_zero_ne_zero :
    fderiv ℂ (curveYCoordinateInLocalChart 0) curveInfinityChartCenter ≠ 0 := by
  let := regularSectionAlgebra (Over.mk curveToBase) (chart 1)
  obtain ⟨j, hj⟩ := exists_generator_fderiv_ne_zero (Over.mk curveToBase) 1 (chart 1)
    (chart_isAffineOpen 1) infinity infinity_mem_chart_one (by decide) curveYCoordinateMap
    (hypersurfaceCoordinateMap_surjective _ _)
  fin_cases j
  · exact hj
  · exact False.elim (hj fderiv_curveYCoordinateInLocalChart_one)

@[simp] theorem evaluate_curveYDifferentialC_infinity :
    Point.evaluate (chart 1) (curveYCoordinateMap yDifferentialC) infinity = 1 := by
  have h0 := evaluate_curveYCoordinate_infinity (0 : Fin 2)
  have h1 := evaluate_curveYCoordinate_infinity (1 : Fin 2)
  simp only [Point.evaluate, dif_pos infinity_mem_chart_one] at h0 h1
  simp only [curveYCoordinateMap, yDifferentialC, map_add, map_sub, map_mul, map_pow,
    map_ofNat, map_one, Point.evaluate, dif_pos infinity_mem_chart_one]
  erw [h0, h1]
  norm_num

/-- The analytic evaluation of the explicit differential at infinity is `-du`. -/
theorem curveYHolomorphicDifferential_evaluation (v : Fin 1 → ℂ) :
    holomorphicFormEvaluation (Over.mk curveToBase) 1 (.op (curveAnalyticOpen (chart 1)))
        infinity 1 curveInfinityChartCenter
        (localChart_center_mem_regularChartSectionDomain (Over.mk curveToBase) 1
          (chart 1) infinity infinity_mem_chart_one)
        (curveDifferentialToHolomorphic (chart 1) curveYDifferential) (fun _ => v) =
      -(fderiv ℂ (curveYCoordinateInLocalChart 0) curveInfinityChartCenter v) := by
  have hk : Algebra.DeRham.kaehlerToForm ℂ Γ(curve, chart 1) curveYDifferential =
      -(Algebra.DeRham.mk ℂ _ 1 (curveYCoordinateMap yDifferentialC)
          (fun _ => curveYCoordinateMap (MvPolynomial.X 0)) -
        Algebra.DeRham.mk ℂ _ 1 (curveYCoordinateMap yDifferentialB)
          (fun _ => curveYCoordinateMap (MvPolynomial.X 1))) := by
    change Algebra.DeRham.kaehlerToForm ℂ Γ(curve, chart 1)
      (-(curveYCoordinateMap yDifferentialC • KaehlerDifferential.D ℂ Γ(curve, chart 1)
          (curveYCoordinateMap (MvPolynomial.X 0)) -
        curveYCoordinateMap yDifferentialB • KaehlerDifferential.D ℂ Γ(curve, chart 1)
          (curveYCoordinateMap (MvPolynomial.X 1)))) = _
    rw [map_neg, map_sub, Algebra.DeRham.kaehlerToForm_smul_D,
      Algebra.DeRham.kaehlerToForm_smul_D]
  simp only [curveDifferentialToHolomorphic, LinearMap.comp_apply]
  erw [hk]
  simp only [map_neg, map_sub,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.sub_apply]
  erw [holomorphicFormEvaluation_regular_mk_one, holomorphicFormEvaluation_regular_mk_one] <;>
    try exact infinity_mem_chart_one
  change -(Point.evaluate (chart 1) (curveYCoordinateMap yDifferentialC) infinity *
      fderiv ℂ (curveYCoordinateInLocalChart 0) curveInfinityChartCenter v -
    Point.evaluate (chart 1) (curveYCoordinateMap yDifferentialB) infinity *
      fderiv ℂ (curveYCoordinateInLocalChart 1) curveInfinityChartCenter v) = _
  rw [evaluate_curveYDifferentialC_infinity, fderiv_curveYCoordinateInLocalChart_one]
  simp

/-- The actual holomorphic form is nonzero, detected by its analytic value at infinity. -/
theorem curveYHolomorphicDifferential_ne_zero :
    curveDifferentialToHolomorphic (chart 1) curveYDifferential ≠ 0 := by
  intro h
  apply fderiv_curveYCoordinateInLocalChart_zero_ne_zero
  ext v
  have he := curveYHolomorphicDifferential_evaluation v
  rw [h, map_zero] at he
  simpa using he.symm

theorem curveYHolomorphicSheafDifferential_ne_zero :
    curveDifferentialToHolomorphicSheaf (chart 1) curveYDifferential ≠ 0 :=
  holomorphicDeRham_toSheafify_ne_zero (Over.mk curveToBase) 1
    (curveAnalyticOpen (chart 1)) 1 curveYHolomorphicDifferential_ne_zero

/-- The global form glued from the actual regular elliptic differential is nonzero. -/
theorem curveGlobalHolomorphicDifferential_ne_zero : curveGlobalHolomorphicDifferential ≠ 0 := by
  intro h
  have hr := curveGlobalHolomorphicDifferential_restrict_y
  rw [h, map_zero] at hr
  exact curveYHolomorphicSheafDifferential_ne_zero hr.symm

end AlgebraicGeometry.ExplicitEllipticCandidate
