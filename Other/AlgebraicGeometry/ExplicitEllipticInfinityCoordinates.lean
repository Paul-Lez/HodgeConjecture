/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticDifferentialOverlap

/-!
# Regular coordinates at the point at infinity

The vanishing loci of the actual quotient coordinates are the corresponding
projective coordinate loci. In particular both affine coordinates on the Y chart
evaluate to zero at the constructed point `[0:1:0]`.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A quotient chart coordinate vanishes precisely when its homogeneous numerator vanishes. -/
theorem evaluate_curveChartCoordinate_ne_zero_iff (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) (j : Fin 2)
    (P : Fin 3 → ℂ) (hP : P ≠ 0) (heq : equation.toProjective.Equation P)
    (hi : P (e 2) ≠ 0) :
    Point.evaluate (curveToPlane ⁻¹ᵁ ambientChart e)
        (hypersurfaceCoordinateMap (chartEquation e) (curveChartGlobalAlgEquiv e hp) (X j))
        (curvePoint P hP heq) ≠ 0 ↔ P (e j.castSucc) ≠ 0 := by
  have hz : curvePoint P hP heq ∈ Point.overOpen (curveToPlane ⁻¹ᵁ ambientChart e) :=
    (curvePoint_mem_chart_iff P hP heq (e 2)).2 hi
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero _ _ hz,
    hypersurfaceCoordinateMap_X_eq_pullRatio, ProjectiveRatioSections.basicOpen_pullRatio]
  change ((curvePoint P hP heq).underlying ∈ curveToPlane ⁻¹ᵁ ambientChart e ∧
    (curvePoint P hP heq).underlying ∈ chart (e j.castSucc)) ↔ _
  change (curvePoint P hP heq).underlying ∈ curveToPlane ⁻¹ᵁ ambientChart e at hz
  exact (and_iff_right hz).trans (curvePoint_mem_chart_iff P hP heq (e j.castSucc))

/-- The constructed point at infinity belongs to the Y chart. -/
theorem infinity_mem_chart_one : infinity.underlying ∈ chart 1 := by
  exact (curvePoint_mem_chart_iff ![0, 1, 0]
    (by intro h; have := congrFun h 1; simp at this)
    WeierstrassCurve.Projective.equation_zero 1).2 one_ne_zero

/-- Both regular affine coordinates on the Y chart evaluate to zero at infinity. -/
@[simp] theorem evaluate_curveYCoordinate_infinity (j : Fin 2) :
    Point.evaluate (chart 1)
        (hypersurfaceCoordinateMap (chartEquation (Equiv.swap (1 : Fin 3) 2))
          (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) (X j))
        infinity = 0 := by
  by_contra h
  have hn := (evaluate_curveChartCoordinate_ne_zero_iff (Equiv.swap (1 : Fin 3) 2)
    chartEquation_y_prime j ![0, 1, 0]
    (by intro h; have := congrFun h 1; simp at this)
    WeierstrassCurve.Projective.equation_zero (by simp)).1 h
  fin_cases j <;> exact hn rfl

end AlgebraicGeometry.ExplicitEllipticCandidate
