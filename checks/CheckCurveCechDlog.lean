import Other.Algebra.DeRham.Logarithmic
import Other.Algebra.DeRham.Kaehler
import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
import Other.AlgebraicGeometry.ExplicitEllipticCotangentTrivialization

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem check_curveCMOverlap_y_equation :
    curveCMOverlapYV - curveCMOverlapYU ^ 3 +
        curveCMOverlapYU * curveCMOverlapYV ^ 2 = 0 := by
  have h := congrArg (curveSectionRestriction curveCMOverlap_le_y)
    (hypersurfaceCoordinateMap_equation
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime))
  simpa only [chartEquation_y, map_add, map_sub, map_pow, map_mul, map_zero,
    curveCMOverlapYU, curveCMOverlapYV] using h

theorem check_curveCMOverlapYU_mul_candidate_inverse :
    curveCMOverlapYU *
        (curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) = 1 := by
  have heq : curveCMOverlapYU ^ 3 =
      curveCMOverlapYV + curveCMOverlapYU * curveCMOverlapYV ^ 2 := by
    have h := check_curveCMOverlap_y_equation
    linear_combination -h
  have hv : curveCMOverlapYV * curveCMOverlapZY = 1 := by
    rw [mul_comm, curveCMOverlap_y_mul_v]
  calc
    curveCMOverlapYU *
        (curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) =
      curveCMOverlapYU ^ 3 * curveCMOverlapZY -
        curveCMOverlapYU * curveCMOverlapYV := by ring
    _ = (curveCMOverlapYV + curveCMOverlapYU * curveCMOverlapYV ^ 2) *
        curveCMOverlapZY - curveCMOverlapYU * curveCMOverlapYV := by rw [heq]
    _ = curveCMOverlapYV * curveCMOverlapZY +
        curveCMOverlapYU * curveCMOverlapYV *
          (curveCMOverlapYV * curveCMOverlapZY) -
        curveCMOverlapYU * curveCMOverlapYV := by ring
    _ = 1 := by rw [hv]; ring

/-- The overlap coordinate `X/Y` as an actual unit of the overlap section ring. -/
def check_curveCMOverlapYUUnit : Γ(curve, curveCMOverlap)ˣ where
  val := curveCMOverlapYU
  inv := curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV
  val_inv := check_curveCMOverlapYU_mul_candidate_inverse
  inv_val := by
    rw [mul_comm]
    exact check_curveCMOverlapYU_mul_candidate_inverse

@[simp] theorem check_curveCMOverlapYUUnit_val :
    (check_curveCMOverlapYUUnit : Γ(curve, curveCMOverlap)) = curveCMOverlapYU :=
  rfl

@[simp] theorem check_curveCMOverlapYUUnit_inv_val :
    (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) =
      curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV :=
  rfl

theorem check_curveCMOverlapZX_eq_YU_mul_ZY :
    curveCMOverlapZX = curveCMOverlapYU * curveCMOverlapZY := by
  calc
    curveCMOverlapZX = curveCMOverlapZX * 1 := (mul_one _).symm
    _ = curveCMOverlapZX * (curveCMOverlapYV * curveCMOverlapZY) := by
      rw [show curveCMOverlapYV * curveCMOverlapZY = 1 by
        rw [mul_comm, curveCMOverlap_y_mul_v]]
    _ = (curveCMOverlapZX * curveCMOverlapYV) * curveCMOverlapZY := by ring
    _ = curveCMOverlapYU * curveCMOverlapZY := by rw [curveCMOverlap_x_mul_v]

/-- The residue-adjusted regular Čech representative `(x²+1)/y`. -/
def check_curveCechAdjustedRegularRepresentative : Γ(curve, curveCMOverlap) :=
  curveCMOverlapZX ^ 2 * curveCMOverlapYV + curveCMOverlapYV

theorem check_curveCechAdjustedRegularRepresentative_eq :
    check_curveCechAdjustedRegularRepresentative =
      (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
        2 * curveCMOverlapYV := by
  have hv : curveCMOverlapYV * curveCMOverlapZY = 1 := by
    rw [mul_comm, curveCMOverlap_y_mul_v]
  rw [check_curveCechAdjustedRegularRepresentative,
    check_curveCMOverlapZX_eq_YU_mul_ZY,
    check_curveCMOverlapYUUnit_inv_val]
  calc
    (curveCMOverlapYU * curveCMOverlapZY) ^ 2 * curveCMOverlapYV +
        curveCMOverlapYV =
      curveCMOverlapYU ^ 2 * curveCMOverlapZY *
          (curveCMOverlapYV * curveCMOverlapZY) + curveCMOverlapYV := by ring
    _ = curveCMOverlapYU ^ 2 * curveCMOverlapZY + curveCMOverlapYV := by rw [hv]; ring
    _ = curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV +
        2 * curveCMOverlapYV := by ring

theorem check_curveCMOverlap_curveYDifferential_smul :
    (1 + 2 * curveCMOverlapYU * curveCMOverlapYV) •
        curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential =
      -KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU := by
  have hp : pderiv 1 (chartEquation (Equiv.swap (1 : Fin 3) 2)) =
      1 + 2 * X 0 * X 1 := by simp; ring
  have hb := hypersurfaceDifferential_smul_y
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (2 * X 1 ^ 3) yDifferentialB yDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime) yDifferential_bezout
  rw [hp, map_add, map_one, map_mul, map_mul, map_ofNat] at hb
  have h := congrArg (curveDifferentialRestriction
    (show curveCMOverlap ≤ curveToPlane ⁻¹ᵁ
      ambientChart (Equiv.swap (1 : Fin 3) 2) from curveCMOverlap_le_y)) hb
  simp only [curveDifferentialRestriction_smul,
    curveDifferentialRestriction_D, map_add, map_one, map_mul, map_ofNat] at h
  have hn := congrArg Neg.neg h
  rw [← smul_neg] at hn
  simpa only [curveYDifferential, map_neg, neg_neg,
    curveCMOverlapYU, curveCMOverlapYV] using hn

theorem check_curveCechAdjustedRegularRepresentative_smul_differential :
    check_curveCechAdjustedRegularRepresentative •
        curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential =
      -(↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU := by
  rw [check_curveCechAdjustedRegularRepresentative_eq]
  have hu :
      (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          curveCMOverlapYU = 1 := by
    exact Units.inv_mul check_curveCMOverlapYUUnit
  have hcoeff :
      (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          (1 + 2 * curveCMOverlapYU * curveCMOverlapYV) =
        (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
          2 * curveCMOverlapYV := by
    rw [mul_add, mul_one]
    congr 1
    calc
      (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          (2 * curveCMOverlapYU * curveCMOverlapYV) =
        2 * ((↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          curveCMOverlapYU) * curveCMOverlapYV := by ring
      _ = 2 * curveCMOverlapYV := by rw [hu, mul_one]
  calc
    ((↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
        2 * curveCMOverlapYV) •
        curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential =
      (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        ((1 + 2 * curveCMOverlapYU * curveCMOverlapYV) •
          curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential) := by
      rw [smul_smul, hcoeff]
    _ = (↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        (-KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU) := by
      rw [check_curveCMOverlap_curveYDifferential_smul]
    _ = -(↑(check_curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU := by
      rw [smul_neg, neg_smul]

theorem check_curveCechAdjustedRegularRepresentative_form_eq_neg_dlog :
    Algebra.DeRham.kaehlerToForm ℂ Γ(curve, curveCMOverlap)
        (check_curveCechAdjustedRegularRepresentative •
          curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential) =
      -Algebra.DeRham.dlog ℂ Γ(curve, curveCMOverlap)
        check_curveCMOverlapYUUnit := by
  rw [check_curveCechAdjustedRegularRepresentative_smul_differential,
    Algebra.DeRham.kaehlerToForm_smul_D]
  simp only [Algebra.DeRham.dlog, Algebra.DeRham.logarithmicForm,
    Fin.prod_univ_one, check_curveCMOverlapYUUnit_inv_val,
    check_curveCMOverlapYUUnit_val]
  rw [show -(curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) =
      (-1 : ℂ) •
        (curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) by simp]
  rw [Algebra.DeRham.mk_coeff_smul]
  simp

end
end AlgebraicGeometry.ExplicitEllipticCandidate
