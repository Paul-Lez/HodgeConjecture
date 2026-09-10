/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.DeRham.Logarithmic
public import Other.Algebra.DeRham.Kaehler
public import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
public import Other.AlgebraicGeometry.ExplicitEllipticCotangentTrivialization
public import Other.AlgebraicGeometry.ExplicitEllipticInfinityCoordinates
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechProduct

/-!
# An explicit Čech representative on the elliptic curve

On the intersection of the standard `Z ≠ 0` and `Y ≠ 0` charts, the regular
function `x² / y = x²v` is the usual representative of structure-sheaf
cohomology of a plane cubic. This file constructs that function in the actual
analytic structure sheaf and records a residue-friendly representative of the
same Čech class. The latter multiplied by the invariant differential is
exactly `-dlog (X/Y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem curveCMOverlap_eq :
    curveCMOverlap = curveZOpen ⊓ curveYOpen := by
  exact curveZOverlapCoordinate_basicOpen

theorem regularAnalyticOpen_curveCMOverlap :
    regularAnalyticOpen curveVariety curveCMOverlap = curveCechOverlap := by
  rw [curveCMOverlap_eq]
  rfl

/-- The standard algebraic Cech representative `x²/y = x²v` on the overlap. -/
def curveCechRegularRepresentative : Γ(curve, curveCMOverlap) :=
  curveCMOverlapZX ^ 2 * curveCMOverlapYV

theorem curveCechRegularRepresentative_cm :
    curveYCMOverlapRingEnd curveCechRegularRepresentative =
      -(Complex.I • curveCechRegularRepresentative) := by
  simp only [curveCechRegularRepresentative, map_mul, map_pow,
    curveYCMOverlapRingEnd_ZX, curveYCMOverlapRingEnd_YV]
  simp [Algebra.smul_def]
  ring

theorem overlapPoint_mem_curveCMOverlap :
    overlapPoint.underlying ∈ curveCMOverlap := by
  rw [curveCMOverlap_eq]
  constructor
  · exact (curvePoint_mem_chart_iff _ _ _ 2).2 one_ne_zero
  · apply (curvePoint_mem_chart_iff _ _ _ 1).2
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem overlapPoint_mem_overOpen_curveCMOverlap :
    overlapPoint ∈ Point.overOpen curveCMOverlap := by
  exact overlapPoint_mem_curveCMOverlap

theorem evaluate_curveCMOverlapZX_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap curveCMOverlapZX overlapPoint ≠ 0 := by
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    curveCMOverlapZX overlapPoint
      overlapPoint_mem_overOpen_curveCMOverlap]
  rw [curveCMOverlapZX, curveSectionRestriction_coordinate,
    ProjectiveRatioSections.basicOpen_pullRatio]
  exact ⟨overlapPoint_mem_curveCMOverlap,
    (curvePoint_mem_chart_iff _ _ _ 0).2 Complex.I_ne_zero⟩

theorem evaluate_curveCMOverlapYV_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap curveCMOverlapYV overlapPoint ≠ 0 := by
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero
    curveCMOverlapYV overlapPoint
      overlapPoint_mem_overOpen_curveCMOverlap]
  rw [curveCMOverlapYV, curveSectionRestriction_coordinate,
    ProjectiveRatioSections.basicOpen_pullRatio]
  exact ⟨overlapPoint_mem_curveCMOverlap,
    (curvePoint_mem_chart_iff _ _ _ 2).2 one_ne_zero⟩

theorem curveCechRegularRepresentative_ne_zero :
    curveCechRegularRepresentative ≠ 0 := by
  intro h
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩
  have he := congrArg
    (fun s : Γ(curve, curveCMOverlap) => ev s) h
  change ev (curveCMOverlapZX ^ 2 * curveCMOverlapYV) = ev 0 at he
  simp only [map_mul, map_pow, map_zero] at he
  have hx : ev curveCMOverlapZX ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapZX ≠ 0
    rw [Point.evaluationHom_apply]
    exact evaluate_curveCMOverlapZX_overlapPoint_ne_zero
  have hv : ev curveCMOverlapYV ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapYV ≠ 0
    rw [Point.evaluationHom_apply]
    exact evaluate_curveCMOverlapYV_overlapPoint_ne_zero
  exact mul_ne_zero (pow_ne_zero 2 hx) hv he

theorem evaluate_curveCechRegularRepresentative_overlapPoint_ne_zero :
    Point.evaluate curveCMOverlap curveCechRegularRepresentative overlapPoint ≠ 0 := by
  let ev := Point.evaluationHom (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩
  have hx : ev curveCMOverlapZX ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapZX ≠ 0
    rw [Point.evaluationHom_apply]
    exact evaluate_curveCMOverlapZX_overlapPoint_ne_zero
  have hv : ev curveCMOverlapYV ≠ 0 := by
    change (ConcreteCategory.hom (Point.evaluationHom curveCMOverlap
      ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩))
        curveCMOverlapYV ≠ 0
    rw [Point.evaluationHom_apply]
    exact evaluate_curveCMOverlapYV_overlapPoint_ne_zero
  rw [← Point.evaluationHom_apply (X := curveVariety) curveCMOverlap
    ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩
    curveCechRegularRepresentative]
  change ev curveCechRegularRepresentative ≠ 0
  change ev (curveCMOverlapZX ^ 2 * curveCMOverlapYV) ≠ 0
  rw [map_mul, map_pow]
  exact mul_ne_zero (pow_ne_zero 2 hx) hv

/-- The regular representative as a holomorphic function before identifying overlap opens. -/
def curveCMOverlapHolomorphicRepresentative :
    OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveCMOverlap)) :=
  regularToHolomorphicAlgHom curveVariety 1 curveCMOverlap
    curveCechRegularRepresentative

theorem curveCMOverlapHolomorphicRepresentative_ne_zero :
    curveCMOverlapHolomorphicRepresentative ≠ 0 := by
  intro h
  have he := congrArg (fun f => f.1
    ⟨overlapPoint, overlapPoint_mem_overOpen_curveCMOverlap⟩) h
  change Point.evaluate curveCMOverlap curveCechRegularRepresentative overlapPoint = 0 at he
  exact evaluate_curveCechRegularRepresentative_overlapPoint_ne_zero he

/-- Transport holomorphic functions across an equality of analytic opens. -/
def openHolomorphicFunctionAddEquivOfEq
    {U V : Opens (TopCat.of (ComplexPoint curveVariety))} (h : U = V) :
    OpenHolomorphicFunctions curveVariety 1 (.op U) ≃+
      OpenHolomorphicFunctions curveVariety 1 (.op V) :=
  AddEquiv.cast (congrArg Opposite.op h)

@[simp] theorem openHolomorphicFunctionAddEquivOfEq_apply
    {U V : Opens (TopCat.of (ComplexPoint curveVariety))} (h : U = V)
    (f : OpenHolomorphicFunctions curveVariety 1 (.op U)) (z : V) :
    (openHolomorphicFunctionAddEquivOfEq h f).1 z =
      f.1 ⟨z.1, by simpa only [h] using z.2⟩ := by
  subst V
  rfl

/-- Transport holomorphic functions across the equality of the two descriptions of the overlap. -/
def curveCechOpenFunctionAddEquiv :
    OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveCMOverlap)) ≃+
      OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) :=
  openHolomorphicFunctionAddEquivOfEq regularAnalyticOpen_curveCMOverlap

/-- The actual holomorphic overlap function obtained from `x²/y`. -/
def curveCechRepresentative :
    OpenHolomorphicFunctions curveVariety 1 (.op curveCechOverlap) := by
  exact curveCechOpenFunctionAddEquiv
    curveCMOverlapHolomorphicRepresentative

theorem curveCechRepresentative_ne_zero :
    curveCechRepresentative ≠ 0 := by
  intro h
  apply curveCMOverlapHolomorphicRepresentative_ne_zero
  apply curveCechOpenFunctionAddEquiv.injective
  change curveCechOpenFunctionAddEquiv
      curveCMOverlapHolomorphicRepresentative = 0 at h
  exact h.trans curveCechOpenFunctionAddEquiv.map_zero.symm

/-! ### A logarithmic representative of the same Čech class -/

theorem curveCMOverlap_y_equation :
    curveCMOverlapYV - curveCMOverlapYU ^ 3 +
        curveCMOverlapYU * curveCMOverlapYV ^ 2 = 0 := by
  have h := congrArg (curveSectionRestriction curveCMOverlap_le_y)
    (hypersurfaceCoordinateMap_equation
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime))
  simpa only [chartEquation_y, map_add, map_sub, map_pow, map_mul, map_zero,
    curveCMOverlapYU, curveCMOverlapYV] using h

theorem curveCMOverlapYU_mul_candidate_inverse :
    curveCMOverlapYU *
        (curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) = 1 := by
  have heq : curveCMOverlapYU ^ 3 =
      curveCMOverlapYV + curveCMOverlapYU * curveCMOverlapYV ^ 2 := by
    have h := curveCMOverlap_y_equation
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
def curveCMOverlapYUUnit : Γ(curve, curveCMOverlap)ˣ where
  val := curveCMOverlapYU
  inv := curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV
  val_inv := curveCMOverlapYU_mul_candidate_inverse
  inv_val := by
    rw [mul_comm]
    exact curveCMOverlapYU_mul_candidate_inverse

@[simp] theorem curveCMOverlapYUUnit_val :
    (curveCMOverlapYUUnit : Γ(curve, curveCMOverlap)) = curveCMOverlapYU :=
  rfl

@[simp] theorem curveCMOverlapYUUnit_inv_val :
    (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) =
      curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV :=
  rfl

theorem curveCMOverlapZX_eq_YU_mul_ZY :
    curveCMOverlapZX = curveCMOverlapYU * curveCMOverlapZY := by
  calc
    curveCMOverlapZX = curveCMOverlapZX * 1 := (mul_one _).symm
    _ = curveCMOverlapZX * (curveCMOverlapYV * curveCMOverlapZY) := by
      rw [show curveCMOverlapYV * curveCMOverlapZY = 1 by
        rw [mul_comm, curveCMOverlap_y_mul_v]]
    _ = (curveCMOverlapZX * curveCMOverlapYV) * curveCMOverlapZY := by ring
    _ = curveCMOverlapYU * curveCMOverlapZY := by rw [curveCMOverlap_x_mul_v]

/-- The residue-adjusted regular Čech representative `(x²+1)/y`. -/
def curveCechAdjustedRegularRepresentative : Γ(curve, curveCMOverlap) :=
  curveCechRegularRepresentative + curveCMOverlapYV

/-- The adjusted representative differs from `x²/y` by the restriction of the
regular Y-chart coordinate `Z/Y`, so it defines the same two-open Čech class. -/
theorem curveCechAdjustedRegularRepresentative_eq_add_y_restriction :
    curveCechAdjustedRegularRepresentative =
      curveCechRegularRepresentative +
        curveSectionRestriction curveCMOverlap_le_y
          (hypersurfaceCoordinateMap
            (chartEquation (Equiv.swap (1 : Fin 3) 2))
            (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
              chartEquation_y_prime) (X 1)) := by
  rfl

theorem curveCechAdjustedRegularRepresentative_eq :
    curveCechAdjustedRegularRepresentative =
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
        2 * curveCMOverlapYV := by
  have hv : curveCMOverlapYV * curveCMOverlapZY = 1 := by
    rw [mul_comm, curveCMOverlap_y_mul_v]
  rw [curveCechAdjustedRegularRepresentative, curveCechRegularRepresentative,
    curveCMOverlapZX_eq_YU_mul_ZY, curveCMOverlapYUUnit_inv_val]
  calc
    (curveCMOverlapYU * curveCMOverlapZY) ^ 2 * curveCMOverlapYV +
        curveCMOverlapYV =
      curveCMOverlapYU ^ 2 * curveCMOverlapZY *
          (curveCMOverlapYV * curveCMOverlapZY) + curveCMOverlapYV := by ring
    _ = curveCMOverlapYU ^ 2 * curveCMOverlapZY + curveCMOverlapYV := by rw [hv]; ring
    _ = curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV +
        2 * curveCMOverlapYV := by ring

theorem curveCMOverlap_curveYDifferential_smul :
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

theorem curveCechAdjustedRegularRepresentative_smul_differential :
    curveCechAdjustedRegularRepresentative •
        curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential =
      -(↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU := by
  rw [curveCechAdjustedRegularRepresentative_eq]
  have hu :
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          curveCMOverlapYU = 1 := by
    exact Units.inv_mul curveCMOverlapYUUnit
  have hcoeff :
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          (1 + 2 * curveCMOverlapYU * curveCMOverlapYV) =
        (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
          2 * curveCMOverlapYV := by
    rw [mul_add, mul_one]
    congr 1
    calc
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          (2 * curveCMOverlapYU * curveCMOverlapYV) =
        2 * ((↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) *
          curveCMOverlapYU) * curveCMOverlapYV := by ring
      _ = 2 * curveCMOverlapYV := by rw [hu, mul_one]
  calc
    ((↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) +
        2 * curveCMOverlapYV) •
        curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential =
      (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        ((1 + 2 * curveCMOverlapYU * curveCMOverlapYV) •
          curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential) := by
      rw [smul_smul, hcoeff]
    _ = (↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        (-KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU) := by
      rw [curveCMOverlap_curveYDifferential_smul]
    _ = -(↑(curveCMOverlapYUUnit⁻¹) : Γ(curve, curveCMOverlap)) •
        KaehlerDifferential.D ℂ Γ(curve, curveCMOverlap) curveCMOverlapYU := by
      rw [smul_neg, neg_smul]

/-- Multiplying the adjusted Čech representative by the invariant differential
is exactly the negative logarithmic differential of the overlap unit `X/Y`. -/
theorem curveCechAdjustedRegularRepresentative_form_eq_neg_dlog :
    Algebra.DeRham.kaehlerToForm ℂ Γ(curve, curveCMOverlap)
        (curveCechAdjustedRegularRepresentative •
          curveDifferentialRestriction curveCMOverlap_le_y curveYDifferential) =
      -Algebra.DeRham.dlog ℂ Γ(curve, curveCMOverlap)
        curveCMOverlapYUUnit := by
  rw [curveCechAdjustedRegularRepresentative_smul_differential,
    Algebra.DeRham.kaehlerToForm_smul_D]
  simp only [Algebra.DeRham.dlog, Algebra.DeRham.logarithmicForm,
    Fin.prod_univ_one, curveCMOverlapYUUnit_inv_val,
    curveCMOverlapYUUnit_val]
  rw [show -(curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) =
      (-1 : ℂ) •
        (curveCMOverlapYU ^ 2 * curveCMOverlapZY - curveCMOverlapYV) by simp]
  rw [Algebra.DeRham.mk_coeff_smul]
  simp

end AlgebraicGeometry.ExplicitEllipticCandidate
