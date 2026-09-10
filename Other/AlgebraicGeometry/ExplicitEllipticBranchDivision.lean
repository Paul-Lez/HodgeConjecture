/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicSimpleZeroDivision
public import Other.AlgebraicGeometry.ExplicitEllipticCMOverlapFunctions
public import Other.AlgebraicGeometry.ExplicitEllipticCMEigenfunctionZeros
public import Other.AlgebraicGeometry.ExplicitEllipticDifferentialNowhereVanishing
public import Other.AlgebraicGeometry.ExplicitEllipticCurveConnectivity

/-!
# Division at the finite branch points of the explicit elliptic curve

This file records the analytic input for the CM pole argument.  On the affine
`Z` chart the overlap coordinate is `y = Y / Z`.  Its differential is a
nonzero multiple of the invariant differential at every zero of `y`, so all
its zeros are simple.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace MvPolynomial
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine coordinate `x = X / Z` on the `Z` chart. -/
def curveZAffineX : Γ(curve, curveZOpen) :=
  hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
    (X 0)

/-- On the `Z` chart, `dy = (3x² - 1) ω`. -/
theorem curveZOverlapCoordinate_differential :
    KaehlerDifferential.D ℂ
        Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3)))
        curveZOverlapCoordinate =
      (3 * curveZAffineX ^ 2 - 1) • curveZDifferentialCM := by
  unfold curveZDifferentialCM curveZAffineX
  have h := hypersurfaceDifferential_smul_x
    (chartEquation (Equiv.refl (Fin 3)))
    (C (1 / 4) * (18 * X 0)) zDifferentialB zDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
    zDifferential_bezout
  have hp : pderiv 0 (chartEquation (Equiv.refl (Fin 3))) =
      1 - 3 * X 0 ^ 2 := by
    simp
    ring
  rw [hp, map_sub, map_one, map_mul, map_pow, map_ofNat] at h
  rw [curveZOverlapCoordinate_eq_coordinate]
  have hn := congrArg Neg.neg h
  simp only [neg_neg] at hn
  calc
    _ = -((1 - 3 *
          (hypersurfaceCoordinateMap
            (chartEquation (Equiv.refl (Fin 3)))
            (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
            (X 0)) ^ 2) •
          hypersurfaceDifferential
            (chartEquation (Equiv.refl (Fin 3))) zDifferentialB zDifferentialC
            (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3))
              chartEquation_z_prime)) := hn.symm
    _ = _ := by module

/-- Evaluation of the affine cubic equation on the `Z` chart. -/
theorem evaluate_curveZAffine_equation
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ curveZOpen) :
    Point.evaluate curveZOpen curveZOverlapCoordinate z ^ 2 -
        Point.evaluate curveZOpen curveZAffineX z ^ 3 +
    Point.evaluate curveZOpen curveZAffineX z = 0 := by
  let ev := Point.evaluationHom (X := Over.mk curveToBase) curveZOpen ⟨z, hz⟩
  let φ := hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
  have he := congrArg
    (fun s : Γ(curve, curveZOpen) ↦ ev s)
    (hypersurfaceCoordinateMap_equation
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime))
  simp only [map_zero] at he
  change ev (φ (chartEquation (Equiv.refl (Fin 3)))) = 0 at he
  have hm := congrArg φ chartEquation_z
  rw [hm] at he
  simp only [map_add, map_sub, map_pow] at he
  rw [← Point.evaluationHom_apply (X := Over.mk curveToBase) curveZOpen
      ⟨z, hz⟩ curveZOverlapCoordinate,
    ← Point.evaluationHom_apply (X := Over.mk curveToBase) curveZOpen
      ⟨z, hz⟩ curveZAffineX]
  change ev curveZOverlapCoordinate ^ 2 - ev curveZAffineX ^ 3 +
      ev curveZAffineX = 0
  simpa only [φ, curveZAffineX, curveZOverlapCoordinate_eq_coordinate] using he

/-- At a zero of `y`, the coefficient `3x² - 1` in `dy = (3x²-1)ω`
does not vanish. -/
theorem evaluate_curveZAffine_coefficient_ne_zero_of_y_eq_zero
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    3 * Point.evaluate curveZOpen curveZAffineX z ^ 2 - 1 ≠ 0 := by
  let x := Point.evaluate curveZOpen curveZAffineX z
  have he := evaluate_curveZAffine_equation z hz
  rw [hy] at he
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at he
  have hxprod : x * (1 - x ^ 2) = 0 := by
    dsimp only [x]
    linear_combination he
  rcases mul_eq_zero.mp hxprod with hx | hx
  · simp [x, hx]
  · have hx2 : x ^ 2 = 1 := (sub_eq_zero.mp hx).symm
    norm_num [x, hx2]

/-- The Kähler differential of `y` has nonzero analytic value at every zero
of `y` on the affine `Z` chart. -/
theorem curveZOverlapCoordinate_differential_evaluation_ne_zero_of_y_eq_zero
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1) curveZOpen z
        hz
        (KaehlerDifferential.D ℂ Γ(curve, curveZOpen) curveZOverlapCoordinate) ≠ 0 := by
  have hω : regularKaehlerFormEvaluation (Over.mk curveToBase) (d := 1)
      curveZOpen z hz curveZDifferentialCM ≠ 0 := by
    rw [curveZDifferentialCM_eq_curveZDifferential]
    convert curveZDifferential_evaluation_ne_zero z
        (show z.underlying ∈ chart 2 by
          simpa only [show curveZOpen = chart 2 from rfl] using hz) using 1 <;>
      unfold regularKaehlerFormEvaluation <;> rfl
  rw [curveZOverlapCoordinate_differential,
    regularKaehlerFormEvaluation_smul]
  simpa only [Point.evaluate, dif_pos hz, map_sub, map_mul, map_pow,
    map_ofNat, map_one] using
      (smul_ne_zero
        (evaluate_curveZAffine_coefficient_ne_zero_of_y_eq_zero z hz hy)
        hω)

/-- In a local analytic coordinate at a zero of `y`, the derivative of `y`
is nonzero. Thus every finite branch zero of `y` is simple. -/
theorem curveZOverlapCoordinate_fderiv_ne_zero_of_y_eq_zero
    (z : ComplexPoint (Over.mk curveToBase)) (hz : z.underlying ∈ curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    fderiv ℂ
      (regularInLocalChart (Over.mk curveToBase) 1 curveZOpen
        curveZOverlapCoordinate z)
      (localChart (Over.mk curveToBase) 1 z z) ≠ 0 := by
  intro hD
  apply curveZOverlapCoordinate_differential_evaluation_ne_zero_of_y_eq_zero
    z hz hy
  ext v
  have hv : (fun _ : Fin 1 => v 0) = v := by
    funext i
    exact congrArg v (Fin.eq_zero i).symm
  rw [← hv]
  calc
    _ = fderiv ℂ
        (regularInLocalChart (Over.mk curveToBase) 1 curveZOpen
          curveZOverlapCoordinate z)
        (localChart (Over.mk curveToBase) 1 z z) (v 0) := by
      exact regularKaehlerFormEvaluation_D_apply
        (Over.mk curveToBase) 1 curveZOpen z hz
        (show Γ((Over.mk curveToBase).left, curveZOpen) from
          curveZOverlapCoordinate) (v 0)
    _ = 0 := by rw [hD]; rfl
    _ = (0 : (Fin 1 → ℂ) [⋀^Fin 1]→L[ℂ] ℂ) (fun _ => v 0) := rfl

/-- A holomorphic `-i` CM eigenfunction on the affine `Z` chart is globally
divisible by the odd coordinate `y`. -/
theorem exists_curveZHolomorphicCMMinusEigen_eq_overlapCoordinate_mul
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hf : curveZHolomorphicCMEnd f = -Complex.I • f) :
    ∃ q : OpenHolomorphicFunctions curveVariety 1
        (.op (regularAnalyticOpen curveVariety curveZOpen)),
      (regularToHolomorphicAlgHom curveVariety 1 curveZOpen
        curveZOverlapCoordinate) * q = f := by
  let U : (Opens (TopCat.of (ComplexPoint curveVariety)))ᵒᵖ :=
    .op (regularAnalyticOpen curveVariety curveZOpen)
  let g : OpenHolomorphicFunctions curveVariety 1 U :=
    regularToHolomorphicAlgHom curveVariety 1 curveZOpen
      curveZOverlapCoordinate
  have hvanish : ∀ (z : ComplexPoint curveVariety)
      (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 → f.1 ⟨z, hz⟩ = 0 := by
    intro z hz hg
    apply curveZHolomorphicCMMinusEigen_evaluate_zero_of_overlapCoordinate_eq_zero
      f hf z hz
    exact hg
  have hsimple : ∀ (z : ComplexPoint curveVariety)
      (hz : z ∈ Opposite.unop U),
      g.1 ⟨z, hz⟩ = 0 →
        fderiv ℂ (chartSection curveVariety 1 U z g)
          (localChart curveVariety 1 z z) ≠ 0 := by
    intro z hz hg
    have hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0 := hg
    have hreg := curveZOverlapCoordinate_fderiv_ne_zero_of_y_eq_zero
      z hz hy
    have hc := localChart_center_mem_regularChartSectionDomain
      curveVariety 1 curveZOpen z hz
    have hcompare := chartSectionDifferential_regularToHolomorphic
      curveVariety 1 curveZOpen curveZOverlapCoordinate z hc
    rw [chartSectionDifferential,
      fderivWithin_of_isOpen
        (isOpen_chartSectionDomain curveVariety 1 U z) hc] at hcompare
    rw [hcompare]
    exact hreg
  exact exists_holomorphic_quotient_of_vanishes_on_simple_zeros
    curveVariety U f g hvanish hsimple

end AlgebraicGeometry.ExplicitEllipticCandidate
