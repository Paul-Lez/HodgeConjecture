/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCoordinateRing
public import Other.AlgebraicGeometry.RegularDerivativeRank

import all Mathlib.Data.Complex.Basic

/-!
# Analytic rank of the product differential at infinity

The actual four generators of the Y-by-Y section ring detect every tangent direction.
Differentiating both actual cubic equations at `(∞,∞)` kills the two `dv` derivatives,
so the remaining two `du` derivatives have nonzero wedge.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

local instance (priority := 10000) surfaceDerivativeComplexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup
local instance (priority := 10000) surfaceDerivativeComplexModule : Module ℂ ℂ :=
  (inferInstance : NormedSpace ℂ ℂ).toModule
local instance (priority := 10000) surfaceDerivativePiAddCommGroup : AddCommGroup (Fin 2 → ℂ) :=
  (inferInstance : NormedAddCommGroup (Fin 2 → ℂ)).toAddCommGroup
local instance (priority := 10000) surfaceDerivativePiModule : Module ℂ (Fin 2 → ℂ) :=
  (inferInstance : NormedSpace ℂ (Fin 2 → ℂ)).toModule
local instance (priority := 10000) surfaceDerivativePiTopology : TopologicalSpace (Fin 2 → ℂ) :=
  (inferInstance : PseudoMetricSpace (Fin 2 → ℂ)).toUniformSpace.toTopologicalSpace

local instance surfaceNonvanishingSectionAlgebra (V : surface.Opens) : Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

/-- The actual Y-coordinate ring map on either factor of the product. -/
def surfaceYChartCoordinateMap (i : Fin 2) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Γ(surface, surfaceDifferentialOpen (1, 1)) :=
  ![surfaceYCoordinateMapLeft, surfaceYCoordinateMapRight] i

@[simp] theorem surfaceYChartCoordinateMap_X (i j : Fin 2) :
    surfaceYChartCoordinateMap i (MvPolynomial.X j) = surfaceYCoordinate i j := by
  fin_cases i <;> rfl

@[simp] theorem evaluate_surfaceYDifferentialB_infinity (i : Fin 2) :
    Point.evaluate (surfaceDifferentialOpen (1, 1))
      (surfaceYChartCoordinateMap i yDifferentialB) surfaceInfinity = 0 := by
  let e := (Point.evaluationHom (X := Over.mk surfaceToBase)
    (surfaceDifferentialOpen (1, 1)) ⟨surfaceInfinity, surfaceInfinity_mem_differentialOpen⟩).hom
  have he (s) : e s = Point.evaluate (surfaceDifferentialOpen (1, 1)) s surfaceInfinity :=
    Point.evaluationHom_hom_apply _ ⟨surfaceInfinity, surfaceInfinity_mem_differentialOpen⟩ s
  rw [← he]
  simp only [yDifferentialB, map_neg, map_pow, surfaceYChartCoordinateMap_X]
  have h : e (surfaceYCoordinate i 1) = 0 :=
    (he _).trans (evaluate_surfaceYCoordinate_infinity i 1)
  rw [h]
  ring

@[simp] theorem evaluate_surfaceYDifferentialC_infinity (i : Fin 2) :
    Point.evaluate (surfaceDifferentialOpen (1, 1))
      (surfaceYChartCoordinateMap i yDifferentialC) surfaceInfinity = 1 := by
  let e := (Point.evaluationHom (X := Over.mk surfaceToBase)
    (surfaceDifferentialOpen (1, 1)) ⟨surfaceInfinity, surfaceInfinity_mem_differentialOpen⟩).hom
  have he (s) : e s = Point.evaluate (surfaceDifferentialOpen (1, 1)) s surfaceInfinity :=
    Point.evaluationHom_hom_apply _ ⟨surfaceInfinity, surfaceInfinity_mem_differentialOpen⟩ s
  rw [← he]
  simp only [yDifferentialC, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one,
    surfaceYChartCoordinateMap_X]
  have hu : e (surfaceYCoordinate i 0) = 0 :=
    (he _).trans (evaluate_surfaceYCoordinate_infinity i 0)
  have hv : e (surfaceYCoordinate i 1) = 0 :=
    (he _).trans (evaluate_surfaceYCoordinate_infinity i 1)
  rw [hu, hv]
  ring

/-- The four genuine regular product coordinates expressed in the actual analytic chart. -/
def surfaceYCoordinateInLocalChart (i j : Fin 2) : (Fin 2 → ℂ) → ℂ :=
  regularInLocalChart (Over.mk surfaceToBase) 2 (surfaceDifferentialOpen (1, 1))
    (surfaceYCoordinate i j) surfaceInfinity

/-- The center of the canonical analytic chart at the product point at infinity. -/
def surfaceInfinityChartCenter : Fin 2 → ℂ :=
  localChart (Over.mk surfaceToBase) 2 surfaceInfinity surfaceInfinity

@[simp] theorem surfaceYCoordinateInLocalChart_center (i j : Fin 2) :
    surfaceYCoordinateInLocalChart i j surfaceInfinityChartCenter = 0 := by
  change Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i j)
    ((localChart (Over.mk surfaceToBase) 2 surfaceInfinity).symm
      (localChart (Over.mk surfaceToBase) 2 surfaceInfinity surfaceInfinity)) = 0
  rw [(localChart (Over.mk surfaceToBase) 2 surfaceInfinity).left_inv
    (mem_localChart_source (Over.mk surfaceToBase) 2 surfaceInfinity)]
  exact evaluate_surfaceYCoordinate_infinity i j

theorem analyticAt_surfaceYCoordinateInLocalChart (i j : Fin 2) :
    AnalyticAt ℂ (surfaceYCoordinateInLocalChart i j) surfaceInfinityChartCenter :=
  analyticAt_regularInLocalChart (Over.mk surfaceToBase) 2 (surfaceDifferentialOpen (1, 1))
    _ surfaceInfinity surfaceInfinity_mem_differentialOpen

/-- Each factor's actual cubic equation holds in the product section ring. -/
theorem surfaceYCoordinate_equation (i : Fin 2) :
    surfaceYCoordinate i 1 - surfaceYCoordinate i 0 ^ 3 +
      surfaceYCoordinate i 0 * surfaceYCoordinate i 1 ^ 2 = 0 := by
  have he := hypersurfaceCoordinateMap_equation
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
  fin_cases i
  · have h := congrArg (surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
      (chart 1) (surfaceDifferentialOpen (1, 1)) inf_le_left) he
    simp only [chartEquation_y, map_add, map_sub, map_mul, map_pow, map_zero] at h
    exact h
  · have h := congrArg (surfaceSectionPullback (pullback.snd curveToBase curveToBase)
      pullback.condition.symm (chart 1) (surfaceDifferentialOpen (1, 1)) inf_le_right) he
    simp only [chartEquation_y, map_add, map_sub, map_mul, map_pow, map_zero] at h
    exact h

theorem surfaceYCoordinateInLocalChart_equation (i : Fin 2) :
    (fun w => surfaceYCoordinateInLocalChart i 1 w - surfaceYCoordinateInLocalChart i 0 w ^ 3 +
      surfaceYCoordinateInLocalChart i 0 w * surfaceYCoordinateInLocalChart i 1 w ^ 2) = 0 := by
  funext w
  let z := (localChart (Over.mk surfaceToBase) 2 surfaceInfinity).symm w
  have hv := congrArg (fun s => Point.evaluate (surfaceDifferentialOpen (1, 1)) s z)
    (surfaceYCoordinate_equation i)
  change Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i 1) z -
      Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i 0) z ^ 3 +
    Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i 0) z *
      Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i 1) z ^ 2 = 0
  by_cases hz : z.underlying ∈ surfaceDifferentialOpen (1, 1)
  · simpa only [Point.evaluate, dif_pos hz, map_add, map_sub, map_mul, map_pow, map_zero] using hv
  · simp only [Point.evaluate, dif_neg hz, zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 2 ≠ 0), sub_zero, zero_mul, add_zero]

/-- At the product point, each `dv` vanishes by the actual cubic relation. -/
theorem fderiv_surfaceYCoordinateInLocalChart_one (i : Fin 2) :
    fderiv ℂ (surfaceYCoordinateInLocalChart i 1) surfaceInfinityChartCenter = 0 := by
  have hu := (analyticAt_surfaceYCoordinateInLocalChart i 0).differentiableAt.hasFDerivAt
  have hv := (analyticAt_surfaceYCoordinateInLocalChart i 1).differentiableAt.hasFDerivAt
  have heq := (hv.sub (hu.pow 3)).add (hu.mul (hv.pow 2))
  have hfun : ((surfaceYCoordinateInLocalChart i 1 - fun x => surfaceYCoordinateInLocalChart i 0 x ^ 3) +
      surfaceYCoordinateInLocalChart i 0 * fun x => surfaceYCoordinateInLocalChart i 1 x ^ 2) =
        (fun _ => 0) := surfaceYCoordinateInLocalChart_equation i
  rw [hfun] at heq
  have h := heq.unique (hasFDerivAt_const 0 surfaceInfinityChartCenter)
  ext w
  have hw := congrArg (fun L => L w) h
  simpa [smul_apply, smul_eq_mul] using hw

/-- The two `du` derivatives detect every tangent direction at `(∞,∞)`. -/
theorem surface_u_derivatives_separate_tangent (v : Fin 2 → ℂ)
    (hv : ∀ i : Fin 2, fderiv ℂ (surfaceYCoordinateInLocalChart i 0)
      surfaceInfinityChartCenter v = 0) : v = 0 := by
  apply generator_fderiv_separates_tangent (Over.mk surfaceToBase) 2
    (surfaceDifferentialOpen (1, 1)) surfaceYChart_isAffineOpen surfaceInfinity
    surfaceInfinity_mem_differentialOpen surfaceYPolynomialMap surfaceYPolynomialMap_surjective v
  intro ij
  erw [surfaceYPolynomialMap_X]
  change fderiv ℂ (surfaceYCoordinateInLocalChart ij.1 ij.2) surfaceInfinityChartCenter v = 0
  rcases ij with ⟨i, j⟩
  fin_cases j
  · exact hv i
  · exact congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ => L v)
      (fderiv_surfaceYCoordinateInLocalChart_one i)

/-- The actual analytic wedge `du₁ ∧ du₂` is nonzero at the product point. -/
theorem surface_u_derivatives_wedge_ne_zero :
    wedgeCovectors (Fin 2 → ℂ) 2
      (fun i => fderiv ℂ (surfaceYCoordinateInLocalChart i 0) surfaceInfinityChartCenter) ≠ 0 :=
  wedgeCovectors_two_ne_zero_of_separates _ surface_u_derivatives_separate_tangent

end AlgebraicGeometry.ExplicitEllipticCandidate
