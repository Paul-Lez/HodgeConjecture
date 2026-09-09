/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceInfinity
public import Other.AlgebraicGeometry.ExplicitEllipticAnalyticNonvanishing
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceNonvanishing
public import Other.AlgebraicGeometry.RegularHolomorphicFormEvaluation

/-!
# Analytic evaluation of the actual elliptic surface form

The regular Kähler wedge on the product chart is evaluated through the actual
regular-to-holomorphic comparison. Its value at infinity is the wedge of the two
leading coordinate derivatives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] regularSectionAlgebra

local instance surfaceFormEvaluationSectionAlgebra (V : surface.Opens) :
    Algebra ℂ Γ(surface, V) := regularSectionAlgebra (Over.mk surfaceToBase) V

/-- The actual pullback of the invariant Y-chart differential has its expected weighted
Kähler expression on every smaller product open. -/
theorem surfacePulledCurveDifferential_y
    (f : surface ⟶ curve) (hbase : f ≫ curveToBase = surfaceToBase)
    (V : surface.Opens) (h : V ≤ f ⁻¹ᵁ chart 1) :
    surfacePulledCurveDifferential f hbase 1 V h =
      -((surfaceSectionPullback f hbase (chart 1) V h
          (curveYCoordinateMap yDifferentialC)) • KaehlerDifferential.D ℂ Γ(surface, V)
            (surfaceSectionPullback f hbase (chart 1) V h
              (curveYCoordinateMap (MvPolynomial.X 0))) -
        (surfaceSectionPullback f hbase (chart 1) V h
          (curveYCoordinateMap yDifferentialB)) • KaehlerDifferential.D ℂ Γ(surface, V)
            (surfaceSectionPullback f hbase (chart 1) V h
              (curveYCoordinateMap (MvPolynomial.X 1)))) := by
  change surfaceDifferentialPullback f hbase (chart 1) V h
    (-(curveYCoordinateMap yDifferentialC • KaehlerDifferential.D ℂ Γ(curve, chart 1)
        (curveYCoordinateMap (MvPolynomial.X 0)) -
      curveYCoordinateMap yDifferentialB • KaehlerDifferential.D ℂ Γ(curve, chart 1)
        (curveYCoordinateMap (MvPolynomial.X 1)))) = _
  rw [map_neg, map_sub, surfaceDifferentialPullback_smul_D,
    surfaceDifferentialPullback_smul_D]

/-- The actual algebraic two-form on the Y-by-Y chart is the wedge of the two normalized
weighted coordinate expressions. -/
theorem surfaceLocalTwoFormOn_y_y :
    surfaceLocalTwoFormOn (1, 1) (surfaceDifferentialOpen (1, 1)) le_rfl =
      Algebra.DeRham.kaehlerWedge ℂ Γ(surface, surfaceDifferentialOpen (1, 1))
        (-(surfaceYChartCoordinateMap 0 yDifferentialC •
              KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen (1, 1))
                (surfaceYCoordinate 0 0) -
          surfaceYChartCoordinateMap 0 yDifferentialB •
              KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen (1, 1))
                (surfaceYCoordinate 0 1)))
        (-(surfaceYChartCoordinateMap 1 yDifferentialC •
              KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen (1, 1))
                (surfaceYCoordinate 1 0) -
          surfaceYChartCoordinateMap 1 yDifferentialB •
              KaehlerDifferential.D ℂ Γ(surface, surfaceDifferentialOpen (1, 1))
                (surfaceYCoordinate 1 1))) := by
  unfold surfaceLocalTwoFormOn
  rw [surfacePulledCurveDifferential_y, surfacePulledCurveDifferential_y]
  rfl

/-- The value of the actual local holomorphic two-form at `(∞,∞)` is `du₁ ∧ du₂`. -/
theorem surfaceYHolomorphicTwoForm_evaluation :
    holomorphicFormEvaluation (Over.mk surfaceToBase) 2
        (.op (surfaceAnalyticOpen (surfaceDifferentialOpen (1, 1)))) surfaceInfinity 2
        surfaceInfinityChartCenter
        (localChart_center_mem_regularChartSectionDomain (Over.mk surfaceToBase) 2
          (surfaceDifferentialOpen (1, 1)) surfaceInfinity surfaceInfinity_mem_differentialOpen)
        (surfaceLocalHolomorphicTwoFormOn (1, 1) (surfaceDifferentialOpen (1, 1)) le_rfl) =
      wedgeCovectors (Fin 2 → ℂ) 2
        (fun i => fderiv ℂ (surfaceYCoordinateInLocalChart i 0) surfaceInfinityChartCenter) := by
  unfold surfaceLocalHolomorphicTwoFormOn
  erw [surfaceLocalTwoFormOn_y_y]
  exact holomorphicFormEvaluation_regular_kaehlerWedge_normalized
    (Over.mk surfaceToBase) 2 (surfaceDifferentialOpen (1, 1))
    (fun i => surfaceYChartCoordinateMap i yDifferentialC)
    (fun i => surfaceYChartCoordinateMap i yDifferentialB)
    (fun i => surfaceYCoordinate i 0) (fun i => surfaceYCoordinate i 1)
    surfaceInfinity surfaceInfinity_mem_differentialOpen
    evaluate_surfaceYDifferentialC_infinity evaluate_surfaceYDifferentialB_infinity

/-- The actual local quotient form is nonzero, witnessed by its analytic value. -/
theorem surfaceYHolomorphicTwoForm_ne_zero :
    surfaceLocalHolomorphicTwoFormOn (1, 1) (surfaceDifferentialOpen (1, 1)) le_rfl ≠ 0 := by
  intro h
  have he := surfaceYHolomorphicTwoForm_evaluation
  rw [h, map_zero] at he
  exact surface_u_derivatives_wedge_ne_zero he.symm

/-- The nonzero local form remains nonzero in the actual holomorphic de Rham sheaf. -/
theorem surfaceYHolomorphicSheafTwoForm_ne_zero :
    surfaceLocalSheafTwoFormOn (1, 1) (surfaceDifferentialOpen (1, 1)) le_rfl ≠ 0 :=
  holomorphicDeRham_toSheafify_ne_zero (Over.mk surfaceToBase) 2
    (surfaceAnalyticOpen (surfaceDifferentialOpen (1, 1))) 2 surfaceYHolomorphicTwoForm_ne_zero

/-- The explicit self-product carries the nonzero global holomorphic two-form obtained by
gluing the actual exterior product of the two elliptic invariant differentials. -/
theorem surfaceGlobalHolomorphicTwoForm_ne_zero : surfaceGlobalHolomorphicTwoForm ≠ 0 := by
  intro h
  have hr := surfaceGlobalHolomorphicTwoForm_restrict (1, 1)
  rw [h, map_zero] at hr
  exact surfaceYHolomorphicSheafTwoForm_ne_zero hr.symm

end AlgebraicGeometry.ExplicitEllipticCandidate
