/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDifferential
public import Other.AlgebraicGeometry.ExplicitEllipticInfinityCoordinates

/-!
# The product point at infinity and its actual regular coordinates

The point on the self-product is induced by the pair of complex points at infinity.
The four regular coordinates on its Y-by-Y neighborhood are pulled back along the
two scheme projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] regularSectionAlgebra

local instance surfaceInfinitySectionAlgebra (V : surface.Opens) : Algebra ℂ Γ(surface, V) :=
  regularSectionAlgebra (Over.mk surfaceToBase) V

/-- The actual Y-chart polynomial coordinate map on the first factor. -/
def surfaceYCoordinateMapLeft :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Γ(surface, surfaceDifferentialOpen (1, 1)) :=
  (surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl (chart 1)
    (surfaceDifferentialOpen (1, 1)) inf_le_left).comp
    (hypersurfaceCoordinateMap (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime))

/-- The actual Y-chart polynomial coordinate map on the second factor. -/
def surfaceYCoordinateMapRight :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Γ(surface, surfaceDifferentialOpen (1, 1)) :=
  (surfaceSectionPullback (pullback.snd curveToBase curveToBase) pullback.condition.symm
    (chart 1) (surfaceDifferentialOpen (1, 1)) inf_le_right).comp
    (hypersurfaceCoordinateMap (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime))

/-- The four actual regular coordinates: the first index selects the factor. -/
def surfaceYCoordinate (i j : Fin 2) : Γ(surface, surfaceDifferentialOpen (1, 1)) :=
  ![surfaceYCoordinateMapLeft (MvPolynomial.X j),
    surfaceYCoordinateMapRight (MvPolynomial.X j)] i

@[simp] theorem surfaceYCoordinate_zero (j : Fin 2) :
    surfaceYCoordinate 0 j = surfaceYCoordinateMapLeft (MvPolynomial.X j) := rfl

@[simp] theorem surfaceYCoordinate_one (j : Fin 2) :
    surfaceYCoordinate 1 j = surfaceYCoordinateMapRight (MvPolynomial.X j) := rfl

/-- The actual complex point `(∞,∞)` of the scheme fiber product. -/
def surfaceInfinity : ComplexPoint (Over.mk surfaceToBase) :=
  Over.homMk (pullback.lift infinity.left infinity.left rfl) (by
    change pullback.lift infinity.left infinity.left rfl ≫
      (pullback.fst curveToBase curveToBase ≫ curveToBase) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w infinity)

@[simp] theorem surfaceInfinity_fst :
    Point.map (Over.homMk (pullback.fst curveToBase curveToBase) rfl) surfaceInfinity =
      infinity := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[simp] theorem surfaceInfinity_snd :
    Point.map (Over.homMk (pullback.snd curveToBase curveToBase) pullback.condition.symm)
      surfaceInfinity = infinity := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The product point belongs to the actual Y-by-Y product open. -/
theorem surfaceInfinity_mem_differentialOpen :
    surfaceInfinity.underlying ∈ surfaceDifferentialOpen (1, 1) := by
  constructor
  · change (Point.map (Over.homMk (pullback.fst curveToBase curveToBase) rfl :
      Over.mk surfaceToBase ⟶ Over.mk curveToBase)
      surfaceInfinity).underlying ∈ chart 1
    rw [surfaceInfinity_fst]
    exact infinity_mem_chart_one
  · change (Point.map (Over.homMk (pullback.snd curveToBase curveToBase)
      pullback.condition.symm : Over.mk surfaceToBase ⟶ Over.mk curveToBase)
      surfaceInfinity).underlying ∈ chart 1
    rw [surfaceInfinity_snd]
    exact infinity_mem_chart_one

/-- Evaluation commutes with actual scheme pullback, including restriction to a smaller open. -/
theorem evaluate_surfaceSectionPullback (f : surface ⟶ curve)
    (hbase : f ≫ curveToBase = surfaceToBase) (U : curve.Opens) (V : surface.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(curve, U)) (z : ComplexPoint (Over.mk surfaceToBase))
    (hz : z.underlying ∈ V) :
    Point.evaluate V (surfaceSectionPullback f hbase U V h s) z =
      Point.evaluate U s (Point.map (Over.homMk f hbase :
        Over.mk surfaceToBase ⟶ Over.mk curveToBase) z) := by
  change Point.evaluate V (surface.presheaf.map (homOfLE h).op (f.app U s)) z = _
  exact (Point.evaluate_res (X := Over.mk surfaceToBase) h (f.app U s) z hz).symm.trans
    (Point.evaluate_map (Over.homMk f hbase :
      Over.mk surfaceToBase ⟶ Over.mk curveToBase) U s z).symm

/-- All four projection-pulled Y coordinates vanish at the actual product point. -/
@[simp] theorem evaluate_surfaceYCoordinate_infinity (i j : Fin 2) :
    Point.evaluate (surfaceDifferentialOpen (1, 1)) (surfaceYCoordinate i j)
      surfaceInfinity = 0 := by
  let s : Γ(curve, chart 1) :=
    hypersurfaceCoordinateMap (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
      (MvPolynomial.X j)
  have hs : Point.evaluate (chart 1) s infinity = 0 := evaluate_curveYCoordinate_infinity j
  fin_cases i
  · exact (evaluate_surfaceSectionPullback (pullback.fst curveToBase curveToBase) rfl
      (chart 1) (surfaceDifferentialOpen (1, 1)) inf_le_left s surfaceInfinity
      surfaceInfinity_mem_differentialOpen).trans
      ((congrArg (Point.evaluate (X := Over.mk curveToBase) (chart 1) s)
        surfaceInfinity_fst).trans hs)
  · exact (evaluate_surfaceSectionPullback (pullback.snd curveToBase curveToBase)
      pullback.condition.symm (chart 1) (surfaceDifferentialOpen (1, 1)) inf_le_right s
      surfaceInfinity
      surfaceInfinity_mem_differentialOpen).trans
      ((congrArg (Point.evaluate (X := Over.mk curveToBase) (chart 1) s)
        surfaceInfinity_snd).trans hs)

end AlgebraicGeometry.ExplicitEllipticCandidate
