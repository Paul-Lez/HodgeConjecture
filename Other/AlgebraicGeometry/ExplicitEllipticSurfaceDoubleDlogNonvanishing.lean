/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticIteratedTopTransitionComparison
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDoubleDlog
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceFilteredClass

/-!
# De Rham detection of the explicit elliptic-surface double-dlog class

The concrete two-fold logarithmic transition on the elliptic surface is a
top-form-valued degree-two Ext class.  This file identifies its image in the
full holomorphic de Rham complex and records the resulting nonvanishing
criterion for both it and the adjusted holomorphic Cech product.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceDoubleDlogComparisonSmooth : Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

local instance surfaceDoubleDlogIntrinsicDimensionSmooth :
    SmoothOfRelativeDimension (dim surfaceVariety.left) surfaceVariety.hom :=
  dim_surface_eq_two.symm ▸
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)

local instance surfaceDoubleDlogExplicitFunctionExtZero :
    Zero (Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      surfaceCechHolomorphicFunctionSheaf 2) := by
  change Zero (Abelian.Ext.{1}
    (constantIntegerSheaf (Over.mk surfaceToBase))
    surfaceCechHolomorphicFunctionSheaf 2)
  infer_instance

/-- The displayed-dimension overlap units with their deepest open written as
the terminal ambient of the explicit iterated cover. -/
def surfaceHolomorphicOverlapUnitsDisplayed :
    Fin 2 → (OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceCechIteratedCover.ambient 2)))ˣ := fun j => by
  change (OpenHolomorphicFunctions (Over.mk surfaceToBase) 2
    (.op surfaceCechDeepestOpen))ˣ
  exact surfaceHolomorphicOverlapUnits j

/-- The two explicit overlap units in the intrinsic-dimensional holomorphic
function sheaf used by the full de Rham complex. -/
def surfaceHolomorphicOverlapUnitsIntrinsic :
    Fin 2 → (OpenHolomorphicFunctions surfaceVariety
      (dim surfaceVariety.left)
      (.op (surfaceCechIteratedCover.ambient 2)))ˣ := fun j =>
  analyticOpenHolomorphicUnitOfDimensionEq surfaceVariety
    (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)
    (inferInstance : SmoothOfRelativeDimension
      (dim surfaceVariety.left) surfaceVariety.hom)
    dim_surface_eq_two.symm _ (surfaceHolomorphicOverlapUnitsDisplayed j)

/-- The explicit surface double-dlog Ext class is detected by its concrete
degree-four de Rham image. -/
theorem surfaceIteratedLogarithmicTransitionExtClass_ne_zero_of_deRham
    (h : analyticIteratedLogarithmicDeRhamClass surfaceVariety
      surfaceCechIteratedCover surfaceHolomorphicOverlapUnitsIntrinsic ≠ 0) :
    analyticIteratedLogarithmicTransitionExtClass surfaceVariety
      surfaceCechIteratedCover surfaceHolomorphicOverlapUnits ≠ 0 := by
  have hintrinsic :=
    analyticIteratedLogarithmicTransitionExtClass_ne_zero_of_deRham_of_cardinality_eq_dim
      surfaceVariety dim_surface_eq_two.symm surfaceCechIteratedCover
        surfaceHolomorphicOverlapUnitsIntrinsic h
  have htransport :=
    analyticIteratedLogarithmicTransitionExtClass_ne_zero_iff_of_dimensionEq
      surfaceVariety
      (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)
      (inferInstance : SmoothOfRelativeDimension
        (dim surfaceVariety.left) surfaceVariety.hom)
      dim_surface_eq_two.symm surfaceCechIteratedCover
      surfaceHolomorphicOverlapUnitsDisplayed
  have huIntrinsic :
      (fun j => analyticOpenHolomorphicUnitOfDimensionEq surfaceVariety
        (inferInstance : SmoothOfRelativeDimension 2 surfaceVariety.hom)
        (inferInstance : SmoothOfRelativeDimension
          (dim surfaceVariety.left) surfaceVariety.hom)
        dim_surface_eq_two.symm
        (surfaceCechIteratedCover.ambient
          ⟨2, Nat.lt_succ_self 2⟩)
        (surfaceHolomorphicOverlapUnitsDisplayed j)) =
      surfaceHolomorphicOverlapUnitsIntrinsic := by
    rfl
  rw [huIntrinsic] at htransport
  have hdisplayed := htransport.mpr hintrinsic
  have huDisplayed : surfaceHolomorphicOverlapUnitsDisplayed =
      surfaceHolomorphicOverlapUnits := by
    rfl
  rw [huDisplayed] at hdisplayed
  exact hdisplayed

/-- Nonvanishing of the explicit degree-four de Rham double-logarithmic class
implies nonvanishing of the adjusted degree-two holomorphic-function Cech
class on the surface. -/
theorem surfaceAdjustedCechExternalProductClass_ne_zero_of_deRham
    (h : analyticIteratedLogarithmicDeRhamClass surfaceVariety
      surfaceCechIteratedCover surfaceHolomorphicOverlapUnitsIntrinsic ≠ 0) :
    (surfaceHolomorphicCechExternalProductClass
      curveCechAdjustedRepresentative curveCechAdjustedRepresentative :
        Abelian.Ext.{1} (constantIntegerSheaf (Over.mk surfaceToBase))
          surfaceCechHolomorphicFunctionSheaf 2) ≠ 0 :=
  surfaceAdjustedCechExternalProductClass_ne_zero_of_iterated
    (surfaceIteratedLogarithmicTransitionExtClass_ne_zero_of_deRham h)

end AlgebraicGeometry.ExplicitEllipticCandidate
