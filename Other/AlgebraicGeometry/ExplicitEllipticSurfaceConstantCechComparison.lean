/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ConstantToHolomorphicExtComparison
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechCohomology
public import Other.AlgebraicGeometry.ExplicitEllipticCurveCechNonvanishing
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceFirstHodgeReduction

/-!
# The exact constant/Cech comparison needed by the elliptic-surface candidate

This file expresses the remaining comparison problem entirely in sheaf Ext. The
constant-to-holomorphic-function map is postcomposition in Ext, while the
explicit four-chart class is presented by a degree-two extension. Thus equality
of the two cohomology classes is equivalent to one concrete equality of
degree-two extensions.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceVariety_smoothForConstantCechComparison :
    Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

local instance surfaceIntrinsicDimensionSmoothForConstantCechComparison :
    SmoothOfRelativeDimension (dim surfaceVariety.left) surfaceVariety.hom := by
  rw [show dim surfaceVariety.left = 2 from dim_surface_eq_two]
  infer_instance

/-- The explicit complex constant class, presented as a degree-two sheaf Ext
class with target the complex constant sheaf. -/
def explicitSurfaceComplexConstantExtClass :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (constantComplexSheaf surfaceVariety) 2 :=
  complexConstantCohomologyExtEquiv surfaceVariety 2
    explicitSurfaceComplexifiedExternalBettiClass

/-- The image of the explicit complex constant class after postcomposing its
Ext representative with the inclusion of constants into holomorphic
functions. -/
def explicitSurfaceConstantToHolomorphicExtClass :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (holomorphicAdditiveFunctionSheaf surfaceVariety
        (dim surfaceVariety.left)) 2 :=
  explicitSurfaceComplexConstantExtClass.comp
    (Abelian.Ext.mk₀
      (constantComplexToHolomorphicFunctionSheaf surfaceVariety))
    (show 2 + 0 = 2 from rfl)

/-- The adjusted four-chart Cech product, with its displayed dimension-two
function sheaf transported to the intrinsic holomorphic-function sheaf. -/
def surfaceAdjustedCechHolomorphicExtClass :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      (holomorphicAdditiveFunctionSheaf surfaceVariety
        (dim surfaceVariety.left)) 2 :=
  (surfaceHolomorphicCechExternalProductClass
      curveCechAdjustedHolomorphicRepresentative
      curveCechAdjustedHolomorphicRepresentative).comp
    (Abelian.Ext.mk₀ surfaceCechFunctionSheafIso.hom)
    (show 2 + 0 = 2 from rfl)

/-- The adjusted Cech cohomology class is nonzero exactly when its concrete
degree-two Ext representative (in the intrinsic function sheaf) is nonzero. -/
theorem surfaceAdjustedCechCohomologyClass_ne_zero_iff_ext :
    Iff
      (Ne (surfaceHolomorphicCechExternalProductCohomologyClass
          curveCechAdjustedHolomorphicRepresentative
          curveCechAdjustedHolomorphicRepresentative) 0)
      (Ne surfaceAdjustedCechHolomorphicExtClass 0) := by
  let e := sheafExtHypercohomologyEquiv surfaceVariety
    (holomorphicAdditiveFunctionSheaf surfaceVariety
      (dim surfaceVariety.left)) 0 2
  have hcech :
      surfaceHolomorphicCechExternalProductCohomologyClass
          curveCechAdjustedHolomorphicRepresentative
          curveCechAdjustedHolomorphicRepresentative =
        e surfaceAdjustedCechHolomorphicExtClass := by
    rfl
  constructor
  · intro hcoh hext
    apply hcoh
    rw [hcech, hext]
    dsimp only [e]
    exact sheafExtHypercohomologyEquiv_zero surfaceVariety
      (holomorphicAdditiveFunctionSheaf surfaceVariety
        (dim surfaceVariety.left)) 0 2
  · intro hext hcoh
    apply hext
    apply e.injective
    have hezero : e 0 = 0 := by
      dsimp only [e]
      exact sheafExtHypercohomologyEquiv_zero surfaceVariety
        (holomorphicAdditiveFunctionSheaf surfaceVariety
          (dim surfaceVariety.left)) 0 2
    exact (hcech.symm.trans hcoh).trans hezero.symm

/-- The two remaining concrete Ext facts imply that the named rational class
is not Hodge. Both hypotheses are statements about the displayed degree-two
extensions. -/
theorem explicitSurfaceRationalExternalBettiClass_not_isHodge_of_ext
    (hcompare :
      complexConstantToHolomorphicFunctionCohomology surfaceVariety 2
          explicitSurfaceComplexifiedExternalBettiClass =
        surfaceHolomorphicCechExternalProductCohomologyClass
          curveCechAdjustedHolomorphicRepresentative
          curveCechAdjustedHolomorphicRepresentative)
    (hnonzero : Ne surfaceAdjustedCechHolomorphicExtClass 0) :
    Not (IsHodgeClass Rat surfaceVariety 1
      explicitSurfaceRationalExternalBettiClass) := by
  apply explicitSurfaceRationalExternalBettiClass_not_isHodge_of_image_ne_zero
  rw [hcompare]
  exact surfaceAdjustedCechCohomologyClass_ne_zero_iff_ext.mpr hnonzero

end AlgebraicGeometry.ExplicitEllipticCandidate
