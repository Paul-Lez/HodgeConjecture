import Other.AlgebraicGeometry.ExplicitEllipticSurfaceDoubleDlog
import Other.AlgebraicGeometry.ExplicitEllipticCurveCechResidueBridge

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

@[expose] noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

example : curveCechAdjustedRepresentative =
    curveCechAdjustedHolomorphicRepresentative := by
  ext z
  rfl

def check_surfaceCechIteratedCover :
    AnalyticIteratedCover surfaceVariety 2 where
  ambient := ![⊤, surfaceCechOuterOverlap, surfaceCechDeepestOpen]
  left := ![surfaceFstCechOpen 0, surfaceCechInnerOpen 0]
  right := ![surfaceFstCechOpen 1, surfaceCechInnerOpen 1]
  cover i := by
    fin_cases i
    · exact surfaceFstCechOpen_cover
    · exact surfaceCechInnerOpen_cover
  overlap i := by
    fin_cases i <;> rfl
  ambient_zero := rfl

example : check_surfaceCechIteratedCover.ambient 2 = surfaceCechDeepestOpen := by
  rfl

example : check_surfaceCechIteratedCover.ambient 1 = surfaceCechOuterOverlap := by
  rfl

example :
    surfaceHolomorphicTopFormMultiplication.hom.app
        (.op surfaceCechDeepestOpen)
        (surfaceCechProductSection curveCechAdjustedRepresentative
          curveCechAdjustedRepresentative) =
      analyticIteratedLogarithmicFormSection surfaceVariety
        surfaceCechIteratedCover surfaceHolomorphicOverlapUnits := by
  rw [surfaceTopFormProduct_eq_logarithmicFormSection]
  rfl

example :
    (surfaceHolomorphicCechExternalProductClass
        curveCechAdjustedRepresentative curveCechAdjustedRepresentative).comp
        (Abelian.Ext.mk₀ surfaceHolomorphicTopFormMultiplication)
        (show 2 + 0 = 2 from rfl) =
      analyticNestedTransitionExtClass surfaceVariety
        surfaceHolomorphicTwoFormSheaf
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover
        (analyticIteratedLogarithmicFormSection surfaceVariety
          surfaceCechIteratedCover surfaceHolomorphicOverlapUnits) := by
  rw [surfaceHolomorphicCechExternalProductClass_comp_topForm]
  rw [surfaceTopFormProduct_eq_iteratedLogarithmicFormSection]

example :
    analyticNestedTransitionExtClass surfaceVariety
        surfaceHolomorphicTwoFormSheaf
        (surfaceFstCechOpen 0) (surfaceFstCechOpen 1)
        (surfaceCechInnerOpen 0) (surfaceCechInnerOpen 1)
        surfaceFstCechOpen_cover inf_le_left inf_le_left
        surfaceCechInnerOpen_cover
        (analyticIteratedLogarithmicFormSection surfaceVariety
          surfaceCechIteratedCover surfaceHolomorphicOverlapUnits) =
      analyticIteratedLogarithmicTransitionExtClass surfaceVariety
        surfaceCechIteratedCover surfaceHolomorphicOverlapUnits := by
  unfold analyticIteratedLogarithmicTransitionExtClass
  rfl

end

end AlgebraicGeometry.ExplicitEllipticCandidate
