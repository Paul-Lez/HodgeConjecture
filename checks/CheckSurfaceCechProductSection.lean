import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCechCover
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceHolomorphicPullback

open CategoryTheory TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

abbrev testCurveCechOpen (i : Fin 2) :
    Opens (TopCat.of (ComplexPoint curveVariety)) :=
  curveAnalyticOpen (chart (differentialChartIndex i))

abbrev testCurveCechOverlap := testCurveCechOpen 0 ⊓ testCurveCechOpen 1

abbrev testSurfaceCechDeepestOpen :=
  surfaceCechInnerOpen 0 ⊓ surfaceCechInnerOpen 1

example : testCurveCechOpen 0 ⊔ testCurveCechOpen 1 = ⊤ := by
  exact curveAnalyticOpen_cover

example :
    testCurveCechOverlap.comap
        (analyticMapContinuous surfaceVariety curveVariety surfaceVarietyFst) =
      surfaceCechOuterOverlap := by
  ext z
  rfl

example :
    testCurveCechOverlap.comap
        (analyticMapContinuous surfaceVariety curveVariety surfaceVarietySnd) =
      surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 := by
  ext z
  rfl

#check surfaceFstHolomorphicFunctionPullback
#check surfaceSndHolomorphicFunctionPullback
#check holomorphicRestrictionAlgHom

def testSurfaceFstOverlapPullback
    (a : OpenHolomorphicFunctions curveVariety 1 (.op testCurveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op surfaceCechOuterOverlap) :=
  surfaceFstHolomorphicFunctionPullback.hom.app (.op testCurveCechOverlap) a

def testSurfaceSndOverlapPullback
    (b : OpenHolomorphicFunctions curveVariety 1 (.op testCurveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2
      (.op (surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1)) :=
  surfaceSndHolomorphicFunctionPullback.hom.app (.op testCurveCechOverlap) b

def testSurfaceCechProductSection
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op testCurveCechOverlap)) :
    OpenHolomorphicFunctions surfaceVariety 2 (.op testSurfaceCechDeepestOpen) :=
  holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show testSurfaceCechDeepestOpen ≤ surfaceCechOuterOverlap by
        exact (inf_le_left.trans inf_le_left))).op
      (testSurfaceFstOverlapPullback a) *
    holomorphicRestrictionAlgHom surfaceVariety 2
      (homOfLE (show testSurfaceCechDeepestOpen ≤
          surfaceSndCechOpen 0 ⊓ surfaceSndCechOpen 1 by
        apply le_inf
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right.trans inf_le_right)).op
      (testSurfaceSndOverlapPullback b)

def testSurfaceCechProductExtClass
    (a b : OpenHolomorphicFunctions curveVariety 1 (.op testCurveCechOverlap)) :
    Abelian.Ext.{1} (constantIntegerSheaf surfaceVariety)
      surfaceCechHolomorphicFunctionSheaf 2 :=
  surfaceHolomorphicNestedTransitionClass (testSurfaceCechProductSection a b)

end AlgebraicGeometry.ExplicitEllipticCandidate
