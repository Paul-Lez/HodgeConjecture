import Other.AlgebraicGeometry.ProjectivePlaneExplicitClassNormalizationScratch
import Other.AlgebraicGeometry.ExplicitSingularOrdinaryBridge
import Other.AlgebraicGeometry.ExplicitProjectivePlaneHyperplaneCycleComparison

@[expose] noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ProjectivePlane.AnalyticNormalization

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))

noncomputable local instance analyticPlane_isIntegral : IsIntegral analyticPlane.left := by
  change IsIntegral plane
  infer_instance

noncomputable local instance analyticPlane_smooth : Smooth analyticPlane.hom := by
  change Smooth planeOver.hom
  infer_instance

noncomputable local instance analyticPlane_isProjective : IsProjective analyticPlane.hom := by
  change IsProjective planeOver.hom
  infer_instance

theorem coordinateHyperplaneExplicitSupportedSingularClass_eq_smoothClosedSupportSingularClass :
    coordinateHyperplaneExplicitSupportedSingularClass =
      smoothClosedSupportSingularClass analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 := by
  letI : IsIntegral analyticPlane.left := by
    change IsIntegral plane
    infer_instance
  letI : Smooth analyticPlane.hom := by
    change Smooth planeOver.hom
    infer_instance
  letI : IsProjective analyticPlane.hom := by
    change IsProjective planeOver.hom
    infer_instance
  apply smoothClosedSupportSingularClass_eq_of_normalization
    (X := analyticPlane) (Y := hyperplaneOver) (i := hyperplaneAnalyticι)
    (m := 1) (d := 2) coordinateHyperplaneExplicitSupportedSingularClass
  have hsupport : Set.range (Point.map hyperplaneAnalyticι) =
      Set.range (Point.map hyperplaneOverι) := by
    rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
    rfl
  cases hsupport
  change coordinateHyperplaneExplicitSupportedSheafSection = _
  exact coordinateHyperplaneExplicitSupportedSheafSection_eq_smoothClosedSupportCoclassSection

/-- The explicit coordinate Čech/winding singular class agrees with the normalized singular
class attached to the displayed hyperplane.  The proof uses the chartwise normalization above
and the coefficient-forgetting bridge; no cycle-class/Chern-class correspondence is invoked. -/
theorem coordinateHyperplaneExplicitOrdinarySingularClass_eq_hyperplaneOrdinarySingularClass :
    coordinateHyperplaneExplicitOrdinarySingularClass =
      AlgebraicGeometry.ProjectivePlane.hyperplaneOrdinarySingularClass := by
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension planeOver 2
  rw [coordinateHyperplaneExplicitOrdinarySingularClass,
    coordinateHyperplaneExplicitSupportedSingularClass_eq_smoothClosedSupportSingularClass]
  change AlgebraicTopology.Singular.forgetSupport ℚ
      (TopCat.of (ComplexPoint planeOver))
      (Set.range (Point.map hyperplaneOverι)) 2
      (smoothClosedSupportSingularClass planeOver hyperplaneOver hyperplaneOverι 1 2) =
    singularClassOfSupportedSingularClass planeOver
      (Set.range (Point.map hyperplaneOverι)) 2
      (smoothClosedSupportSingularClass planeOver hyperplaneOver hyperplaneOverι 1 2)
  exact (singularClassOfSupportedSingularClass_eq_forgetSupport
    planeOver (Set.range (Point.map hyperplaneOverι)) 2
      (smoothClosedSupportSingularClass planeOver hyperplaneOver hyperplaneOverι 1 2)).symm

/-- The explicit coordinate Čech/winding hypercohomology class agrees with the normalized
hyperplane hypercohomology class. -/
theorem coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective_eq_hyperplaneHypercohomologyClass :
    coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective =
      AlgebraicGeometry.ProjectivePlane.hyperplaneHypercohomologyClass := by
  apply AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension_canonical.injective
  rw [planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective,
    AlgebraicGeometry.ProjectivePlane.planeBettiComparison_hyperplaneHypercohomologyClass]
  exact coordinateHyperplaneExplicitOrdinarySingularClass_eq_hyperplaneOrdinarySingularClass

/-- The concrete transferred singular cocycle and the normalized selected raw representative
represent the same ordinary singular class.  This deliberately compares cohomology classes,
not raw cochains from different complex models. -/
theorem coordinateHyperplaneExplicitOrdinaryCochainClass_eq_hyperplaneOrdinarySingularClassOfSelectedRawCochain :
    (ordinarySingularCohomologyEquivCohomology ℚ analyticPlaneTop 2)
        coordinateHyperplaneExplicitOrdinaryCochainClass =
      AlgebraicGeometry.ProjectivePlane.hyperplaneOrdinarySingularClassOfSelectedRawCochain := by
  rw [coordinateHyperplaneExplicitOrdinaryRawCochain_class,
    coordinateHyperplaneExplicitOrdinarySingularClass_eq_hyperplaneOrdinarySingularClass]
  exact (AlgebraicGeometry.ProjectivePlane.hyperplaneOrdinarySingularClassOfSelectedRawCochain_eq
    ).symm

set_option maxHeartbeats 2000000 in
/-- The normalized smooth hyperplane hypercohomology class is the canonical cycle-component
sheaf class for the coordinate hyperplane. -/
theorem hyperplaneHypercohomologyClass_eq_cycleComponentSheafClass
    :
    AlgebraicGeometry.ProjectivePlane.hyperplaneHypercohomologyClass =
      cycleComponentSheafClass planeOver hyperplaneGenericPoint
        (d := 2) (p := 1)
        (by convert hyperplaneGenericPoint_coheight using 1 <;> norm_num) := by
  have hpos := smoothClosedHypercohomologyClass_eq_positiveKernel
    planeOver hyperplaneOver hyperplaneOverι 1 2
  let Φ : CycleComponentSupportedCohomology planeOver hyperplaneGenericPoint 1 →
      H^(2 * ((2 - 1 : ℕ) : ℤ))(planeOver; ℚ) :=
    fun z =>
      (rationalCohomologyAddEquivAmbientInjectiveHomology planeOver
        (2 * (2 - 1 : ℕ) : ℤ)).symm
        ((HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint planeOver))
            (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint).compl ⊤
            (ambientRationalInjectiveComplex planeOver)).f
          (2 * (2 - 1 : ℕ) : ℤ)) z)
  have hmap := congrArg Φ
    (AlgebraicGeometry.ProjectivePlane.hyperplaneSmoothClosedSupportInjectiveClass_eq_cycleComponent)
  change smoothClosedHypercohomologyClass planeOver hyperplaneOver hyperplaneOverι 1 2 = _
  have htarget : Φ (cycleComponentSupportedInjectiveClass planeOver hyperplaneGenericPoint
      (d := 2) hyperplaneGenericPoint_coheight) =
      cycleComponentSheafClass planeOver hyperplaneGenericPoint
        (d := 2) (p := 1)
        (by convert hyperplaneGenericPoint_coheight using 1 <;> norm_num) := by
    dsimp [Φ, cycleComponentSheafClass]
  have hsmooth :
      (rationalCohomologyAddEquivAmbientInjectiveHomology planeOver
        (2 * (2 - 1 : ℕ) : ℤ)).symm
          ((HomologicalComplex.homologyMap
            (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
              (TopCat.of (ComplexPoint planeOver))
              (smoothClosedAnalyticSupport planeOver hyperplaneOver hyperplaneOverι).compl ⊤
              (ambientRationalInjectiveComplex planeOver)).f
            (2 * (2 - 1 : ℕ) : ℤ))
            (smoothClosedSupportInjectiveClass planeOver hyperplaneOver hyperplaneOverι 1 2)) =
        Φ AlgebraicGeometry.ProjectivePlane.hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent := by
    simp [Φ, AlgebraicGeometry.ProjectivePlane.hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent]
    congr 2
    all_goals try rw [cycleComponentAnalyticClosedSupport_hyperplaneGenericPoint]
    all_goals exact (heq_cast_iff_heq _ _ _).2 HEq.rfl
  have hpos' := hpos
  norm_num at hpos'
  exact hpos'.trans (hsmooth.trans (hmap.trans htarget))

set_option maxHeartbeats 2000000 in
/-- The explicit literal-cochain hypercohomology class equals the canonical sheaf cycle class
of the displayed coordinate hyperplane. -/
theorem coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective_eq_sheafCycleClassOnCycles
    :
    coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective =
      ComplexPoint.sheafCycleClassOnCycles
        AlgebraicGeometry.ProjectivePlane.dimensionedPlane 1
        AlgebraicGeometry.ProjectivePlane.coordinateHyperplaneCycle := by
  rw [coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective_eq,
    coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective_eq_hyperplaneHypercohomologyClass,
    hyperplaneHypercohomologyClass_eq_cycleComponentSheafClass,
    AlgebraicGeometry.ProjectivePlane.sheafCycleClassOnCycles_coordinateHyperplaneCycle]
  change cycleComponentSheafClass planeOver hyperplaneGenericPoint
      (d := 2) (p := 1) _ =
    cycleComponentSheafClass planeOver hyperplaneGenericPoint
      (d := 2) (p := 1) _
  rfl

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
