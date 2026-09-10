/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCMProjector

/-!
# The odd CM projection of the explicit elliptic-surface candidate

This file isolates the last analytic input needed by the order-four CM route.  If
the singular class of the invariant elliptic differential has its geometric
pullback eigenvalue `i`, rational periods select a rational curve class whose
odd part `q - J²q` is nonzero.  Its external square gives a rational class on the
actual elliptic surface, and the full `(-i,-i)` order-four projection of its
complexification is nonzero.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicTopology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

/-- The sole comparison input still needed to select an odd rational curve
class: geometric CM pullback acts on the singular class of the invariant
differential by `i`. -/
abbrev CurveCMSingularIEigen : Prop :=
  Singular.cohomologyMap ℂ 1 curveCMTopologicalMap curveComplexSingularClass =
    Complex.I • curveComplexSingularClass

/-- A rational degree-one class selected by the nonzero odd-period theorem. -/
def curveCMOddRationalOneClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℚ curveAnalyticSpace 1 :=
  Classical.choose
    (Singular.exists_rationalCohomology_odd_of_complex_I_eigen
      curveAnalyticSpace 1 curveCMTopologicalMap curveComplexSingularClass
      curveComplexSingularClass_ne_zero hCM)

/-- The selected rational class has nonzero anti-invariant part for the square
of complex multiplication. -/
theorem curveCMOddRationalOneClass_odd_ne_zero (hCM : CurveCMSingularIEigen) :
    curveCMOddRationalOneClass hCM -
        Singular.cohomologyMap ℚ 1 curveCMTopologicalMap
          (Singular.cohomologyMap ℚ 1 curveCMTopologicalMap
            (curveCMOddRationalOneClass hCM)) ≠ 0 :=
  Classical.choose_spec
    (Singular.exists_rationalCohomology_odd_of_complex_I_eigen
      curveAnalyticSpace 1 curveCMTopologicalMap curveComplexSingularClass
      curveComplexSingularClass_ne_zero hCM)

theorem curveCMOddRationalOneClass_ne_zero (hCM : CurveCMSingularIEigen) :
    curveCMOddRationalOneClass hCM ≠ 0 := by
  intro hzero
  apply curveCMOddRationalOneClass_odd_ne_zero hCM
  rw [hzero, map_zero, map_zero, sub_zero]

/-- The rational external square of the selected odd class on the topological
product of the two curves. -/
def curveProductCMOddRationalTwoClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℚ (curveAnalyticSpace ⊗ curveAnalyticSpace) 2 :=
  Singular.degreeOneExternalCohomologyClassOfNonzero ℚ
    (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)
    (curveCMOddRationalOneClass_ne_zero hCM)
    (curveCMOddRationalOneClass_ne_zero hCM)

theorem curveProductCMOddRationalTwoClass_ne_zero
    (hCM : CurveCMSingularIEigen) :
    curveProductCMOddRationalTwoClass hCM ≠ 0 :=
  Singular.degreeOneExternalCohomologyClassOfNonzero_ne_zero ℚ
    (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)
    (curveCMOddRationalOneClass_ne_zero hCM)
    (curveCMOddRationalOneClass_ne_zero hCM)

/-- Transport the odd rational external square to the complex points of the
actual algebraic surface. -/
def surfaceCMOddRationalTwoClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℚ surfaceAnalyticSpace 2 :=
  (Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm
    (curveProductCMOddRationalTwoClass hCM)

theorem surfaceCMOddRationalTwoClass_ne_zero (hCM : CurveCMSingularIEigen) :
    surfaceCMOddRationalTwoClass hCM ≠ 0 :=
  (Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm.injective.ne
    (curveProductCMOddRationalTwoClass_ne_zero hCM)

/-- Complexification of the odd rational class on the actual surface. -/
def surfaceCMOddComplexifiedTwoClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℂ surfaceAnalyticSpace 2 :=
  Singular.rationalToComplexCohomologyMap surfaceAnalyticSpace 2
    (surfaceCMOddRationalTwoClass hCM)

/-- In product coordinates, the complexification is the external product of
the complexified rational odd factor with itself. -/
theorem surfaceCMOddComplexifiedTwoClass_product
    (hCM : CurveCMSingularIEigen) :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        (surfaceCMOddComplexifiedTwoClass hCM) =
      Singular.degreeOneExternalCohomologyBilinear ℂ
        curveAnalyticSpace curveAnalyticSpace
        (Singular.rationalToComplexCohomologyMap curveAnalyticSpace 1
          (curveCMOddRationalOneClass hCM))
        (Singular.rationalToComplexCohomologyMap curveAnalyticSpace 1
          (curveCMOddRationalOneClass hCM)) := by
  rw [surfaceCMOddComplexifiedTwoClass, surfaceCMOddRationalTwoClass]
  rw [show
      (Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm
          (curveProductCMOddRationalTwoClass hCM) =
        Singular.cohomologyMap ℚ 2 surfaceAnalyticProductIso.hom
          (curveProductCMOddRationalTwoClass hCM) from rfl]
  rw [Singular.rationalToComplexCohomologyMap_naturality]
  rw [show Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
      (Singular.cohomologyMap ℂ 2 surfaceAnalyticProductIso.hom
        (Singular.rationalToComplexCohomologyMap
          (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
          (curveProductCMOddRationalTwoClass hCM))) =
      Singular.rationalToComplexCohomologyMap
          (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
          (curveProductCMOddRationalTwoClass hCM) by
        exact LinearEquiv.apply_symm_apply _ _]
  exact
    Singular.rationalToComplexCohomologyMap_degreeOneExternalCohomologyClassOfNonzero
      (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)
      (curveCMOddRationalOneClass_ne_zero hCM)
      (curveCMOddRationalOneClass_ne_zero hCM)

/-- The full order-four `(-i,-i)` projection of the product-coordinate
complexification. -/
def curveProductCMOddMinusTwoClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℂ (curveAnalyticSpace ⊗ curveAnalyticSpace) 2 :=
  Singular.continuousOrderFourCMMinusExternalClass
    curveAnalyticSpace curveAnalyticSpace
    curveCMTopologicalMap curveCMTopologicalMap
    (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)

/-- The projected class is nonzero.  This is the concrete odd-part conclusion
that was unavailable for the arbitrary rational class used earlier. -/
theorem curveProductCMOddMinusTwoClass_ne_zero
    (hCM : CurveCMSingularIEigen) :
    curveProductCMOddMinusTwoClass hCM ≠ 0 := by
  exact Singular.continuousOrderFourCMMinusExternalClass_ne_zero
    curveAnalyticSpace curveAnalyticSpace
    curveCMTopologicalMap curveCMTopologicalMap
    (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)
    (curveCMOddRationalOneClass_odd_ne_zero hCM)
    (curveCMOddRationalOneClass_odd_ne_zero hCM)

/-- Applying the two order-four projectors to the complexification of the
rational surface class gives the named nonzero projected class. -/
theorem iteratedProductProjector_surfaceCMOddComplexifiedTwoClass
    (hCM : CurveCMSingularIEigen) :
    Singular.orderFourCMMinusPart
        (Singular.firstFactorCohomologyEnd curveAnalyticSpace
          curveAnalyticSpace curveCMTopologicalMap)
      (Singular.orderFourCMMinusPart
        (Singular.secondFactorCohomologyEnd curveAnalyticSpace
          curveAnalyticSpace curveCMTopologicalMap)
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
          (surfaceCMOddComplexifiedTwoClass hCM))) =
      curveProductCMOddMinusTwoClass hCM := by
  rw [surfaceCMOddComplexifiedTwoClass_product]
  exact Singular.iteratedProductProjector_externalClass
    curveAnalyticSpace curveAnalyticSpace
    curveCMTopologicalMap curveCMTopologicalMap
    (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)

theorem iteratedProductProjector_surfaceCMOddComplexifiedTwoClass_ne_zero
    (hCM : CurveCMSingularIEigen) :
    Singular.orderFourCMMinusPart
        (Singular.firstFactorCohomologyEnd curveAnalyticSpace
          curveAnalyticSpace curveCMTopologicalMap)
      (Singular.orderFourCMMinusPart
        (Singular.secondFactorCohomologyEnd curveAnalyticSpace
          curveAnalyticSpace curveCMTopologicalMap)
        (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
          (surfaceCMOddComplexifiedTwoClass hCM))) ≠ 0 := by
  rw [iteratedProductProjector_surfaceCMOddComplexifiedTwoClass]
  exact curveProductCMOddMinusTwoClass_ne_zero hCM

/-! ## The corrected detector on the actual surface -/

/-- The corrected whole-degree-two CM detector on the actual surface.  The two
odd-part numerators remove the factor-even summands before the double-minus
operator selects the simultaneous `-i` part. -/
def surfaceCMOddDoubleMinusEnd :
    Module.End ℂ (Singular.Cohomology ℂ surfaceAnalyticSpace 2) :=
  (Singular.cmOddPartEnd
      (Singular.cohomologyMap ℂ 2 surfaceFirstCMTopologicalMap)).comp
    ((Singular.cmOddPartEnd
      (Singular.cohomologyMap ℂ 2 surfaceSecondCMTopologicalMap)).comp
        surfaceCMDoubleMinusEnd)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In product coordinates, the corrected detector on the actual surface is
the factorwise corrected detector. -/
theorem surfaceProductCohomologyEquiv_surfaceCMOddDoubleMinusEnd
    (x : Singular.Cohomology ℂ surfaceAnalyticSpace 2) :
    Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2
        (surfaceCMOddDoubleMinusEnd x) =
      Singular.productCMOddDoubleMinusEnd
        curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ
          surfaceAnalyticProductIso 2 x) := by
  simp only [surfaceCMOddDoubleMinusEnd,
    Singular.productCMOddDoubleMinusEnd, Singular.cmOddPartEnd,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_sub, surfaceProductCohomologyEquiv_firstCM,
    surfaceProductCohomologyEquiv_firstCM,
    map_sub, surfaceProductCohomologyEquiv_secondCM,
    surfaceProductCohomologyEquiv_secondCM,
    surfaceProductCohomologyEquiv_surfaceCMDoubleMinusEnd]

/-- The corrected surface detector is nonzero on the corrected rational
external-product candidate after complexification. -/
theorem surfaceCMOddDoubleMinusEnd_surfaceCMOddComplexifiedTwoClass_ne_zero
    (hCM : CurveCMSingularIEigen) :
    surfaceCMOddDoubleMinusEnd (surfaceCMOddComplexifiedTwoClass hCM) ≠ 0 := by
  intro hzero
  have hproduct :
      Singular.productCMOddDoubleMinusEnd
        curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap curveCMTopologicalMap
        (Singular.cohomologyLinearEquivOfIso ℂ
          surfaceAnalyticProductIso 2
          (surfaceCMOddComplexifiedTwoClass hCM)) ≠ 0 := by
    rw [surfaceCMOddComplexifiedTwoClass_product]
    exact
      Singular.productCMOddDoubleMinusEnd_externalRationalClass_ne_zero
        curveAnalyticSpace curveAnalyticSpace
        curveCMTopologicalMap curveCMTopologicalMap
        (curveCMOddRationalOneClass hCM) (curveCMOddRationalOneClass hCM)
        (curveCMOddRationalOneClass_odd_ne_zero hCM)
        (curveCMOddRationalOneClass_odd_ne_zero hCM)
  apply hproduct
  rw [← surfaceProductCohomologyEquiv_surfaceCMOddDoubleMinusEnd, hzero,
    map_zero]

end AlgebraicGeometry.ExplicitEllipticCandidate
