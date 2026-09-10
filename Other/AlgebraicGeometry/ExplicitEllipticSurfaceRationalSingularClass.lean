/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfacePointProduct
public import Other.AlgebraicGeometry.BettiGlobalSectionsAdditivity
public import Other.AlgebraicGeometry.ComplexBettiGlobalSectionsComparison
public import Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact
public import Other.AlgebraicTopology.SingularCohomologyCoefficientNonvanishing
public import Other.AlgebraicTopology.SingularProductCoefficientChange

/-!
# A rational external-product class on the explicit elliptic surface

A nonzero complex singular class in degree one on the explicit elliptic curve gives a
nonzero rational class without any finite-dimensionality assumption.  Representative
cocycles for two copies of that rational class are multiplied by the degree-`(1,1)` shuffle
construction.  The resulting rational degree-two class is then transported across the
homeomorphism between the explicit surface and the topological self-product of the curve.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicTopology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

local instance surfaceVariety_smoothForBetti : Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

abbrev curveAnalyticSpace : TopCat :=
  TopCat.of (ComplexPoint curveVariety)

abbrev surfaceAnalyticSpace : TopCat :=
  TopCat.of (ComplexPoint surfaceVariety)

/-- The pointwise product homeomorphism, regarded as an isomorphism in `TopCat`. -/
def surfaceAnalyticProductIso :
    surfaceAnalyticSpace ≅ curveAnalyticSpace ⊗ curveAnalyticSpace :=
  TopCat.isoOfHomeo (X := surfaceAnalyticSpace)
    (Y := curveAnalyticSpace ⊗ curveAnalyticSpace)
    surfaceComplexPointHomeomorph

/-- A chosen rational degree-one class obtained from a nonzero complex singular class. -/
def curveRationalOneClassOfComplexNonzero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.Cohomology ℚ curveAnalyticSpace 1 :=
  Classical.choose
    (Singular.exists_rationalCohomologyClass_image_ne_zero
      curveAnalyticSpace 1 alpha halpha)

theorem curveRationalOneClassOfComplexNonzero_image_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap curveAnalyticSpace 1
      (curveRationalOneClassOfComplexNonzero alpha halpha) ≠ 0 :=
  Classical.choose_spec
    (Singular.exists_rationalCohomologyClass_image_ne_zero
      curveAnalyticSpace 1 alpha halpha)

theorem curveRationalOneClassOfComplexNonzero_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    curveRationalOneClassOfComplexNonzero alpha halpha ≠ 0 := by
  intro hzero
  apply curveRationalOneClassOfComplexNonzero_image_ne_zero alpha halpha
  rw [hzero, map_zero]

/-- The chosen rational external-product class on the topological self-product of the curve. -/
def curveProductRationalExternalTwoClass
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.Cohomology ℚ (curveAnalyticSpace ⊗ curveAnalyticSpace) 2 :=
  Singular.degreeOneExternalCohomologyClassOfNonzero ℚ
    (curveRationalOneClassOfComplexNonzero alpha halpha)
    (curveRationalOneClassOfComplexNonzero alpha halpha)
    (curveRationalOneClassOfComplexNonzero_ne_zero alpha halpha)
    (curveRationalOneClassOfComplexNonzero_ne_zero alpha halpha)

theorem curveProductRationalExternalTwoClass_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    curveProductRationalExternalTwoClass alpha halpha ≠ 0 :=
  Singular.degreeOneExternalCohomologyClassOfNonzero_ne_zero ℚ
    (curveRationalOneClassOfComplexNonzero alpha halpha)
    (curveRationalOneClassOfComplexNonzero alpha halpha)
    (curveRationalOneClassOfComplexNonzero_ne_zero alpha halpha)
    (curveRationalOneClassOfComplexNonzero_ne_zero alpha halpha)

/-- The chosen cycle/cocycle representative of the rational curve class.  Its cocycle
represents that exact class, rather than merely detecting some nonzero class. -/
def curveRationalOneRepresentativePairing
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.OneCycleCocycleRepresentativePairing ℚ curveAnalyticSpace
      (curveRationalOneClassOfComplexNonzero alpha halpha) :=
  Singular.oneCycleCocycleRepresentativePairingOfNonzero ℚ
    (curveRationalOneClassOfComplexNonzero alpha halpha)
    (curveRationalOneClassOfComplexNonzero_ne_zero alpha halpha)

/-- After extending coefficients, the chosen rational product class is exactly the external
product of the coefficient-extended representative cocycle. -/
theorem curveProductRationalExternalTwoClass_toComplex
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap
        (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
        (curveProductRationalExternalTwoClass alpha halpha) =
      let a := curveRationalOneRepresentativePairing alpha halpha
      Singular.degreeOneExternalCohomologyClass ℂ
        (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
        (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
        (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
          map_zero])
        (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
          map_zero]) := by
  let a := curveRationalOneRepresentativePairing alpha halpha
  change Singular.rationalToComplexCohomologyMap
      (curveAnalyticSpace ⊗ curveAnalyticSpace) 2
      (Singular.degreeOneExternalCohomologyClass ℚ a.cochain a.cochain
        a.coboundary_eq_zero a.coboundary_eq_zero) = _
  exact Singular.rationalToComplexCohomologyMap_degreeOneExternalCohomologyClass
    a.cochain a.cochain a.coboundary_eq_zero a.coboundary_eq_zero

/-- The rational shuffle product of the two detecting curve cycles. -/
def curveProductRationalShuffleTwoHomologyClass
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.Homology ℚ (curveAnalyticSpace ⊗ curveAnalyticSpace) 2 :=
  let a := curveRationalOneRepresentativePairing alpha halpha
  Singular.degreeOneShuffleHomologyClass ℚ a.chain a.chain
    a.boundary_eq_zero a.boundary_eq_zero

/-- The rational external cohomology class evaluates nontrivially on its rational shuffle
homology class. -/
theorem curveProductRationalExternalTwoClass_shuffle_pairing_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    curveProductRationalExternalTwoClass alpha halpha
        (curveProductRationalShuffleTwoHomologyClass alpha halpha) ≠ 0 := by
  let a := curveRationalOneRepresentativePairing alpha halpha
  change Singular.degreeOneExternalCohomologyClass ℚ a.cochain a.cochain
      a.coboundary_eq_zero a.coboundary_eq_zero
      (Singular.degreeOneShuffleHomologyClass ℚ a.chain a.chain
        a.boundary_eq_zero a.boundary_eq_zero) ≠ 0
  rw [Singular.degreeOneExternalCohomologyClass_shuffleHomologyClass]
  exact mul_ne_zero a.pairing_ne_zero a.pairing_ne_zero

theorem curveProductRationalShuffleTwoHomologyClass_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    curveProductRationalShuffleTwoHomologyClass alpha halpha ≠ 0 := by
  intro hzero
  apply curveProductRationalExternalTwoClass_shuffle_pairing_ne_zero alpha halpha
  rw [hzero, map_zero]

/-- The rational degree-two external-product class transported to the analytic space of the
explicit algebraic surface. -/
def surfaceRationalExternalTwoClass
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.Cohomology ℚ surfaceAnalyticSpace 2 :=
  (Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm
    (curveProductRationalExternalTwoClass alpha halpha)

/-- Coefficient extension and transport across the product homeomorphism commute. Thus the
complexification of the rational surface class is the transported complex external product. -/
theorem surfaceRationalExternalTwoClass_toComplex
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap surfaceAnalyticSpace 2
        (surfaceRationalExternalTwoClass alpha halpha) =
      (Singular.cohomologyLinearEquivOfIso ℂ surfaceAnalyticProductIso 2).symm
        (let a := curveRationalOneRepresentativePairing alpha halpha
        Singular.degreeOneExternalCohomologyClass ℂ
          (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
          (Singular.qToCSingularCochain curveAnalyticSpace 1 a.cochain)
          (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
            map_zero])
          (by rw [← Singular.qToCSingularCochain_coboundary, a.coboundary_eq_zero,
            map_zero])) := by
  rw [show surfaceRationalExternalTwoClass alpha halpha =
      Singular.cohomologyMap ℚ 2 surfaceAnalyticProductIso.hom
        (curveProductRationalExternalTwoClass alpha halpha) from rfl]
  rw [Singular.rationalToComplexCohomologyMap_naturality_degreeTwo]
  rw [curveProductRationalExternalTwoClass_toComplex]
  rfl

theorem surfaceRationalExternalTwoClass_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    surfaceRationalExternalTwoClass alpha halpha ≠ 0 := by
  exact (Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm.injective.ne
    (curveProductRationalExternalTwoClass_ne_zero alpha halpha)

/-- The rational shuffle homology class transported from the product to the actual analytic
surface. -/
def surfaceRationalShuffleTwoHomologyClass
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.Homology ℚ surfaceAnalyticSpace 2 :=
  (Singular.homologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2).symm
    (curveProductRationalShuffleTwoHomologyClass alpha halpha)

/-- The transported rational external cohomology and shuffle homology classes retain their
nonzero evaluation pairing on the actual analytic surface. -/
theorem surfaceRationalExternalTwoClass_shuffle_pairing_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    surfaceRationalExternalTwoClass alpha halpha
        (surfaceRationalShuffleTwoHomologyClass alpha halpha) ≠ 0 := by
  have htransport :=
    Singular.cohomologyLinearEquivOfIso_apply_homologyLinearEquivOfIso ℚ
      surfaceAnalyticProductIso 2
      (surfaceRationalExternalTwoClass alpha halpha)
      (surfaceRationalShuffleTwoHomologyClass alpha halpha)
  rw [show Singular.cohomologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2
      (surfaceRationalExternalTwoClass alpha halpha) =
        curveProductRationalExternalTwoClass alpha halpha by
      exact LinearEquiv.apply_symm_apply _ _] at htransport
  rw [show Singular.homologyLinearEquivOfIso ℚ surfaceAnalyticProductIso 2
      (surfaceRationalShuffleTwoHomologyClass alpha halpha) =
        curveProductRationalShuffleTwoHomologyClass alpha halpha by
      exact LinearEquiv.apply_symm_apply _ _] at htransport
  rw [← htransport]
  exact curveProductRationalExternalTwoClass_shuffle_pairing_ne_zero alpha halpha

theorem surfaceRationalShuffleTwoHomologyClass_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    surfaceRationalShuffleTwoHomologyClass alpha halpha ≠ 0 := by
  intro hzero
  apply surfaceRationalExternalTwoClass_shuffle_pairing_ne_zero alpha halpha
  rw [hzero, map_zero]

/-- The singular complexification of the rational external-product class is nonzero. -/
theorem surfaceRationalExternalTwoClass_toComplex_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    Singular.rationalToComplexCohomologyMap surfaceAnalyticSpace 2
      (surfaceRationalExternalTwoClass alpha halpha) ≠ 0 := by
  intro hzero
  apply surfaceRationalExternalTwoClass_ne_zero alpha halpha
  apply Singular.rationalToComplexCohomologyMap_injective surfaceAnalyticSpace 2
  rw [hzero, map_zero]

/-- The same class in the rational constant-sheaf cohomology type used by the Hodge
conjecture statement. -/
def surfaceRationalExternalBettiClass
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    ComplexPoint.FieldCohomology ℚ surfaceVariety 2 := by
  let : ∀ U : Opens (ComplexPoint surfaceVariety), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace surfaceVariety
  exact (ComplexPoint.rationalCohomologyAddEquivSingularCohomology
    surfaceVariety 2).symm (surfaceRationalExternalTwoClass alpha halpha)

theorem surfaceRationalExternalBettiClass_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    surfaceRationalExternalBettiClass alpha halpha ≠ 0 := by
  let : ∀ U : Opens (ComplexPoint surfaceVariety), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace surfaceVariety
  exact (ComplexPoint.rationalCohomologyAddEquivSingularCohomology
    surfaceVariety 2).symm.map_ne_zero_iff.mpr
      (surfaceRationalExternalTwoClass_ne_zero alpha halpha)

/-- The complex constant-sheaf image of the rational surface class is nonzero. -/
theorem surfaceRationalExternalBettiClass_toComplex_ne_zero
    (alpha : Singular.Cohomology ℂ curveAnalyticSpace 1) (halpha : alpha ≠ 0) :
    ComplexPoint.fieldToComplexCohomology ℚ surfaceVariety 2
      (surfaceRationalExternalBettiClass alpha halpha) ≠ 0 := by
  intro hzero
  apply surfaceRationalExternalBettiClass_ne_zero alpha halpha
  apply ComplexPoint.fieldToComplexCohomology_injective ℚ surfaceVariety 2
  rw [hzero, map_zero]

/-! ## The unconditional explicit classes -/

/-- The concrete rational degree-two singular class obtained from the invariant elliptic
differential. -/
def explicitSurfaceRationalExternalTwoClass :
    Singular.Cohomology ℚ surfaceAnalyticSpace 2 :=
  surfaceRationalExternalTwoClass curveComplexSingularClass
    curveComplexSingularClass_ne_zero

theorem explicitSurfaceRationalExternalTwoClass_ne_zero :
    explicitSurfaceRationalExternalTwoClass ≠ 0 :=
  surfaceRationalExternalTwoClass_ne_zero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

/-- The concrete rational shuffle homology class paired with the external cohomology class. -/
def explicitSurfaceRationalShuffleTwoHomologyClass :
    Singular.Homology ℚ surfaceAnalyticSpace 2 :=
  surfaceRationalShuffleTwoHomologyClass curveComplexSingularClass
    curveComplexSingularClass_ne_zero

theorem explicitSurfaceRationalExternalTwoClass_shuffle_pairing_ne_zero :
    explicitSurfaceRationalExternalTwoClass
        explicitSurfaceRationalShuffleTwoHomologyClass ≠ 0 :=
  surfaceRationalExternalTwoClass_shuffle_pairing_ne_zero
    curveComplexSingularClass curveComplexSingularClass_ne_zero

theorem explicitSurfaceRationalShuffleTwoHomologyClass_ne_zero :
    explicitSurfaceRationalShuffleTwoHomologyClass ≠ 0 :=
  surfaceRationalShuffleTwoHomologyClass_ne_zero
    curveComplexSingularClass curveComplexSingularClass_ne_zero

/-- The complex singular class obtained by extending the coefficients of the concrete rational
external-product class. -/
def explicitSurfaceComplexifiedExternalTwoClass :
    Singular.Cohomology ℂ surfaceAnalyticSpace 2 :=
  Singular.rationalToComplexCohomologyMap surfaceAnalyticSpace 2
    explicitSurfaceRationalExternalTwoClass

theorem explicitSurfaceComplexifiedExternalTwoClass_ne_zero :
    explicitSurfaceComplexifiedExternalTwoClass ≠ 0 :=
  surfaceRationalExternalTwoClass_toComplex_ne_zero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

/-- The concrete rational degree-two class in the constant-sheaf cohomology used by the Hodge
conjecture statement. -/
def explicitSurfaceRationalExternalBettiClass :
    ComplexPoint.FieldCohomology ℚ surfaceVariety 2 :=
  surfaceRationalExternalBettiClass curveComplexSingularClass
    curveComplexSingularClass_ne_zero

theorem explicitSurfaceRationalExternalBettiClass_ne_zero :
    explicitSurfaceRationalExternalBettiClass ≠ 0 :=
  surfaceRationalExternalBettiClass_ne_zero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

/-- The complex constant-sheaf image of the concrete rational class. -/
def explicitSurfaceComplexifiedExternalBettiClass :
    ComplexPoint.ComplexConstantCohomology surfaceVariety 2 :=
  ComplexPoint.fieldToComplexCohomology ℚ surfaceVariety 2
    explicitSurfaceRationalExternalBettiClass

theorem explicitSurfaceComplexifiedExternalBettiClass_ne_zero :
    explicitSurfaceComplexifiedExternalBettiClass ≠ 0 :=
  surfaceRationalExternalBettiClass_toComplex_ne_zero curveComplexSingularClass
    curveComplexSingularClass_ne_zero

end AlgebraicGeometry.ExplicitEllipticCandidate
