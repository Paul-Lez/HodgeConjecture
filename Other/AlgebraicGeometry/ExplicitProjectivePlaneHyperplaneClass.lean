/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneHyperplane
public import Other.AlgebraicGeometry.ProjectivePlanePresentation
public import Other.AlgebraicGeometry.ExplicitSmoothClosedSupportSingularClass

/-!
# A supported singular class associated to the coordinate hyperplane in `ℙ²`

This specializes the normalized normal-coclass construction to the displayed zero locus `X₀ = 0`,
subject to the geometric instances shown on the declarations below. It does *not* identify this
supported class with the independent coordinate-transition cocycle; that comparison is a separate
task.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane

open AlgebraicGeometry.ComplexPoint

/-- The hereditary-paracompactness instance used by the dimension-specific Betti comparison is
    obtained from the already proved smooth relative dimension of the ambient plane. -/
noncomputable def planeBettiComparison_of_smoothOfRelativeDimension_canonical
    :
    H2 ≃ SingularH2 := by
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U :=
    ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension planeOver 2
  exact planeBettiComparison_of_smoothOfRelativeDimension

/-- A selected degree-two global singular cochain representing the normalized supported construction for
the coordinate hyperplane `X₀ = 0`.

It is obtained by choosing a preimage under the cohomology quotient map, so it is *not* the
displayed coordinate cochain. The two remaining geometric inputs are the ambient projective
presentation and the displayed relative-dimension-one smoothness of the hyperplane. -/
noncomputable def hyperplaneSelectedOrdinaryRawCochain
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint planeOver))).X 2 :=
  smoothClosedOrdinaryRawCochain planeOver hyperplaneOver hyperplaneOverι 1 2

/-- The selected global representative for `X₀ = 0` is closed. -/
lemma hyperplaneSelectedOrdinaryRawCochain_closed
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint planeOver))).d 2 3).hom
      hyperplaneSelectedOrdinaryRawCochain = 0 :=
  smoothClosedOrdinaryRawCochain_closed planeOver hyperplaneOver hyperplaneOverι 1 2

/-- The global supported **singular** class of the explicit zero locus `X₀ = 0`, obtained from the
normalized normal-coclass section. -/
def hyperplaneSupportedSingularClass
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint planeOver))
      (Set.range (Point.map hyperplaneOverι)) 2 :=
  smoothClosedSupportSingularClass planeOver hyperplaneOver hyperplaneOverι 1 2

/-- Forgetting support gives the desired degree-two ordinary singular class of `ℙ²(ℂ)`. -/
def hyperplaneOrdinarySingularClass
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint planeOver)) 2 :=
  smoothClosedOrdinarySingularClass planeOver hyperplaneOver hyperplaneOverι 1 2

/-- The degree-two singular class read from the selected raw representative. -/
noncomputable def hyperplaneOrdinarySingularClassOfSelectedRawCochain
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint planeOver)) 2 :=
  smoothClosedOrdinarySingularClassOfRawCochain planeOver hyperplaneOver hyperplaneOverι 1 2

/-- The selected global cochain represents the supported coordinate-hyperplane singular class. -/
lemma hyperplaneOrdinarySingularClassOfSelectedRawCochain_eq
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    hyperplaneOrdinarySingularClassOfSelectedRawCochain = hyperplaneOrdinarySingularClass :=
  smoothClosedOrdinarySingularClassOfRawCochain_eq
    planeOver hyperplaneOver hyperplaneOverι 1 2

/-- The same explicitly globalised singular class in constant-sheaf hypercohomology. -/
def hyperplaneHypercohomologyClass
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    H^2(planeOver; ℚ) :=
  smoothClosedHypercohomologyClass planeOver hyperplaneOver hyperplaneOverι 1 2

@[simp]
lemma planeBettiComparison_hyperplaneHypercohomologyClass
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    planeBettiComparison_of_smoothOfRelativeDimension_canonical
        (hyperplaneHypercohomologyClass) =
      hyperplaneOrdinarySingularClass :=
  by
    exact rationalCohomologyLinearEquivSingularCohomology_smoothClosedHypercohomologyClass
      planeOver hyperplaneOver hyperplaneOverι 1 2

end AlgebraicGeometry.ProjectivePlane
