/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMHolomorphicDifferential
public import Other.AlgebraicGeometry.TopHodgeFilteredScalarNaturality

/-!
# The de Rham eigenclass of complex multiplication on the explicit elliptic curve

The chartwise pullback calculation for the invariant differential gives `i` times the
original global form. This file carries that equality through the top-filtration
comparison and then through the inclusion into the full holomorphic de Rham complex.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Scalar multiplication on top forms when the dimension has been supplied as an
explicit natural number. -/
def topHolomorphicFormScalarSheafMapOfDimension (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (c : ℂ) :
    holomorphicDeRhamSheaf X d d ⟶ holomorphicDeRhamSheaf X d d :=
  (presheafToSheaf
      (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
      AddCommGrpCat).map
    (scalarHolomorphicDeRhamPresheaf X d d c)

/-- Dimension-indexed version of scalar naturality for the top-form comparison. -/
theorem topHolomorphicFormFilteredEquivOfDimension_scalar
    (d : ℕ) (hd : dim X.left = d)
    [SmoothOfRelativeDimension d X.hom] (c : ℂ)
    (w : (holomorphicDeRhamSheaf X d d).obj.obj (.op ⊤)) :
    topHolomorphicFormFilteredEquivOfDimension X d hd
        ((topHolomorphicFormScalarSheafMapOfDimension X d c).hom.app (.op ⊤) w) =
      hypercohomologyMap X (hodgeFilteredDeRhamComplexScalar X d c) d
        (topHolomorphicFormFilteredEquivOfDimension X d hd w) := by
  subst d
  exact topHolomorphicFormFilteredEquiv_scalar X c w

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

/-- The class of the CM-transformed invariant differential is complex scalar
multiplication by `i` on the highest filtered de Rham class. -/
theorem curveCMTopFilteredClass_eq_i_smul :
    curveCMTopFilteredClass =
      hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 Complex.I) 1
        curveTopFilteredClass := by
  exact topHolomorphicFormFilteredEquivOfDimension_scalar
    curveVariety 1 dim_curve_eq_one Complex.I
    curveGlobalHolomorphicDifferential

/-- After forgetting the filtration, the class of the CM-transformed invariant
differential is `i` times the original explicit de Rham class. -/
theorem curveCMDeRhamClass_eq_i_smul :
    curveCMDeRhamClass =
      Complex.I •
        filteredToDeRhamCohomology curveVariety 1 1 curveTopFilteredClass := by
  unfold curveCMDeRhamClass
  rw [curveCMTopFilteredClass_eq_i_smul]
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

end AlgebraicGeometry.ExplicitEllipticCandidate
