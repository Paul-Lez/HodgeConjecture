/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CompactFirstHodge
public import Other.AlgebraicGeometry.TopHodgeFilteredClass
public import Other.AlgebraicGeometry.ExplicitEllipticAnalyticNonvanishing
public import Other.AlgebraicGeometry.ExplicitEllipticSegre

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension

/-!
# The explicit elliptic differential in de Rham cohomology

The global invariant differential on the explicit smooth projective elliptic curve gives a
nonzero first-filtered class. Compactness makes the first filtered-to-de Rham map injective, so
this class remains nonzero in actual analytic de Rham hypercohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

instance curveVariety_smoothMorphism : Smooth curveVariety.hom :=
  SmoothOfRelativeDimension.smooth 1 curveVariety.hom

theorem dim_curve_eq_one : dim curve = 1 := by
  rw [TopologicalSpace.dim_eq_krullDim,
    SmoothOfRelativeDimension.orderKrullDim_eq_complex
      (f := curveToBase) (d := 1)]
  simp

/-- The filtered degree-one class of the explicit elliptic differential. -/
def curveTopFilteredClass :
    FilteredDeRhamHypercohomology curveVariety 1 1 :=
  topHolomorphicFormFilteredEquivOfDimension curveVariety 1 dim_curve_eq_one
    curveGlobalHolomorphicDifferential

theorem curveTopFilteredClass_ne_zero : curveTopFilteredClass ≠ 0 := by
  intro h
  apply curveGlobalHolomorphicDifferential_ne_zero
  apply (topHolomorphicFormFilteredEquivOfDimension curveVariety 1
    dim_curve_eq_one).injective
  exact h.trans (topHolomorphicFormFilteredEquivOfDimension_zero curveVariety 1
    dim_curve_eq_one).symm

/-- The explicit elliptic differential survives in actual analytic de Rham cohomology. -/
theorem curveTopFilteredClass_toDeRham_ne_zero :
    filteredToDeRhamCohomology curveVariety 1 1 curveTopFilteredClass ≠ 0 := by
  intro h
  apply curveTopFilteredClass_ne_zero
  apply firstHodgeFilteredToDeRham_injective curveVariety
  exact h.trans (map_zero (filteredToDeRhamCohomology curveVariety 1 1)).symm

end AlgebraicGeometry.ExplicitEllipticCandidate
