/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.TopHodgeFilteredClass
public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceFormEvaluation
public import Other.AlgebraicGeometry.ExplicitEllipticSegre

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension

/-!
# A nonzero top-filtered hypercohomology class on the explicit surface

The actual nonzero global holomorphic two-form gives a nonzero class in
`FilteredDeRhamHypercohomology surfaceVariety 2 2`. This is the source of the
filtered-to-de-Rham map; nonvanishing of its image is a separate question.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

instance surfaceVariety_smoothMorphism : Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

/-- The scheme-theoretic dimension of the actual self-product is two. -/
theorem dim_surface_eq_two : dim surface = 2 := by
  rw [TopologicalSpace.dim_eq_krullDim,
    SmoothOfRelativeDimension.orderKrullDim_eq_complex (f := surfaceToBase) (d := 2)]
  simp

/-- The filtered class of the global exterior product of the two elliptic differentials. -/
def surfaceTopFilteredClass : FilteredDeRhamHypercohomology surfaceVariety 2 2 :=
  topHolomorphicFormFilteredEquivOfDimension surfaceVariety 2 dim_surface_eq_two
    surfaceGlobalHolomorphicTwoForm

/-- The explicitly constructed class in the top filtered source group is nonzero. -/
theorem surfaceTopFilteredClass_ne_zero : surfaceTopFilteredClass ≠ 0 := by
  intro h
  apply surfaceGlobalHolomorphicTwoForm_ne_zero
  apply (topHolomorphicFormFilteredEquivOfDimension surfaceVariety 2
    dim_surface_eq_two).injective
  exact h.trans (topHolomorphicFormFilteredEquivOfDimension_zero surfaceVariety 2
    dim_surface_eq_two).symm

end AlgebraicGeometry.ExplicitEllipticCandidate
