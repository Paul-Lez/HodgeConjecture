/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.MvPolynomialStandardSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Affine space is smooth of relative dimension `n`

Over an affine base, `𝔸ⁿ` is the spectrum of a polynomial ring, so its structure morphism is
standard smooth of relative dimension `n`.  This supplies the `SmoothOfRelativeDimension`
instance that the repository's complex-manifold machinery needs on complex affine space.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

namespace Other.AffineSpaceSmooth

/-- Affine `N`-space over an affine base is smooth of relative dimension `N`. -/
theorem smoothOfRelativeDimension_affineSpace (N : ℕ) (R : CommRingCat) :
    SmoothOfRelativeDimension N (AffineSpace (Fin N) (Spec R) ↘ Spec R) := by
  have hresp : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension N) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange N).respectsIso
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension N)
      (AffineSpace.SpecIso (Fin N) R).inv,
    AffineSpace.SpecIso_inv_over,
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension N)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  simp only [CommRingCat.hom_ofHom]
  rw [show (MvPolynomial.C : R →+* MvPolynomial (Fin N) R) =
      algebraMap R (MvPolynomial (Fin N) R) from rfl,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  infer_instance

/-- Complex affine `N`-space, as an object over `Spec ℂ`, is smooth of relative dimension `N`. -/
instance smoothOfRelativeDimension_complexAffineSpace (N : ℕ) :
    SmoothOfRelativeDimension N
      (Over.mk (AlgebraicGeometry.ComplexPoint.complexAffineSpace (Fin N) ↘ Spec ↧ℂ)).hom :=
  smoothOfRelativeDimension_affineSpace N ↧ℂ

end Other.AffineSpaceSmooth
