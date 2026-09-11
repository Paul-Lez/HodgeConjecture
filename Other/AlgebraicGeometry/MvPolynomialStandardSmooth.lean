/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Polynomial algebras are standard smooth

A polynomial algebra `MvPolynomial (Fin n) R` is standard smooth of relative dimension `n` over
`R`: the tautological generators `Algebra.Generators.mvPolynomial` have no relations, so the
Jacobian is the determinant of the empty matrix.  Mathlib records the generators and the
vanishing of their kernel but not the resulting submersive presentation.

This is the local model for smoothness of projective space: the standard affine charts of
`Proj` of a polynomial ring are spectra of polynomial algebras in one fewer variable.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Other.MvPolynomialStandardSmooth

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The tautological presentation of a polynomial algebra: the variables generate, and there are
no relations. -/
noncomputable def presentation :
    Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty where
  __ := Algebra.Generators.mvPolynomial R (Fin n)
  relation := Empty.elim
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_mvPolynomial]
    simp

/-- The tautological presentation, with the (empty) injection from relations to variables. -/
noncomputable def preSubmersive :
    Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty where
  __ := presentation R n
  map := Empty.elim
  map_inj := fun a ↦ a.elim

/-- The tautological presentation is submersive: with no relations the Jacobian is `1`. -/
noncomputable def submersive :
    Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty where
  __ := preSubmersive R n
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

@[simp]
theorem presentation_dimension : (presentation R n).dimension = n := by
  simp [Algebra.Presentation.dimension]

/-- A polynomial algebra in `n` variables is standard smooth of relative dimension `n`. -/
instance isStandardSmoothOfRelativeDimension :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) :=
  (submersive R n).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

end Other.MvPolynomialStandardSmooth
