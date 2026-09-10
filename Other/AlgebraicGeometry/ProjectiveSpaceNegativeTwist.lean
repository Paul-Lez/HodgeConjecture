/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Other.AlgebraicGeometry.InvertiblePullback
public import Other.AlgebraicGeometry.ProjectiveSpectrumNegativeTwist

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Negative twists on the universal projective-space model

The coordinate basic opens of the universal homogeneous coordinate ring cover its projective
spectrum. Combining this fact with the general local homogeneous-fraction construction proves
that every `𝒪(-n)` is an invertible sheaf on the integral `Proj` model used to construct complex
projective space.
-/

@[expose] public noncomputable section

open scoped DirectSum Pointwise
open MvPolynomial

namespace AlgebraicGeometry.ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A standard homogeneous coordinate, bundled as an element of degree one. -/
def homogeneousCoordinate (N : ℕ) (i : Fin (N + 1)) : UniversalGrading N 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X (ULift ℤ) i⟩

/-- Every negative twist on the universal integral projective-space model is invertible. -/
theorem universalNegativeTwist_isInvertible (N n : ℕ) :
    TauCeti.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.NegativeTwist.schemeSheafOfModules (UniversalGrading N) n) := by
  apply ProjectiveSpectrum.NegativeTwist.isInvertible_of_degreeOneCover
    (UniversalGrading N) (homogeneousCoordinate N)
  exact iSup_coordinateBasicOpen_eq_top N

/-- The projection from complex projective space to the universal integral `Proj` model used in
its definition. -/
def toUniversalProj (N : ℕ) :
    ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ) ⟶ Proj (UniversalGrading N) :=
  CategoryTheory.Limits.pullback.snd
    (CategoryTheory.Limits.terminal.from (Spec ↧ℂ))
    (CategoryTheory.Limits.terminal.from (Proj (UniversalGrading N)))

/-- The algebraic negative twist on complex projective space, obtained by base change from the
universal integral model. -/
def negativeTwist (N n : ℕ) :
    (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ)).Modules :=
  (Scheme.Modules.pullback (toUniversalProj N)).obj
    (ProjectiveSpectrum.NegativeTwist.schemeSheafOfModules (UniversalGrading N) n)

/-- Every negative twist on complex projective space is an invertible sheaf. -/
theorem complexProjectiveNegativeTwist_isInvertible (N n : ℕ) :
    TauCeti.SheafOfModules.IsInvertible (negativeTwist N n) := by
  apply Scheme.Modules.pullback_isInvertible
  exact universalNegativeTwist_isInvertible N n

end AlgebraicGeometry.ComplexProjectiveSpace
