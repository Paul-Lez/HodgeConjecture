/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationRestriction
public import Other.AlgebraicGeometry.ProjectiveSpaceNegativeTwist

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Negative twists induced by a projective presentation

An explicit projective presentation embeds a complex scheme into some `ℙⁿ_ℂ`.  This file
pulls the algebraic negative twists on that ambient projective space back to the scheme and then
analytifies them.  Both operations preserve invertibility.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

namespace ProjectiveTwist

/-- The algebraic `𝒪(-n)` on `X` selected by an explicit projective presentation. -/
def algebraic (P : ProjectiveSpace.Presentation X.hom) (n : ℕ) : X.left.Modules :=
  (Scheme.Modules.pullback P.immersion).obj
    (ComplexProjectiveSpace.negativeTwist P.ambientDimension n)

/-- A presentation-induced algebraic negative twist is invertible. -/
theorem algebraic_isInvertible (P : ProjectiveSpace.Presentation X.hom) (n : ℕ) :
    TauCeti.SheafOfModules.IsInvertible (algebraic X P n) := by
  apply Scheme.Modules.pullback_isInvertible
  exact ComplexProjectiveSpace.complexProjectiveNegativeTwist_isInvertible
    P.ambientDimension n

/-- The analytic `𝒪(-n)` on `Xᵃⁿ` obtained by analytifying the presentation-induced algebraic
twist. -/
def analytic (P : ProjectiveSpace.Presentation X.hom) (n : ℕ) :
    SheafOfModules (holomorphicRingSheaf X d) :=
  (moduleAnalytification X d).obj (algebraic X P n)

/-- A presentation-induced analytic negative twist is invertible. -/
theorem analytic_isInvertible (P : ProjectiveSpace.Presentation X.hom) (n : ℕ) :
    TauCeti.SheafOfModules.IsInvertible (analytic X d P n) :=
  moduleAnalytification_isInvertible X d (algebraic X P n)
    (algebraic_isInvertible X P n)

/-- The analytification comparison for a presentation-induced twist is the identity
isomorphism. This named interface lets later Serre-presentation statements refer to the analytic
and algebraic forms without unfolding either construction. -/
def analytificationIso (P : ProjectiveSpace.Presentation X.hom) (n : ℕ) :
    (moduleAnalytification X d).obj (algebraic X P n) ≅ analytic X d P n :=
  Iso.refl _

end ProjectiveTwist

end AlgebraicGeometry.ComplexPoint
