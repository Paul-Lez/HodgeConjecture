/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePresentationTwist

/-!
# The degree-zero projective twist

The explicit negative twists used by the projective GAGA development recover the structure
sheaf in degree zero. This file transports that comparison through base change to complex
projective space, through a chosen projective presentation, and finally through analytification.
It is the degree-zero base case for comparison of morphisms between finite twist sums.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

namespace ProjectiveSpectrum.NegativeTwist.DegreeZero

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The scheme-module form of `𝒪(0) ≅ 𝒪` on a projective spectrum. -/
def schemeUnitIso :
    SheafOfModules.unit (_root_.AlgebraicGeometry.«Proj» 𝒜).ringCatSheaf ≅
      ProjectiveSpectrum.NegativeTwist.schemeSheafOfModules 𝒜 0 := by
  change SheafOfModules.unit (ProjectiveSpectrum.NegativeTwist.ringSheaf 𝒜) ≅
    ProjectiveSpectrum.NegativeTwist.sheafOfModules 𝒜 0
  exact unitIso 𝒜

end ProjectiveSpectrum.NegativeTwist.DegreeZero

namespace ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit `𝒪(0)` on complex projective space is its structure sheaf. -/
def negativeTwistZeroIso (N : ℕ) :
    SheafOfModules.unit (ProjectiveSpace (Fin (N + 1)) (Spec ↧ℂ)).ringCatSheaf ≅
      negativeTwist N 0 :=
  (Scheme.Modules.pullbackUnitIso (toUniversalProj N)).symm ≪≫
    (Scheme.Modules.pullback (toUniversalProj N)).mapIso
      (ProjectiveSpectrum.NegativeTwist.DegreeZero.schemeUnitIso (UniversalGrading N))

end ComplexProjectiveSpace

namespace ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The presentation-induced algebraic `𝒪_X(0)` is the algebraic structure sheaf. -/
def algebraicZeroIso (P : ProjectiveSpace.Presentation X.hom) :
    SheafOfModules.unit X.left.ringCatSheaf ≅ algebraic X P 0 :=
  (Scheme.Modules.pullbackUnitIso P.immersion).symm ≪≫
    (Scheme.Modules.pullback P.immersion).mapIso
      (ComplexProjectiveSpace.negativeTwistZeroIso P.ambientDimension)

/-- The presentation-induced analytic `𝒪_X(0)` is the holomorphic structure sheaf. -/
def analyticZeroIso (P : ProjectiveSpace.Presentation X.hom) :
    SheafOfModules.unit (holomorphicRingSheaf X d) ≅ analytic X d P 0 :=
  (moduleAnalytificationUnitIso X d).symm ≪≫
    (moduleAnalytification X d).mapIso (algebraicZeroIso X P)

end ComplexPoint.ProjectiveTwist

end AlgebraicGeometry
