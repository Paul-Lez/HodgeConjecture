/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurface
public import Other.AlgebraicGeometry.ExplicitSegreMorphism
public import Other.AlgebraicGeometry.ExplicitProjectiveRelabeling

/-!
# The Segre morphism of the constructed elliptic self-product

This constructs an actual morphism from the integral smooth self-product into projective
8-space over the complex numbers. The morphism is defined from the two actual curve projections
and the regular coordinate-ratio construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The first projective-plane coordinate map of the actual elliptic self-product. -/
def surfaceFirstPlane : surface ⟶ integerPlane :=
  pullback.fst curveToBase curveToBase ≫ curveToIntegerPlane

/-- The second projective-plane coordinate map of the actual elliptic self-product. -/
def surfaceSecondPlane : surface ⟶ integerPlane :=
  pullback.snd curveToBase curveToBase ≫ curveToIntegerPlane

/-- The canonical integral coefficients in the surface's regular functions. -/
def surfaceIntegerScalar : ULift.{0} ℤ →+* Γ(surface, ⊤) :=
  (Int.castRingHom Γ(surface, ⊤)).comp ULift.ringEquiv.toRingHom

/-- The Segre morphism on the integral projective-spectrum models. -/
def surfaceToIntegerMatrixSpace : surface ⟶
    Proj (homogeneousSubmodule (Fin 3 × Fin 3) (ULift.{0} ℤ)) :=
  SegreMorphism.fromMaps (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane

/-- Reindex the nine matrix coordinates by `Fin 9`. -/
def surfaceToIntegerP8 : surface ⟶ Proj (homogeneousSubmodule (Fin 9) (ULift.{0} ℤ)) :=
  surfaceToIntegerMatrixSpace ≫ (ProjectiveRelabeling.iso (ULift.{0} ℤ) finProdFinEquiv).hom

/-- The actual Segre morphism of the surface into complex projective eight-space. -/
def surfaceSegre : surface ⟶ ProjectiveSpace (Fin 9) base :=
  pullback.lift surfaceToBase surfaceToIntegerP8 (Subsingleton.elim _ _)

/-- The constructed Segre morphism is over the complex base. -/
@[reassoc] theorem surfaceSegre_toBase :
    surfaceSegre ≫ ProjectiveSpace.toBase (Fin 9) base = surfaceToBase :=
  pullback.lift_fst _ _ _

/-- On every simultaneous coordinate chart, the morphism is given by the products of the
actual regular coordinate ratios of the two elliptic factors. -/
@[reassoc] theorem surfaceToIntegerMatrixSpace_chart (p : Fin 3 × Fin 3) :
    (SegreMorphism.chart (ULift.{0} ℤ) surfaceFirstPlane surfaceSecondPlane p).ι ≫
      surfaceToIntegerMatrixSpace =
    SegreMorphism.localMap (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane p :=
  SegreMorphism.chart_ι_fromMaps (ULift.{0} ℤ) surfaceIntegerScalar surfaceFirstPlane surfaceSecondPlane p

end AlgebraicGeometry.ExplicitEllipticCandidate
