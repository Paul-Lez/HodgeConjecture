/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# An explicit projective cubic and its self-product

This file constructs the closed subscheme of the complex projective plane cut out set-theoretically
by `Y²Z = X³ - XZ²`, with its induced vanishing-ideal subscheme structure. Its structure map is
projective and proper. Its self-product is also an actual scheme, with a proper structure map.

The associated Weierstrass equation has discriminant `64`. These constructions are preparation
for a geometric non-Hodge example. This file does not prove smoothness of the scheme, compute
its cohomology, or assign a Hodge structure to that cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Weierstrass equation `y² = x³ - x` over `ℂ`. -/
def equation : WeierstrassCurve ℂ := ⟨0, 0, 0, -1, 0⟩

/-- The equation is nonsingular according to the discriminant criterion. -/
theorem discriminant : equation.Δ = 64 := by
  norm_num [equation, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : equation.IsElliptic := by
  constructor
  rw [discriminant]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- The homogeneous cubic defining the example, first written over the integers. -/
def cubic : MvPolynomial (Fin 3) (ULift ℤ) :=
  X 1 ^ 2 * X 2 - X 0 ^ 3 + X 0 * X 2 ^ 2

/-- The defining equation is homogeneous of degree three. -/
theorem cubic_homogeneous : cubic.IsHomogeneous 3 := by
  unfold cubic
  exact (((isHomogeneous_X (ULift ℤ) (1 : Fin 3)).pow 2).mul
      (isHomogeneous_X (ULift ℤ) 2)).sub
    ((isHomogeneous_X (ULift ℤ) 0).pow 3) |>.add
      ((isHomogeneous_X (ULift ℤ) 0).mul ((isHomogeneous_X (ULift ℤ) 2).pow 2))

/-- The coefficient map used to view the integral equation over `ℂ`. -/
def integerToComplex : ULift ℤ →+* ℂ :=
  (Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom

/-- The homogeneous equation defining the scheme is the projective Weierstrass equation
whose discriminant was computed above. -/
theorem cubic_map_eq_weierstrass :
    cubic.map integerToComplex = equation.toProjective.polynomial := by
  simp [cubic, equation, WeierstrassCurve.Projective.polynomial]
  ring

/-- Every nonzero complex projective representative satisfying the displayed equation has
a nonvanishing partial derivative. This is a statement about polynomial points; the comparison
with scheme-theoretic smoothness is not proved here. -/
theorem projective_nonsingular (P : Fin 3 → ℂ) (hP0 : P ≠ 0)
    (hP : equation.toProjective.Equation P) : equation.toProjective.Nonsingular P := by
  by_cases hz : P 2 = 0
  · have hx : P 0 = 0 :=
      WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero hP hz
    have hy : P 1 ≠ 0 := by
      intro hy
      apply hP0
      rw [← WeierstrassCurve.Projective.fin3_def P, hx, hy, hz]
      exact WeierstrassCurve.Projective.fin3_def 0
    apply (WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero hz).2
    refine ⟨hP, Or.inr ?_⟩
    simpa [hx, equation] using pow_ne_zero 2 hy
  · apply (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz).2
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    exact (WeierstrassCurve.Projective.equation_of_Z_ne_zero hz).1 hP

/-- The complex base scheme. -/
def base : Scheme := Spec (CommRingCat.of ℂ)

/-- The projective plane over the integers used by `ProjectiveSpace`. -/
def integerPlane : Scheme := Proj (homogeneousSubmodule (Fin 3) (ULift ℤ))

/-- The complex projective plane. -/
def plane : Scheme := ProjectiveSpace (Fin 3) base

/-- The projection of the complex projective plane to the integral projective plane. -/
def planeToIntegerPlane : plane ⟶ integerPlane :=
  pullback.snd (terminal.from base) (terminal.from integerPlane)

/-- The closed cubic locus in the complex projective plane. -/
def cubicLocus : TopologicalSpace.Closeds plane :=
  ⟨planeToIntegerPlane ⁻¹'
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin 3) (ULift ℤ)) {cubic},
    (ProjectiveSpectrum.isClosed_zeroLocus _ _).preimage planeToIntegerPlane.continuous⟩

/-- The vanishing ideal sheaf of the cubic locus. -/
def cubicIdeal : plane.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal cubicLocus

/-- The explicit cubic as a scheme. -/
def curve : Scheme := cubicIdeal.subscheme

/-- The vanishing-ideal construction gives the cubic its reduced scheme structure. -/
instance : IsReduced curve := by
  change IsReduced cubicIdeal.subscheme
  rw [IsReduced.iff_of_openCover _ cubicIdeal.subschemeCover.openCover]
  intro U
  let U' : plane.affineOpens := U
  change IsReduced (Spec (CommRingCat.of (Γ(plane, U'.1) ⧸ cubicIdeal.ideal U')))
  rw [affine_isReduced_iff, ← Ideal.isRadical_iff_quotient_reduced]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- The closed embedding of the cubic in the complex projective plane. -/
def curveToPlane : curve ⟶ plane := cubicIdeal.subschemeι

instance : IsClosedImmersion curveToPlane := by
  exact inferInstanceAs (IsClosedImmersion cubicIdeal.subschemeι)

/-- The structure morphism of the cubic. -/
def curveToBase : curve ⟶ base :=
  curveToPlane ≫ ProjectiveSpace.toBase (Fin 3) base

/-- The cubic has its displayed projective presentation in projective dimension two. -/
instance : IsProjective curveToBase where
  nonempty_presentation := ⟨{
    ambientDimension := 2
    immersion := curveToPlane
    isClosedImmersion := by exact inferInstanceAs (IsClosedImmersion curveToPlane)
    immersion_toBase := rfl }⟩

instance : IsProper curveToBase := inferInstance

/-- The self-product of the explicit cubic over `ℂ`. -/
def surface : Scheme := pullback curveToBase curveToBase

/-- The structure morphism of the self-product. -/
def surfaceToBase : surface ⟶ base :=
  pullback.fst curveToBase curveToBase ≫ curveToBase

instance : IsProper surfaceToBase := by
  exact inferInstanceAs (IsProper (pullback.fst curveToBase curveToBase ≫ curveToBase))

end AlgebraicGeometry.ExplicitEllipticCandidate
