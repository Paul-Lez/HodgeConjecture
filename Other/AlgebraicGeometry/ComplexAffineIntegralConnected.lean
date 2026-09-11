/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module


public import Other.AlgebraicGeometry.ComplexLocalizationConnectedness
public import Other.RingTheory.IntegralPrimitiveElement

@[expose] public section

open scoped Polynomial Topology
open Set

namespace AlgebraicGeometry.ComplexAlgHom

open Polynomial

noncomputable section

/-- The complete connectedness assembly after choosing the normalization presentation. The two
nonzero localization parameters feed the smooth localization descent theorem. -/
theorem connectedSpace_of_localized_irreducible_hypersurface
    {n : ℕ} {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.Smooth ℂ A]
    [Algebra (complexPolynomialRing n) A]
    [IsScalarTower ℂ (complexPolynomialRing n) A]
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic) (hirr : Irreducible p)
    (a : A) (r : complexPolynomialRing n) (hr : r ≠ 0)
    (ha : a ≠ 0)
    (e : Localization.Away a ≃ₐ[complexPolynomialRing n]
      Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r)) :
    ConnectedSpace (A →ₐ[ℂ] ℂ) := by
  let ρ := mvRamificationPolynomial p
  have hρ : ρ ≠ 0 := mvRamificationPolynomial_ne_zero_of_irreducible hp hirr
  have hdeg : 0 < p.natDegree := hp.natDegree_pos_of_not_isUnit hirr.not_isUnit
  let C := Localization.Away
    (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r)
  let y : C := algebraMap (AdjoinRoot p) C (derivativeAdjoinRootElement p ρ)
  let z : Localization.Away a := e.symm y
  have hz : z ≠ 0 :=
    symm_algebraMap_derivativeAdjoinRootElement_ne_zero p hp hirr hdeg r ρ hr hρ e
  let e₂P := transportedIteratedAwayEquivDerivativeStandardEtale p hp r ρ e
  let e₂ : Localization.Away z ≃ₐ[ℂ]
      (derivativeStandardEtalePair p hp (r * ρ)).Ring :=
    e₂P.restrictScalars ℂ
  let _ : ConnectedSpace (MvSimpleRootLocusOn p (r * ρ)) :=
    connectedSpace_mvSimpleRootLocusOn_mul_mvRamificationPolynomial hp hirr r hr
  let _ : ConnectedSpace
      ((derivativeStandardEtalePair p hp (r * ρ)).Ring →ₐ[ℂ] ℂ) :=
    (derivativeStandardEtaleCoordinateHomeomorph p hp (r * ρ)).connectedSpace_iff.mpr
      inferInstance
  let _ : ConnectedSpace (Localization.Away z →ₐ[ℂ] ℂ) :=
    (precompAlgEquivHomeomorph e₂).connectedSpace_iff.mp inferInstance
  exact connectedSpace_affineAlgHom_of_two_smooth_localizations A a ha z hz


/-- Complex points of a smooth integral finite-type affine complex algebra form a connected
space. -/
theorem connectedSpace_complexAlgHom_of_smooth_integral
    (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A] :
    ConnectedSpace (A →ₐ[ℂ] ℂ) := by
  obtain ⟨N⟩ := Algebra.exists_complexNoetherNormalization A
  let P := complexPolynomialRing N.dimension
  let _ : Algebra P A := N.hom.toAlgebra
  let _ : IsScalarTower ℂ P A := IsScalarTower.of_algebraMap_eq fun x ↦ (N.hom.commutes x).symm
  obtain ⟨a, y, r, hy, hyIntegral, hyPrimitive, hyMem, hadjoin, hp, hirr,
      hadjoinRoot, ⟨e⟩⟩ := N.exists_primitive_numerator_localized_presentation
  let p := minpoly P y
  have hr : (r : P) ≠ 0 := nonZeroDivisors.ne_zero r.property
  have ha : N.hom (r : P) ≠ 0 := by
    simpa only [map_zero] using N.injective.ne hr
  exact connectedSpace_of_localized_irreducible_hypersurface p hp hirr
    (N.hom (r : P)) (r : P) hr ha e

end

end AlgebraicGeometry.ComplexAlgHom
