/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Other.AlgebraicGeometry.ComplexDerivativeStandardEtale

@[expose] public section

open scoped Polynomial

namespace AlgebraicGeometry.ComplexAlgHom

open Polynomial

noncomputable section

/-- Transport one further localization across an algebra equivalence.  This keeps the iterated
localization visible, which is useful when descending connectedness one dense map at a time. -/
def iteratedAwayAlgEquivOfAlgEquiv
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) (y : C) :
    Localization.Away (e.symm y) ≃ₐ[R] Localization.Away y :=
  IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (e.symm y)) (T := Submonoid.powers y)
    (Localization.Away (e.symm y)) (Localization.Away y) e
    (by
      rw [Submonoid.map_powers]
      simp)

/-- Nonvanishing of the element used for the second localization transports back across the
normalization equivalence. -/
lemma iteratedAwayAlgEquivOfAlgEquiv_symm_ne_zero
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C) {y : C} (hy : y ≠ 0) :
    e.symm y ≠ 0 := by
  simpa only [map_zero] using e.symm.injective.ne hy

variable {n : ℕ}

def derivativeAdjoinRootElement
    (p : Polynomial (complexPolynomialRing n)) (t : complexPolynomialRing n) :
    AdjoinRoot p :=
  AdjoinRoot.mk p (p.derivative * Polynomial.C t)

/-- After first localizing `AdjoinRoot p` at a base element `r`, and then at the image of
`p' * ρ`, the resulting ring is a localization of `AdjoinRoot p` at `p' * (r * ρ)`. -/
lemma iteratedAway_isLocalization_derivative_mul_base
    (p : Polynomial (complexPolynomialRing n))
    (r ρ : complexPolynomialRing n) :
    let AR := AdjoinRoot p
    let C := Localization.Away (algebraMap (complexPolynomialRing n) AR r)
    let y : C := algebraMap AR C (derivativeAdjoinRootElement p ρ)
    let T := Localization.Away y
    IsLocalization.Away (derivativeAdjoinRootElement p (r * ρ)) T := by
  dsimp only
  let AR := AdjoinRoot p
  let C := Localization.Away (algebraMap (complexPolynomialRing n) AR r)
  let y : C := algebraMap AR C (derivativeAdjoinRootElement p ρ)
  let T := Localization.Away y
  have hloc := IsLocalization.Away.mul C T
    (algebraMap (complexPolynomialRing n) AR r) (derivativeAdjoinRootElement p ρ)
  rw [show derivativeAdjoinRootElement p (r * ρ) =
      derivativeAdjoinRootElement p ρ * algebraMap (complexPolynomialRing n) AR r by
    simp [derivativeAdjoinRootElement, map_mul]
    rw [show algebraMap (complexPolynomialRing n) AR r = AdjoinRoot.of p r from rfl]
    ring]
  exact hloc

/-- The twice-localized monogenic algebra is the derivative standard étale algebra for the
product of the old denominator and the new principal-open equation. -/
def iteratedAwayEquivDerivativeStandardEtale
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (r ρ : complexPolynomialRing n) :
    let AR := AdjoinRoot p
    let C := Localization.Away (algebraMap (complexPolynomialRing n) AR r)
    let y : C := algebraMap AR C (derivativeAdjoinRootElement p ρ)
    let T := Localization.Away y
    T ≃ₐ[complexPolynomialRing n] (derivativeStandardEtalePair p hp (r * ρ)).Ring := by
  dsimp only
  let AR := AdjoinRoot p
  let C := Localization.Away (algebraMap (complexPolynomialRing n) AR r)
  let y : C := algebraMap AR C (derivativeAdjoinRootElement p ρ)
  let T := Localization.Away y
  letI : IsLocalization.Away (derivativeAdjoinRootElement p (r * ρ)) T :=
    iteratedAway_isLocalization_derivative_mul_base p r ρ
  exact ((IsLocalization.algEquiv
    (Submonoid.powers (derivativeAdjoinRootElement p (r * ρ))) T
    (Localization.Away (derivativeAdjoinRootElement p (r * ρ)))).restrictScalars
      (complexPolynomialRing n)).trans
    (derivativeStandardEtalePair p hp (r * ρ)).equivAwayAdjoinRoot.symm

/-- Combining the normalization equivalence with one further localization identifies the
localized normalization algebra with the corresponding derivative standard étale algebra. -/
def transportedIteratedAwayEquivDerivativeStandardEtale
    {B : Type*} [CommRing B] [Algebra (complexPolynomialRing n) B]
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (r ρ : complexPolynomialRing n)
    (e : B ≃ₐ[complexPolynomialRing n]
      Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r)) :
    let C := Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r)
    let y : C := algebraMap (AdjoinRoot p) C (derivativeAdjoinRootElement p ρ)
    Localization.Away (e.symm y) ≃ₐ[complexPolynomialRing n]
      (derivativeStandardEtalePair p hp (r * ρ)).Ring := by
  dsimp only
  exact (iteratedAwayAlgEquivOfAlgEquiv e _).trans
    (iteratedAwayEquivDerivativeStandardEtale p hp r ρ)

end

end AlgebraicGeometry.ComplexAlgHom
