/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexStandardEtale
public import HodgeConjecture.Lemmas.Analysis.MvPolynomialFactorHolomorphic

@[expose] public section

open scoped Polynomial

namespace AlgebraicGeometry.ComplexAlgHom

open Polynomial

noncomputable section

/-- The standard étale presentation of the simple-root locus of a monic polynomial family,
restricted to a principal open of the base. -/
def derivativeStandardEtalePair {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (t : complexPolynomialRing n) : StandardEtalePair (complexPolynomialRing n) where
  f := p
  monic_f := hp
  g := p.derivative * Polynomial.C t
  cond := ⟨Polynomial.C t, 0, 1, by simp⟩

@[simp]
lemma derivativeStandardEtalePair_f {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (t : complexPolynomialRing n) :
    (derivativeStandardEtalePair p hp t).f = p := rfl

@[simp]
lemma derivativeStandardEtalePair_g {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (t : complexPolynomialRing n) :
    (derivativeStandardEtalePair p hp t).g = p.derivative * Polynomial.C t := rfl

/-- The equations attached to `derivativeStandardEtalePair` are exactly the equation of the
polynomial family together with nonvanishing of the base function times the root derivative. -/
lemma derivativeStandardEtalePair_coordinate_condition {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (t : complexPolynomialRing n) (zw : (Fin n → ℂ) × ℂ) :
    (Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) zw.1).toRingHom zw.2
          (derivativeStandardEtalePair p hp t).f = 0 ∧
        Polynomial.eval₂ (MvPolynomial.aeval (R := ℂ) zw.1).toRingHom zw.2
          (derivativeStandardEtalePair p hp t).g ≠ 0) ↔
      mvFamilyEquation p zw = 0 ∧
        MvPolynomial.eval zw.1 t *
          (mvFamilySpecialization p zw.1).derivative.eval zw.2 ≠ 0 := by
  simp [derivativeStandardEtalePair, mvFamilyEquation, mvFamilySpecialization,
    Polynomial.eval_map, mul_comm]

/-- Complex points of the derivative standard étale algebra form the locus of individual simple
roots over the chosen principal open. -/
def derivativeStandardEtaleCoordinateHomeomorph {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (t : complexPolynomialRing n) :
    ((derivativeStandardEtalePair p hp t).Ring →ₐ[ℂ] ℂ) ≃ₜ
      MvSimpleRootLocusOn p t :=
  (standardEtaleCoordinateHomeomorph (derivativeStandardEtalePair p hp t)).trans <|
    Homeomorph.setCongr <| Set.ext fun zw ↦
      derivativeStandardEtalePair_coordinate_condition p hp t zw

end

end AlgebraicGeometry.ComplexAlgHom
