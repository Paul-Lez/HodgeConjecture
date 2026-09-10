/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticDifferentials

/-!
# The invariant differential trivializes the elliptic cotangent modules

For a smooth plane hypersurface equipped with an explicit Bezout identity, contraction with
the Hamiltonian derivation is inverse to multiplication by the corresponding invariant
differential.  Applying this to the two affine charts of the explicit cubic gives actual
rank-one trivializations of their Kahler differential modules.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Hypersurface

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Multiplication by the explicit invariant differential. -/
def hypersurfaceDifferentialMultiplication (f b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) :
    S →ₗ[S] KaehlerDifferential R S where
  toFun s := s • hypersurfaceDifferential f b c e
  map_add' s t := add_smul s t _
  map_smul' s t := by simp [mul_smul]

/-- Contract a differential with the Hamiltonian vector field, then multiply the invariant
differential by the resulting function. -/
def hypersurfaceDifferentialProjection (f b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) :
    KaehlerDifferential R S →ₗ[S] KaehlerDifferential R S :=
  (hypersurfaceDifferentialMultiplication f b c e).comp
    (hypersurfaceDerivation f e).liftKaehlerDifferential

theorem hypersurfaceDifferentialProjection_D_zero (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceDifferentialProjection f b c e
        (KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 0))) =
      KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 0)) := by
  simp only [hypersurfaceDifferentialProjection, LinearMap.comp_apply,
    hypersurfaceDifferentialMultiplication,
    Derivation.liftKaehlerDifferential_comp_D]
  change hypersurfaceDerivation f e (hypersurfaceCoordinateMap f e (X 0)) •
      hypersurfaceDifferential f b c e = _
  rw [hypersurfaceDerivation_coordinate, hamiltonianDerivation_X_zero,
    hypersurfaceDifferential_smul_y f a b c e h]

theorem hypersurfaceDifferentialProjection_D_one (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceDifferentialProjection f b c e
        (KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 1))) =
      KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 1)) := by
  simp only [hypersurfaceDifferentialProjection, LinearMap.comp_apply,
    hypersurfaceDifferentialMultiplication,
    Derivation.liftKaehlerDifferential_comp_D]
  change hypersurfaceDerivation f e (hypersurfaceCoordinateMap f e (X 1)) •
      hypersurfaceDifferential f b c e = _
  rw [hypersurfaceDerivation_coordinate, hamiltonianDerivation_X_one]
  rw [map_neg, neg_smul, hypersurfaceDifferential_smul_x f a b c e h, neg_neg]

/-- The invariant-differential projection fixes every Kahler differential. -/
theorem hypersurfaceDifferentialProjection_eq_id (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceDifferentialProjection f b c e = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext s
  obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective f e s
  change hypersurfaceDifferentialProjection f b c e
      (KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e p)) =
    KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e p)
  rw [derivation_polynomial (KaehlerDifferential.D R S)
    (hypersurfaceCoordinateMap f e) p, map_add, map_smul, map_smul]
  change
    hypersurfaceCoordinateMap f e (pderiv 0 p) •
        hypersurfaceDifferentialProjection f b c e
          (KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 0))) +
      hypersurfaceCoordinateMap f e (pderiv 1 p) •
        hypersurfaceDifferentialProjection f b c e
          (KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 1))) = _
  rw [hypersurfaceDifferentialProjection_D_zero f a b c e h,
    hypersurfaceDifferentialProjection_D_one f a b c e h]

/-- Every Kahler differential is its Hamiltonian contraction times the invariant differential. -/
theorem hypersurfaceDifferential_eq_contraction_smul (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1)
    (w : KaehlerDifferential R S) :
    (hypersurfaceDerivation f e).liftKaehlerDifferential w •
        hypersurfaceDifferential f b c e = w := by
  exact LinearMap.congr_fun (hypersurfaceDifferentialProjection_eq_id f a b c e h) w

/-- The explicit invariant differential is a basis of the cotangent module. -/
def hypersurfaceDifferentialLinearEquiv (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    S ≃ₗ[S] KaehlerDifferential R S where
  toLinearMap := hypersurfaceDifferentialMultiplication f b c e
  invFun := (hypersurfaceDerivation f e).liftKaehlerDifferential
  left_inv s := by
    change (hypersurfaceDerivation f e).liftKaehlerDifferential
        (s • hypersurfaceDifferential f b c e) = s
    rw [map_smul, hypersurfaceDifferential_contraction f a b c e h, smul_eq_mul, mul_one]
  right_inv w := hypersurfaceDifferential_eq_contraction_smul f a b c e h w

@[simp]
theorem hypersurfaceDifferentialLinearEquiv_apply (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) (s : S) :
    hypersurfaceDifferentialLinearEquiv f a b c e h s =
      s • hypersurfaceDifferential f b c e := rfl

@[simp]
theorem hypersurfaceDifferentialLinearEquiv_symm_apply
    (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1)
    (w : KaehlerDifferential R S) :
    (hypersurfaceDifferentialLinearEquiv f a b c e h).symm w =
      (hypersurfaceDerivation f e).liftKaehlerDifferential w := rfl

end Hypersurface

/-- The regular cotangent module on the `Z ≠ 0` chart is freely generated by the invariant
differential. -/
def curveZCotangentLinearEquiv :
    Γ(curve, chart 2) ≃ₗ[Γ(curve, chart 2)]
      KaehlerDifferential ℂ Γ(curve, chart 2) :=
  hypersurfaceDifferentialLinearEquiv
    (chartEquation (Equiv.refl (Fin 3))) (C (1 / 4) * (18 * X 0))
    zDifferentialB zDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
    zDifferential_bezout

@[simp] theorem curveZCotangentLinearEquiv_one :
    curveZCotangentLinearEquiv 1 = curveZDifferential := by
  change (1 : Γ(curve, chart 2)) • curveZDifferential = curveZDifferential
  rw [one_smul]

/-- The regular cotangent module on the chart containing infinity is freely generated by the
sign-normalized invariant differential. -/
def curveYCotangentLinearEquiv :
    Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2))
      ≃ₗ[Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2))]
      KaehlerDifferential ℂ
        Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2)) :=
  (hypersurfaceDifferentialLinearEquiv
    (chartEquation (Equiv.swap (1 : Fin 3) 2)) (2 * X 1 ^ 3)
    yDifferentialB yDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
    yDifferential_bezout).trans
      (LinearEquiv.neg
        Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2)))

@[simp] theorem curveYCotangentLinearEquiv_apply
    (s : Γ(curve, chart 1)) :
    curveYCotangentLinearEquiv s = s • curveYDifferential := by
  rw [curveYCotangentLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.neg_apply, hypersurfaceDifferentialLinearEquiv_apply]
  rw [curveYDifferential, smul_neg]

@[simp] theorem curveYCotangentLinearEquiv_one :
    curveYCotangentLinearEquiv 1 = curveYDifferential := by
  rw [curveYCotangentLinearEquiv_apply, one_smul]

end AlgebraicGeometry.ExplicitEllipticCandidate
