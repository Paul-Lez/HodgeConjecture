/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurface
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Regular differentials on the actual elliptic affine charts

The Hamiltonian derivation of a plane equation descends to its quotient and contracts the
explicit Bézout differential to one. Transporting along the proved chart equivalences produces
nonzero Kähler differentials on the actual section rings of the two affine opens of the cubic.
These are local regular forms; gluing and comparison with analytic cohomology are separate steps.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Hypersurface

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The polynomial vector field tangent to a plane equation. -/
def hamiltonianDerivation (f : MvPolynomial (Fin 2) R) :
    Derivation R (MvPolynomial (Fin 2) R) (MvPolynomial (Fin 2) R) :=
  pderiv 1 f • pderiv 0 - pderiv 0 f • pderiv 1

@[simp]
theorem hamiltonianDerivation_equation (f : MvPolynomial (Fin 2) R) :
    hamiltonianDerivation f f = 0 := by
  simp [hamiltonianDerivation, mul_comm]

@[simp]
theorem hamiltonianDerivation_X_zero (f : MvPolynomial (Fin 2) R) :
    hamiltonianDerivation f (X 0) = pderiv 1 f := by
  simp [hamiltonianDerivation]

@[simp]
theorem hamiltonianDerivation_X_one (f : MvPolynomial (Fin 2) R) :
    hamiltonianDerivation f (X 1) = -pderiv 0 f := by
  simp [hamiltonianDerivation]

/-- The quotient presentation, followed by the specified actual coordinate-ring equivalence. -/
def hypersurfaceCoordinateMap (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) : MvPolynomial (Fin 2) R →ₐ[R] S :=
  e.toAlgHom.comp (Ideal.Quotient.mkₐ R _)

@[simp]
theorem hypersurfaceCoordinateMap_equation (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) : hypersurfaceCoordinateMap f e f = 0 := by
  change e (Ideal.Quotient.mk _ f) = 0
  have hf : Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => f))) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(), rfl⟩)
  rw [hf, map_zero]

theorem hypersurfaceCoordinateMap_surjective (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) : Function.Surjective (hypersurfaceCoordinateMap f e) :=
  e.surjective.comp Ideal.Quotient.mk_surjective

theorem hamiltonianDerivation_preserves_kernel (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) (g : MvPolynomial (Fin 2) R)
    (hg : hypersurfaceCoordinateMap f e g = 0) :
    hypersurfaceCoordinateMap f e (hamiltonianDerivation f g) = 0 := by
  have hg' : Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => f))) g = 0 :=
    e.injective (hg.trans (map_zero e).symm)
  rw [Ideal.Quotient.eq_zero_iff_mem, Set.range_const, Ideal.mem_span_singleton] at hg'
  obtain ⟨q, rfl⟩ := hg'
  simp [Derivation.leibniz]

/-- The tangent vector field on the actual hypersurface section ring. -/
def hypersurfaceDerivation (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) : Derivation R S S :=
  Derivation.liftOfSurjective (hypersurfaceCoordinateMap_surjective f e)
    (hamiltonianDerivation_preserves_kernel f e)

@[simp]
theorem hypersurfaceDerivation_coordinate (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) (g : MvPolynomial (Fin 2) R) :
    hypersurfaceDerivation f e (hypersurfaceCoordinateMap f e g) =
      hypersurfaceCoordinateMap f e (hamiltonianDerivation f g) :=
  Derivation.liftOfSurjective_apply _ (hamiltonianDerivation_preserves_kernel f e) _

/-- A polynomial expression for the invariant differential, with no denominators on the chart. -/
def hypersurfaceDifferential (f b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) : KaehlerDifferential R S :=
  hypersurfaceCoordinateMap f e c • KaehlerDifferential.D R S
      (hypersurfaceCoordinateMap f e (X 0)) -
    hypersurfaceCoordinateMap f e b • KaehlerDifferential.D R S
      (hypersurfaceCoordinateMap f e (X 1))

/-- The polynomial chain rule for a derivation and two affine coordinate functions. -/
theorem derivation_polynomial {M : Type*} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (D : Derivation R S M)
    (φ : MvPolynomial (Fin 2) R →ₐ[R] S) (f : MvPolynomial (Fin 2) R) :
    D (φ f) = φ (pderiv 0 f) • D (φ (X 0)) + φ (pderiv 1 f) • D (φ (X 1)) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp
  | add f g hf hg => simp [hf, hg, add_smul]; module
  | mul_X f j hf =>
      fin_cases j <;> simp [Derivation.leibniz, hf, add_smul, mul_smul] <;> module

/-- The differential of the actual equation vanishes in its quotient. -/
theorem hypersurfaceDifferential_relation (f : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S) :
    hypersurfaceCoordinateMap f e (pderiv 0 f) •
        KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 0)) +
      hypersurfaceCoordinateMap f e (pderiv 1 f) •
        KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 1)) = 0 := by
  rw [← derivation_polynomial, hypersurfaceCoordinateMap_equation, map_zero]

/-- Multiplying by `F_y` gives `dx`, including at points where `F_y` vanishes. -/
theorem hypersurfaceDifferential_smul_y (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceCoordinateMap f e (pderiv 1 f) • hypersurfaceDifferential f b c e =
      KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 0)) := by
  have hh := congrArg (hypersurfaceCoordinateMap f e) h
  simp only [map_add, map_mul, map_one, hypersurfaceCoordinateMap_equation, mul_zero,
    zero_add] at hh
  let φ := hypersurfaceCoordinateMap f e
  change φ (pderiv 1 f) • (φ c • KaehlerDifferential.D R S (φ (X 0)) -
    φ b • KaehlerDifferential.D R S (φ (X 1))) = _
  calc
    _ = (φ b * φ (pderiv 0 f) + φ c * φ (pderiv 1 f)) •
        KaehlerDifferential.D R S (φ (X 0)) - φ b •
        (φ (pderiv 0 f) • KaehlerDifferential.D R S (φ (X 0)) +
         φ (pderiv 1 f) • KaehlerDifferential.D R S (φ (X 1))) := by module
    _ = _ := by rw [hh, hypersurfaceDifferential_relation, smul_zero, sub_zero, one_smul]

/-- Multiplying by `F_x` gives `-dy`. Together the two formulas trivialize the cotangent line. -/
theorem hypersurfaceDifferential_smul_x (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceCoordinateMap f e (pderiv 0 f) • hypersurfaceDifferential f b c e =
      -KaehlerDifferential.D R S (hypersurfaceCoordinateMap f e (X 1)) := by
  have hh := congrArg (hypersurfaceCoordinateMap f e) h
  simp only [map_add, map_mul, map_one, hypersurfaceCoordinateMap_equation, mul_zero,
    zero_add] at hh
  let φ := hypersurfaceCoordinateMap f e
  change φ (pderiv 0 f) • (φ c • KaehlerDifferential.D R S (φ (X 0)) -
    φ b • KaehlerDifferential.D R S (φ (X 1))) = _
  calc
    _ = φ c • (φ (pderiv 0 f) • KaehlerDifferential.D R S (φ (X 0)) +
         φ (pderiv 1 f) • KaehlerDifferential.D R S (φ (X 1))) -
      (φ b * φ (pderiv 0 f) + φ c * φ (pderiv 1 f)) •
        KaehlerDifferential.D R S (φ (X 1)) := by module
    _ = _ := by rw [hh, hypersurfaceDifferential_relation, smul_zero, one_smul, zero_sub]

/-- The explicit differential pairs to one with the actual descended vector field. -/
theorem hypersurfaceDifferential_contraction (f a b c : MvPolynomial (Fin 2) R)
    (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    (hypersurfaceDerivation f e).liftKaehlerDifferential
      (hypersurfaceDifferential f b c e) = 1 := by
  simp only [hypersurfaceDifferential, map_sub, map_smul,
    Derivation.liftKaehlerDifferential_comp_D, hypersurfaceDerivation_coordinate,
    hamiltonianDerivation_X_zero, hamiltonianDerivation_X_one, map_neg, smul_eq_mul,
    mul_neg, sub_neg_eq_add]
  have hh := congrArg (hypersurfaceCoordinateMap f e) h
  simp only [map_add, map_mul, map_one, hypersurfaceCoordinateMap_equation, mul_zero,
    zero_add] at hh
  simpa only [add_comm, mul_comm] using hh

/-- In particular this is a nonzero regular differential on a nonempty hypersurface chart. -/
theorem hypersurfaceDifferential_ne_zero [Nontrivial S]
    (f a b c : MvPolynomial (Fin 2) R) (e : HypersurfaceRing f ≃ₐ[R] S)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    hypersurfaceDifferential f b c e ≠ 0 := by
  intro hz
  have hc := hypersurfaceDifferential_contraction f a b c e h
  rw [hz, map_zero] at hc
  exact zero_ne_one hc

end Hypersurface

/-- Polynomial coefficients for the regular differential on `Z ≠ 0`. -/
def zDifferentialB : MvPolynomial (Fin 2) ℂ := C (1 / 4) * (4 - 6 * X 0 ^ 2)
def zDifferentialC : MvPolynomial (Fin 2) ℂ := C (1 / 4) * (-9 * X 0 * X 1)

theorem zDifferential_bezout :
    (C (1 / 4) * (18 * X 0)) * chartEquation (Equiv.refl (Fin 3)) +
      zDifferentialB * pderiv 0 (chartEquation (Equiv.refl (Fin 3))) +
      zDifferentialC * pderiv 1 (chartEquation (Equiv.refl (Fin 3))) = 1 := by
  simp [zDifferentialB, zDifferentialC]
  calc
    _ = C (1 / 4 : ℂ) * 4 := by ring_nf
    _ = 1 := by rw [← map_ofNat C 4, ← map_mul]; norm_num

/-- Polynomial coefficients for the differential on the chart containing infinity. -/
def yDifferentialB : MvPolynomial (Fin 2) ℂ := -X 1 ^ 2
def yDifferentialC : MvPolynomial (Fin 2) ℂ :=
  X 0 ^ 2 * X 1 ^ 2 - X 1 ^ 4 - 2 * X 0 * X 1 + 1

theorem yDifferential_bezout :
    (2 * X 1 ^ 3) * chartEquation (Equiv.swap (1 : Fin 3) 2) +
      yDifferentialB * pderiv 0 (chartEquation (Equiv.swap (1 : Fin 3) 2)) +
      yDifferentialC * pderiv 1 (chartEquation (Equiv.swap (1 : Fin 3) 2)) = 1 := by
  simp [yDifferentialB, yDifferentialC]
  ring_nf

/-- The regular differential on the actual coordinate ring of the `Z` open of the curve. -/
def curveZDifferential : KaehlerDifferential ℂ Γ(curve, chart 2) :=
  hypersurfaceDifferential (chartEquation (Equiv.refl (Fin 3))) zDifferentialB zDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)

/-- The regular differential on the actual coordinate ring of the infinity open. The sign is
chosen so its rational expression agrees with `dx/(2y)` from the other chart. -/
def curveYDifferential : KaehlerDifferential ℂ Γ(curve, chart 1) :=
  -hypersurfaceDifferential (chartEquation (Equiv.swap (1 : Fin 3) 2)) yDifferentialB yDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)

theorem curveZDifferential_ne_zero : curveZDifferential ≠ 0 :=
  hypersurfaceDifferential_ne_zero _ _ _ _ _ zDifferential_bezout

theorem curveYDifferential_ne_zero : curveYDifferential ≠ 0 := by
  apply neg_ne_zero.mpr
  have : Nontrivial Γ(curve, curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2)) :=
    inferInstanceAs (Nontrivial Γ(curve, chart 1))
  exact hypersurfaceDifferential_ne_zero _ _ _ _ _ yDifferential_bezout

end AlgebraicGeometry.ExplicitEllipticCandidate
