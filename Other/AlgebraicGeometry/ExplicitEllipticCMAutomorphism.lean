/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticDifferentials
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Complex multiplication on the explicit elliptic cubic

The affine coordinate substitution `x ↦ -x`, `y ↦ i y` preserves the cubic equation,
descends to an order-four automorphism of the actual Z-chart section ring, and acts on
the explicit invariant Kähler differential by the eigenvalue `i`.
-/

@[expose] public noncomputable section
open CategoryTheory MvPolynomial
namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ZPoly := MvPolynomial (Fin 2) ℂ
abbrev zIdeal : Ideal ZPoly :=
  Ideal.span (Set.range (fun _ : Unit =>
    chartEquation (Equiv.refl (Fin 3))))

def zCMPolynomialEnd : ZPoly →ₐ[ℂ] ZPoly :=
  MvPolynomial.aeval ![-X 0, C Complex.I * X 1]

@[simp] theorem zCMPolynomialEnd_X_zero :
    zCMPolynomialEnd (X 0) = -X 0 := by
  simp [zCMPolynomialEnd]

@[simp] theorem zCMPolynomialEnd_X_one :
    zCMPolynomialEnd (X 1) = C Complex.I * X 1 := by
  simp [zCMPolynomialEnd]

@[simp] theorem zCMPolynomialEnd_C (r : ℂ) :
    zCMPolynomialEnd (C r) = C r := by
  simp [zCMPolynomialEnd]

@[simp] theorem zCMPolynomialEnd_C_mul_X_one (r : ℂ) :
    zCMPolynomialEnd (C r * X 1) = C (r * Complex.I) * X 1 := by
  rw [map_mul, zCMPolynomialEnd_C, zCMPolynomialEnd_X_one,
    ← mul_assoc, ← map_mul]

theorem zCMPolynomialEnd_equation :
    zCMPolynomialEnd (chartEquation (Equiv.refl (Fin 3))) =
      -chartEquation (Equiv.refl (Fin 3)) := by
  rw [chartEquation_z]
  simp only [map_add, map_sub, map_pow, zCMPolynomialEnd_X_zero,
    zCMPolynomialEnd_X_one]
  rw [mul_pow, ← map_pow]
  simp [Complex.I_sq]
  ring

def zCMQuotientEnd : HypersurfaceRing (chartEquation (Equiv.refl (Fin 3))) →ₐ[ℂ]
    HypersurfaceRing (chartEquation (Equiv.refl (Fin 3))) :=
  Ideal.Quotient.liftₐ zIdeal
    ((Ideal.Quotient.mkₐ ℂ zIdeal).comp zCMPolynomialEnd)
    (by
      intro p hp
      change Ideal.Quotient.mk zIdeal (zCMPolynomialEnd p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp only [zIdeal, Set.range_const] at hp ⊢
      rw [Ideal.mem_span_singleton] at hp ⊢
      obtain ⟨q, rfl⟩ := hp
      rw [map_mul, zCMPolynomialEnd_equation]
      refine ⟨-zCMPolynomialEnd q, by ring⟩)

@[simp] theorem zCMQuotientEnd_mk (p : ZPoly) :
    zCMQuotientEnd (Ideal.Quotient.mk zIdeal p) =
      Ideal.Quotient.mk zIdeal (zCMPolynomialEnd p) := by
  exact Ideal.Quotient.lift_mk _ _ _

@[simp] theorem zCMQuotientEnd_coordinate_zero :
    zCMQuotientEnd (Ideal.Quotient.mk zIdeal (X 0)) =
      -Ideal.Quotient.mk zIdeal (X 0) := by simp

@[simp] theorem zCMQuotientEnd_coordinate_one :
    zCMQuotientEnd (Ideal.Quotient.mk zIdeal (X 1)) =
      Complex.I • Ideal.Quotient.mk zIdeal (X 1) := by
  simp only [zCMQuotientEnd_mk, zCMPolynomialEnd_X_one, map_mul]
  calc
    (Ideal.Quotient.mk zIdeal (C Complex.I)) *
        (Ideal.Quotient.mk zIdeal (X 1)) =
      algebraMap ℂ _ Complex.I * (Ideal.Quotient.mk zIdeal (X 1)) := by rfl
    _ = Complex.I • Ideal.Quotient.mk zIdeal (X 1) :=
      (Algebra.smul_def _ _).symm

theorem zCMPolynomialEnd_sq :
    zCMPolynomialEnd.comp zCMPolynomialEnd =
      MvPolynomial.aeval ![X 0, -X 1] := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  · simp [zCMPolynomialEnd]
  · simp only [AlgHom.comp_apply]
    erw [zCMPolynomialEnd_X_one]
    rw [zCMPolynomialEnd_C_mul_X_one, MvPolynomial.aeval_X]
    simp [Complex.I_sq]

theorem zCMPolynomialEnd_four :
    zCMPolynomialEnd.comp (zCMPolynomialEnd.comp
      (zCMPolynomialEnd.comp zCMPolynomialEnd)) = AlgHom.id ℂ ZPoly := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  · simp [zCMPolynomialEnd]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    erw [zCMPolynomialEnd_X_one]
    rw [zCMPolynomialEnd_C_mul_X_one, zCMPolynomialEnd_C_mul_X_one,
      zCMPolynomialEnd_C_mul_X_one]
    norm_num [Complex.I_sq]

theorem zCMQuotientEnd_four :
    zCMQuotientEnd.comp (zCMQuotientEnd.comp
      (zCMQuotientEnd.comp zCMQuotientEnd)) =
        AlgHom.id ℂ (HypersurfaceRing (chartEquation (Equiv.refl (Fin 3)))) := by
  apply Ideal.Quotient.algHom_ext ℂ
  change (Ideal.Quotient.mkₐ ℂ zIdeal).comp
      (zCMPolynomialEnd.comp (zCMPolynomialEnd.comp
        (zCMPolynomialEnd.comp zCMPolynomialEnd))) =
    (Ideal.Quotient.mkₐ ℂ zIdeal).comp (AlgHom.id ℂ ZPoly)
  rw [zCMPolynomialEnd_four]

def zCMQuotientAut :
    HypersurfaceRing (chartEquation (Equiv.refl (Fin 3))) ≃ₐ[ℂ]
      HypersurfaceRing (chartEquation (Equiv.refl (Fin 3))) :=
  AlgEquiv.ofBijective zCMQuotientEnd ⟨
    fun a b h => by
      have h' := congrArg (fun q => zCMQuotientEnd
        (zCMQuotientEnd (zCMQuotientEnd q))) h
      have hf := AlgHom.congr_fun zCMQuotientEnd_four a
      have hg := AlgHom.congr_fun zCMQuotientEnd_four b
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hf.symm.trans (h'.trans hg),
    fun a => ⟨(zCMQuotientEnd.comp (zCMQuotientEnd.comp zCMQuotientEnd)) a, by
      exact AlgHom.congr_fun zCMQuotientEnd_four a⟩⟩

/-- The CM automorphism transported to the actual section ring of the affine Z chart. -/
abbrev curveZOpen : curve.Opens :=
  curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3))

def curveZCMAlgEquiv : Γ(curve, curveZOpen) ≃ₐ[ℂ] Γ(curve, curveZOpen) :=
  (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime).symm.trans
    (zCMQuotientAut.trans
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime))

abbrev curveZCMEnd : Γ(curve, curveZOpen) →ₐ[ℂ] Γ(curve, curveZOpen) :=
  curveZCMAlgEquiv.toAlgHom

theorem curveZCMEnd_coordinate (p : ZPoly) :
    curveZCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) p) =
      hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
        (zCMPolynomialEnd p) := by
  simp [curveZCMEnd, curveZCMAlgEquiv, hypersurfaceCoordinateMap,
    zCMQuotientAut]

@[simp] theorem curveZCMEnd_coordinate_zero :
    curveZCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 0)) =
      -hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 0) := by
  rw [curveZCMEnd_coordinate, zCMPolynomialEnd_X_zero, map_neg]

@[simp] theorem curveZCMEnd_coordinate_one :
    curveZCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 1)) =
      Complex.I • hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 1) := by
  rw [curveZCMEnd_coordinate, zCMPolynomialEnd_X_one, map_mul]
  rw [show hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
      (C Complex.I) = algebraMap ℂ _ Complex.I by
    exact (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3))
        chartEquation_z_prime)).commutes Complex.I]
  exact (Algebra.smul_def _ _).symm

theorem curveZCMEnd_four :
    curveZCMEnd.comp (curveZCMEnd.comp (curveZCMEnd.comp curveZCMEnd)) =
      AlgHom.id ℂ Γ(curve, curveZOpen) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) a
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [curveZCMEnd_coordinate, curveZCMEnd_coordinate,
    curveZCMEnd_coordinate, curveZCMEnd_coordinate]
  exact congrArg (hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime))
    (AlgHom.congr_fun zCMPolynomialEnd_four p)

theorem zCMPolynomialEnd_zDifferentialB :
    zCMPolynomialEnd zDifferentialB = zDifferentialB := by
  simp only [zDifferentialB, map_mul, map_sub, map_ofNat, map_pow,
    zCMPolynomialEnd_C, zCMPolynomialEnd_X_zero]
  ring

theorem zCMPolynomialEnd_zDifferentialC :
    zCMPolynomialEnd zDifferentialC =
      -(C Complex.I * zDifferentialC) := by
  simp only [zDifferentialC, map_mul, map_neg, map_ofNat,
    zCMPolynomialEnd_C, zCMPolynomialEnd_X_zero,
    zCMPolynomialEnd_X_one]
  ring

/-- A distinct copy of the Z-chart ring, used to express a nonidentity algebra
endomorphism without conflicting with the canonical identity algebra instance. -/
structure CurveZRingCopy where
  down : Γ(curve, curveZOpen)

def curveZRingCopyEquiv : CurveZRingCopy ≃ Γ(curve, curveZOpen) where
  toFun := CurveZRingCopy.down
  invFun := CurveZRingCopy.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing CurveZRingCopy := curveZRingCopyEquiv.commRing

def curveZRingCopyRingEquiv : CurveZRingCopy ≃+* Γ(curve, curveZOpen) where
  __ := curveZRingCopyEquiv
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Algebra ℂ CurveZRingCopy :=
  (curveZRingCopyRingEquiv.symm.toRingHom.comp
    (algebraMap ℂ Γ(curve, curveZOpen))).toAlgebra

def curveZRingCopyAlgEquiv : CurveZRingCopy ≃ₐ[ℂ] Γ(curve, curveZOpen) where
  __ := curveZRingCopyRingEquiv
  commutes' _ := rfl

/-- The CM ring map factored through a distinct isomorphic copy. -/
def curveZCMToCopy :
    Γ(curve, curveZOpen) →ₐ[ℂ] CurveZRingCopy :=
  curveZRingCopyAlgEquiv.symm.toAlgHom.comp curveZCMEnd

def curveZCMFromCopy :
    CurveZRingCopy →ₐ[ℂ] Γ(curve, curveZOpen) :=
  curveZRingCopyAlgEquiv.toAlgHom

def curveZCMDifferentialToCopy :
    KaehlerDifferential ℂ Γ(curve, curveZOpen) →ₗ[ℂ]
      KaehlerDifferential ℂ CurveZRingCopy := by
  letI : Algebra Γ(curve, curveZOpen) CurveZRingCopy :=
    curveZCMToCopy.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(curve, curveZOpen) CurveZRingCopy :=
    IsScalarTower.of_algebraMap_eq' curveZCMToCopy.comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ Γ(curve, curveZOpen)
    CurveZRingCopy).restrictScalars ℂ

def curveZCMDifferentialFromCopy :
    KaehlerDifferential ℂ CurveZRingCopy →ₗ[ℂ]
      KaehlerDifferential ℂ Γ(curve, curveZOpen) := by
  letI : Algebra CurveZRingCopy Γ(curve, curveZOpen) :=
    curveZCMFromCopy.toRingHom.toAlgebra
  letI : IsScalarTower ℂ CurveZRingCopy Γ(curve, curveZOpen) :=
    IsScalarTower.of_algebraMap_eq' curveZCMFromCopy.comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ CurveZRingCopy
    Γ(curve, curveZOpen)).restrictScalars ℂ

/-- Pullback on Kähler differentials along the CM endomorphism of the Z chart. -/
def curveZCMDifferentialEnd :
    KaehlerDifferential ℂ Γ(curve, curveZOpen) →ₗ[ℂ]
      KaehlerDifferential ℂ Γ(curve, curveZOpen) :=
  curveZCMDifferentialFromCopy.comp curveZCMDifferentialToCopy

@[simp] theorem curveZCMDifferentialEnd_D (r : Γ(curve, curveZOpen)) :
    curveZCMDifferentialEnd (KaehlerDifferential.D ℂ _ r) =
      KaehlerDifferential.D ℂ _ (curveZCMEnd r) := by
  simp only [curveZCMDifferentialEnd, LinearMap.comp_apply,
    curveZCMDifferentialFromCopy, curveZCMDifferentialToCopy,
    LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
  rfl

theorem curveZCMDifferentialEnd_smul
    (r : Γ(curve, curveZOpen))
    (w : KaehlerDifferential ℂ Γ(curve, curveZOpen)) :
    curveZCMDifferentialEnd (r • w) =
      curveZCMEnd r • curveZCMDifferentialEnd w := by
  rw [curveZCMDifferentialEnd, LinearMap.comp_apply]
  change curveZCMDifferentialFromCopy
      (curveZCMDifferentialToCopy (r • w)) = _
  have h₁ : curveZCMDifferentialToCopy (r • w) =
      curveZCMToCopy r • curveZCMDifferentialToCopy w := by
    letI : Algebra Γ(curve, curveZOpen) CurveZRingCopy :=
      curveZCMToCopy.toRingHom.toAlgebra
    letI : IsScalarTower ℂ Γ(curve, curveZOpen) CurveZRingCopy :=
      IsScalarTower.of_algebraMap_eq' curveZCMToCopy.comp_algebraMap.symm
    exact (KaehlerDifferential.map ℂ ℂ Γ(curve, curveZOpen)
      CurveZRingCopy).map_smul r w
  rw [h₁]
  have h₂ : curveZCMDifferentialFromCopy
      (curveZCMToCopy r • curveZCMDifferentialToCopy w) =
      curveZCMFromCopy (curveZCMToCopy r) •
        curveZCMDifferentialFromCopy (curveZCMDifferentialToCopy w) := by
    letI : Algebra CurveZRingCopy Γ(curve, curveZOpen) :=
      curveZCMFromCopy.toRingHom.toAlgebra
    letI : IsScalarTower ℂ CurveZRingCopy Γ(curve, curveZOpen) :=
      IsScalarTower.of_algebraMap_eq' curveZCMFromCopy.comp_algebraMap.symm
    exact (KaehlerDifferential.map ℂ ℂ CurveZRingCopy
      Γ(curve, curveZOpen)).map_smul _ _
  rw [h₂]
  rfl

def curveZDifferentialCM :
    KaehlerDifferential ℂ Γ(curve, curveZOpen) :=
  hypersurfaceDifferential (chartEquation (Equiv.refl (Fin 3)))
    zDifferentialB zDifferentialC
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)

theorem curveZCMDifferentialEnd_curveZDifferential :
    curveZCMDifferentialEnd curveZDifferentialCM =
      Complex.I • curveZDifferentialCM := by
  unfold curveZDifferentialCM hypersurfaceDifferential
  rw [map_sub, curveZCMDifferentialEnd_smul,
    curveZCMDifferentialEnd_smul,
    curveZCMDifferentialEnd_D, curveZCMDifferentialEnd_D]
  rw [curveZCMEnd_coordinate, curveZCMEnd_coordinate,
    curveZCMEnd_coordinate, curveZCMEnd_coordinate]
  rw [zCMPolynomialEnd_zDifferentialC,
    zCMPolynomialEnd_zDifferentialB,
    zCMPolynomialEnd_X_zero, zCMPolynomialEnd_X_one]
  simp only [map_neg, map_mul]
  rw [show hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
      (C Complex.I) = algebraMap ℂ _ Complex.I by
    exact (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3))
        chartEquation_z_prime)).commutes Complex.I]
  rw [Derivation.leibniz]
  simp only [Derivation.map_algebraMap, zero_smul, zero_add]
  module

/-! ## The chart containing infinity -/

abbrev YPoly := MvPolynomial (Fin 2) ℂ

abbrev yIdeal : Ideal YPoly :=
  Ideal.span (Set.range (fun _ : Unit =>
    chartEquation (Equiv.swap (1 : Fin 3) 2)))

/-- On the chart normalized by Y = 1, the same projective automorphism is
u ↦ i u, v ↦ -i v. -/
def yCMPolynomialEnd : YPoly →ₐ[ℂ] YPoly :=
  MvPolynomial.aeval ![C Complex.I * X 0, -(C Complex.I * X 1)]

@[simp] theorem yCMPolynomialEnd_X_zero :
    yCMPolynomialEnd (X 0) = C Complex.I * X 0 := by
  simp [yCMPolynomialEnd]

@[simp] theorem yCMPolynomialEnd_X_one :
    yCMPolynomialEnd (X 1) = -(C Complex.I * X 1) := by
  simp [yCMPolynomialEnd]

@[simp] theorem yCMPolynomialEnd_C (r : ℂ) :
    yCMPolynomialEnd (C r) = C r := by
  simp [yCMPolynomialEnd]

theorem yCMPolynomialEnd_equation :
    yCMPolynomialEnd (chartEquation (Equiv.swap (1 : Fin 3) 2)) =
      -(C Complex.I *
        chartEquation (Equiv.swap (1 : Fin 3) 2)) := by
  rw [chartEquation_y]
  simp only [map_add, map_sub, map_mul, map_pow,
    yCMPolynomialEnd_X_zero, yCMPolynomialEnd_X_one]
  have hCI : (C Complex.I : YPoly) * C Complex.I = -1 := by
    rw [← map_mul]
    simp [Complex.I_sq]
  linear_combination
    (C Complex.I * (-X 0 ^ 3 + X 0 * X 1 ^ 2)) * hCI

def yCMQuotientEnd :
    HypersurfaceRing (chartEquation (Equiv.swap (1 : Fin 3) 2)) →ₐ[ℂ]
      HypersurfaceRing (chartEquation (Equiv.swap (1 : Fin 3) 2)) :=
  Ideal.Quotient.liftₐ yIdeal
    ((Ideal.Quotient.mkₐ ℂ yIdeal).comp yCMPolynomialEnd)
    (by
      intro p hp
      change Ideal.Quotient.mk yIdeal (yCMPolynomialEnd p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simp only [yIdeal, Set.range_const] at hp ⊢
      rw [Ideal.mem_span_singleton] at hp ⊢
      obtain ⟨q, rfl⟩ := hp
      rw [map_mul, yCMPolynomialEnd_equation]
      refine ⟨-(C Complex.I * yCMPolynomialEnd q), by ring⟩)

@[simp] theorem yCMQuotientEnd_mk (p : YPoly) :
    yCMQuotientEnd (Ideal.Quotient.mk yIdeal p) =
      Ideal.Quotient.mk yIdeal (yCMPolynomialEnd p) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem yCMPolynomialEnd_four :
    yCMPolynomialEnd.comp (yCMPolynomialEnd.comp
      (yCMPolynomialEnd.comp yCMPolynomialEnd)) = AlgHom.id ℂ YPoly := by
  apply MvPolynomial.algHom_ext
  intro j
  fin_cases j
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    erw [yCMPolynomialEnd_X_zero]
    simp only [map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_zero]
    simp only [map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_zero]
    simp only [map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_zero]
    have hCI : (C Complex.I : YPoly) * C Complex.I = -1 := by
      rw [← map_mul]
      simp [Complex.I_sq]
    calc
      C Complex.I * (C Complex.I *
          (C Complex.I * (C Complex.I * X (0 : Fin 2)))) =
        (C Complex.I * C Complex.I) *
          (C Complex.I * C Complex.I) * X (0 : Fin 2) := by ring
      _ = (-1 : YPoly) * (-1) * X (0 : Fin 2) := by
        rw [hCI]
      _ = X 0 := by ring
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    erw [yCMPolynomialEnd_X_one]
    simp only [map_neg, map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_one]
    simp only [map_neg, map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_one]
    simp only [map_neg, map_mul, yCMPolynomialEnd_C]
    erw [yCMPolynomialEnd_X_one]
    have hCI : (C Complex.I : YPoly) * C Complex.I = -1 := by
      rw [← map_mul]
      simp [Complex.I_sq]
    calc
      -(C Complex.I * -(C Complex.I *
          -(C Complex.I * -(C Complex.I * X (1 : Fin 2))))) =
        ((C Complex.I * C Complex.I) *
          (C Complex.I * C Complex.I)) * X (1 : Fin 2) := by ring
      _ = (-1 : YPoly) * (-1) * X (1 : Fin 2) := by
        rw [hCI]
      _ = X 1 := by ring

theorem yCMQuotientEnd_four :
    yCMQuotientEnd.comp (yCMQuotientEnd.comp
      (yCMQuotientEnd.comp yCMQuotientEnd)) =
        AlgHom.id ℂ
          (HypersurfaceRing
            (chartEquation (Equiv.swap (1 : Fin 3) 2))) := by
  apply Ideal.Quotient.algHom_ext ℂ
  change (Ideal.Quotient.mkₐ ℂ yIdeal).comp
      (yCMPolynomialEnd.comp (yCMPolynomialEnd.comp
        (yCMPolynomialEnd.comp yCMPolynomialEnd))) =
    (Ideal.Quotient.mkₐ ℂ yIdeal).comp (AlgHom.id ℂ YPoly)
  rw [yCMPolynomialEnd_four]

def yCMQuotientAut :
    HypersurfaceRing (chartEquation (Equiv.swap (1 : Fin 3) 2)) ≃ₐ[ℂ]
      HypersurfaceRing (chartEquation (Equiv.swap (1 : Fin 3) 2)) :=
  AlgEquiv.ofBijective yCMQuotientEnd ⟨
    fun a b h => by
      have h' := congrArg (fun q =>
        yCMQuotientEnd (yCMQuotientEnd (yCMQuotientEnd q))) h
      have hf := AlgHom.congr_fun yCMQuotientEnd_four a
      have hg := AlgHom.congr_fun yCMQuotientEnd_four b
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        hf.symm.trans (h'.trans hg),
    fun a =>
      ⟨(yCMQuotientEnd.comp
        (yCMQuotientEnd.comp yCMQuotientEnd)) a,
        AlgHom.congr_fun yCMQuotientEnd_four a⟩⟩

abbrev curveYOpen : curve.Opens :=
  curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2)

def curveYCMAlgEquiv : Γ(curve, curveYOpen) ≃ₐ[ℂ] Γ(curve, curveYOpen) :=
  (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime).symm.trans
    (yCMQuotientAut.trans
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime))

abbrev curveYCMEnd : Γ(curve, curveYOpen) →ₐ[ℂ] Γ(curve, curveYOpen) :=
  curveYCMAlgEquiv.toAlgHom

theorem curveYCMEnd_coordinate (p : YPoly) :
    curveYCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) p) =
      hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (yCMPolynomialEnd p) := by
  simp [curveYCMEnd, curveYCMAlgEquiv, hypersurfaceCoordinateMap,
    yCMQuotientAut]

@[simp] theorem curveYCMEnd_coordinate_zero :
    curveYCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (X 0)) =
      Complex.I • hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (X 0) := by
  rw [curveYCMEnd_coordinate, yCMPolynomialEnd_X_zero, map_mul]
  rw [show hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime) (C Complex.I) = algebraMap ℂ _ Complex.I by
    exact (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime)).commutes Complex.I]
  exact (Algebra.smul_def _ _).symm

@[simp] theorem curveYCMEnd_coordinate_one :
    curveYCMEnd (hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (X 1)) =
      -(Complex.I • hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (X 1)) := by
  rw [curveYCMEnd_coordinate, yCMPolynomialEnd_X_one, map_neg, map_mul]
  rw [show hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime) (C Complex.I) = algebraMap ℂ _ Complex.I by
    exact (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime)).commutes Complex.I]
  exact congrArg Neg.neg (Algebra.smul_def _ _).symm

theorem curveYCMEnd_four :
    curveYCMEnd.comp (curveYCMEnd.comp (curveYCMEnd.comp curveYCMEnd)) =
      AlgHom.id ℂ Γ(curve, curveYOpen) := by
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime) a
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [curveYCMEnd_coordinate, curveYCMEnd_coordinate,
    curveYCMEnd_coordinate, curveYCMEnd_coordinate]
  exact congrArg (hypersurfaceCoordinateMap
    (chartEquation (Equiv.swap (1 : Fin 3) 2))
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime))
    (AlgHom.congr_fun yCMPolynomialEnd_four p)

/-! ## Scheme automorphisms of the two affine charts -/

def curveZCMSchemeIso : curveZOpen.toScheme ≅ curveZOpen.toScheme := by
  have hZ : IsAffineOpen curveZOpen := by
    exact chart_isAffineOpen 2
  exact hZ.isoSpec ≪≫
    Scheme.Spec.mapIso
      curveZCMAlgEquiv.toRingEquiv.toCommRingCatIso.op ≪≫
    hZ.isoSpec.symm

def curveYCMSchemeIso : curveYOpen.toScheme ≅ curveYOpen.toScheme := by
  have hY : IsAffineOpen curveYOpen := by
    exact chart_isAffineOpen 1
  exact hY.isoSpec ≪≫
    Scheme.Spec.mapIso
      curveYCMAlgEquiv.toRingEquiv.toCommRingCatIso.op ≪≫
    hY.isoSpec.symm

end AlgebraicGeometry.ExplicitEllipticCandidate
