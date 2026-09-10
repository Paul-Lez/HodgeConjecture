/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Module

/-!
# Eigenspace projectors for an order-four complex action

The two explicit projectors split a vector into its `i` and `-i` parts.  A nonzero vector fixed by
a compatible conjugation has both parts nonzero.  The final lemmas record how a bilinear external
product of two such `-i` parts gives a simultaneous `(-i,-i)` eigenvector and the exact condition
needed to exclude it from a proposed Hodge-filtration subspace.
-/

@[expose] public noncomputable section

namespace LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem eq_zero_of_nonzero_smul_eq_zero (a : ℂ) (ha : a ≠ 0) (v : V)
    (h : a • v = 0) : v = 0 := by
  have h' := congrArg (fun w : V => a⁻¹ • w) h
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] using h'

/-- The `i`-eigenpart associated to an order-four operator. -/
def cmPlusPart (J : V →ₗ[ℂ] V) (v : V) : V :=
  (1 / 2 : ℂ) • (v - Complex.I • J v)

/-- The `-i`-eigenpart associated to an order-four operator. -/
def cmMinusPart (J : V →ₗ[ℂ] V) (v : V) : V :=
  (1 / 2 : ℂ) • (v + Complex.I • J v)

/-- The two CM parts sum to the original vector. -/
theorem cmPlusPart_add_cmMinusPart (J : V →ₗ[ℂ] V) (v : V) :
    cmPlusPart J v + cmMinusPart J v = v := by
  simp only [cmPlusPart, cmMinusPart]
  module

/-- If `J² = -1`, the minus part is a `-i` eigenvector. -/
theorem map_cmMinusPart_of_sq_neg_one (J : V →ₗ[ℂ] V)
    (hJ : ∀ x, J (J x) = -x) (v : V) :
    J (cmMinusPart J v) = -Complex.I • cmMinusPart J v := by
  rw [cmMinusPart, map_smul, map_add, map_smul, hJ]
  simp only [smul_add, smul_smul]
  simp [smul_neg, ← mul_assoc]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- If `J² = -1`, the plus part is an `i` eigenvector. -/
theorem map_cmPlusPart_of_sq_neg_one (J : V →ₗ[ℂ] V)
    (hJ : ∀ x, J (J x) = -x) (v : V) :
    J (cmPlusPart J v) = Complex.I • cmPlusPart J v := by
  rw [cmPlusPart, map_smul, map_sub, map_smul, hJ]
  simp only [smul_sub, smul_smul]
  simp [smul_neg, ← mul_assoc]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- The minus projector vanishes exactly on the `i` eigenspace. -/
theorem cmMinusPart_eq_zero_iff (J : V →ₗ[ℂ] V) (v : V) :
    cmMinusPart J v = 0 ↔ J v = Complex.I • v := by
  constructor
  · intro h
    have h' : v + Complex.I • J v = 0 := by
      exact eq_zero_of_nonzero_smul_eq_zero (1 / 2 : ℂ) (by norm_num) _
        (by simpa [cmMinusPart] using h)
    have hI := congrArg (fun x : V => (-Complex.I) • x) h'
    simp only [smul_add, smul_zero] at hI
    have hII : (-Complex.I : ℂ) * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I]
      norm_num
    rw [smul_smul, hII, one_smul] at hI
    exact eq_neg_of_add_eq_zero_right hI |>.trans (by module)
  · intro h
    rw [cmMinusPart, h, smul_smul, Complex.I_mul_I]
    simp

/-- The plus projector vanishes exactly on the `-i` eigenspace. -/
theorem cmPlusPart_eq_zero_iff (J : V →ₗ[ℂ] V) (v : V) :
    cmPlusPart J v = 0 ↔ J v = -Complex.I • v := by
  constructor
  · intro h
    have h' : v - Complex.I • J v = 0 := by
      exact eq_zero_of_nonzero_smul_eq_zero (1 / 2 : ℂ) (by norm_num) _
        (by simpa [cmPlusPart] using h)
    have hI := congrArg (fun x : V => Complex.I • x) h'
    simp only [smul_sub, smul_zero, smul_smul] at hI
    rw [Complex.I_mul_I, neg_one_smul, sub_neg_eq_add] at hI
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_right hI
  · intro h
    rw [cmPlusPart, h, smul_smul]
    have hI : Complex.I * -Complex.I = 1 := by
      rw [mul_neg, Complex.I_mul_I]
      norm_num
    rw [hI, one_smul, sub_self, smul_zero]

/-- A nonzero conjugation-fixed vector has a nonzero `-i` part when conjugation commutes with `J`. -/
theorem cmMinusPart_ne_zero_of_conjugation
    (J : V →ₗ[ℂ] V) (C : V → V) (v : V)
    (hv : v ≠ 0)
    (hCv : C v = v)
    (hCJ : ∀ x, C (J x) = J (C x))
    (hCsmul : ∀ (z : ℂ) x, C (z • x) = star z • C x) :
    cmMinusPart J v ≠ 0 := by
  intro hminus
  have hplusEigen : J v = Complex.I • v :=
    (cmMinusPart_eq_zero_iff J v).mp hminus
  have hc := congrArg C hplusEigen
  rw [hCJ, hCsmul, hCv] at hc
  rw [Complex.star_def, Complex.conj_I] at hc
  have he : Complex.I • v = -Complex.I • v := hplusEigen.symm.trans hc
  have hz : (2 * Complex.I) • v = 0 := by
    calc
      (2 * Complex.I) • v = Complex.I • v - (-Complex.I) • v := by module
      _ = 0 := sub_eq_zero.mpr he
  exact hv (eq_zero_of_nonzero_smul_eq_zero (2 * Complex.I)
    (mul_ne_zero (by norm_num) Complex.I_ne_zero) v hz)

/-- A nonzero conjugation-fixed vector has a nonzero `i` part when conjugation commutes with `J`. -/
theorem cmPlusPart_ne_zero_of_conjugation
    (J : V →ₗ[ℂ] V) (C : V → V) (v : V)
    (hv : v ≠ 0)
    (hCv : C v = v)
    (hCJ : ∀ x, C (J x) = J (C x))
    (hCsmul : ∀ (z : ℂ) x, C (z • x) = star z • C x) :
    cmPlusPart J v ≠ 0 := by
  intro hplus
  have hminusEigen : J v = -Complex.I • v :=
    (cmPlusPart_eq_zero_iff J v).mp hplus
  have hc := congrArg C hminusEigen
  rw [hCJ, hCsmul, hCv] at hc
  rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg] at hc
  have he : -Complex.I • v = Complex.I • v := hminusEigen.symm.trans hc
  have hz : (-2 * Complex.I) • v = 0 := by
    calc
      (-2 * Complex.I) • v = -Complex.I • v - Complex.I • v := by module
      _ = 0 := sub_eq_zero.mpr he
  exact hv (eq_zero_of_nonzero_smul_eq_zero (-2 * Complex.I)
    (mul_ne_zero (by norm_num) Complex.I_ne_zero) v hz)

section External

variable {V₁ V₂ W : Type*}
  [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]
  [AddCommGroup W] [Module ℂ W]

/-- The external product of the two `-i` parts. -/
def cmMinusExternalPart (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W)
    (J₁ : V₁ →ₗ[ℂ] V₁) (J₂ : V₂ →ₗ[ℂ] V₂) (v₁ : V₁) (v₂ : V₂) : W :=
  B (cmMinusPart J₁ v₁) (cmMinusPart J₂ v₂)

/-- A bilinear product nonzero on pure nonzero inputs does not kill the external minus part. -/
theorem cmMinusExternalPart_ne_zero
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W)
    (hB : ∀ x : V₁, x ≠ 0 → ∀ y : V₂, y ≠ 0 → B x y ≠ 0)
    (J₁ : V₁ →ₗ[ℂ] V₁) (J₂ : V₂ →ₗ[ℂ] V₂)
    (C₁ : V₁ → V₁) (C₂ : V₂ → V₂) (v₁ : V₁) (v₂ : V₂)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hC₁v : C₁ v₁ = v₁) (hC₂v : C₂ v₂ = v₂)
    (hC₁J : ∀ x, C₁ (J₁ x) = J₁ (C₁ x))
    (hC₂J : ∀ x, C₂ (J₂ x) = J₂ (C₂ x))
    (hC₁smul : ∀ (z : ℂ) x, C₁ (z • x) = star z • C₁ x)
    (hC₂smul : ∀ (z : ℂ) x, C₂ (z • x) = star z • C₂ x) :
    cmMinusExternalPart B J₁ J₂ v₁ v₂ ≠ 0 :=
  hB _ (cmMinusPart_ne_zero_of_conjugation J₁ C₁ v₁ hv₁ hC₁v hC₁J hC₁smul)
    _ (cmMinusPart_ne_zero_of_conjugation J₂ C₂ v₂ hv₂ hC₂v hC₂J hC₂smul)

/-- Equivariance in the first variable makes the external minus part a `-i` eigenvector. -/
theorem first_map_cmMinusExternalPart
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W)
    (J₁ : V₁ →ₗ[ℂ] V₁) (J₂ : V₂ →ₗ[ℂ] V₂)
    (T₁ : W →ₗ[ℂ] W)
    (hJ₁ : ∀ x, J₁ (J₁ x) = -x)
    (hT₁ : ∀ x y, T₁ (B x y) = B (J₁ x) y)
    (v₁ : V₁) (v₂ : V₂) :
    T₁ (cmMinusExternalPart B J₁ J₂ v₁ v₂) =
      -Complex.I • cmMinusExternalPart B J₁ J₂ v₁ v₂ := by
  rw [cmMinusExternalPart, hT₁,
    map_cmMinusPart_of_sq_neg_one J₁ hJ₁]
  rw [map_smul]
  rfl

/-- Equivariance in the second variable makes the external minus part a `-i` eigenvector. -/
theorem second_map_cmMinusExternalPart
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W)
    (J₁ : V₁ →ₗ[ℂ] V₁) (J₂ : V₂ →ₗ[ℂ] V₂)
    (T₂ : W →ₗ[ℂ] W)
    (hJ₂ : ∀ x, J₂ (J₂ x) = -x)
    (hT₂ : ∀ x y, T₂ (B x y) = B x (J₂ y))
    (v₁ : V₁) (v₂ : V₂) :
    T₂ (cmMinusExternalPart B J₁ J₂ v₁ v₂) =
      -Complex.I • cmMinusExternalPart B J₁ J₂ v₁ v₂ := by
  rw [cmMinusExternalPart, hT₂,
    map_cmMinusPart_of_sq_neg_one J₂ hJ₂]
  rw [map_smul]

/-- A nonzero joint `(-i,-i)` external part is outside any subspace containing no such vector. -/
theorem cmMinusExternalPart_not_mem
    (B : V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] W)
    (J₁ : V₁ →ₗ[ℂ] V₁) (J₂ : V₂ →ₗ[ℂ] V₂)
    (T₁ T₂ : W →ₗ[ℂ] W) (F : Submodule ℂ W)
    (v₁ : V₁) (v₂ : V₂)
    (hne : cmMinusExternalPart B J₁ J₂ v₁ v₂ ≠ 0)
    (hT₁ : T₁ (cmMinusExternalPart B J₁ J₂ v₁ v₂) =
      -Complex.I • cmMinusExternalPart B J₁ J₂ v₁ v₂)
    (hT₂ : T₂ (cmMinusExternalPart B J₁ J₂ v₁ v₂) =
      -Complex.I • cmMinusExternalPart B J₁ J₂ v₁ v₂)
    (hF : ∀ w ∈ F, T₁ w = -Complex.I • w →
      T₂ w = -Complex.I • w → w = 0) :
    cmMinusExternalPart B J₁ J₂ v₁ v₂ ∉ F := by
  intro hw
  exact hne (hF _ hw hT₁ hT₂)

end External

end LinearAlgebra
