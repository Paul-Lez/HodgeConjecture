/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.Algebra.DeRham.Kaehler
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Tactic.FinCases

/-!
# Wedges of Kähler one-forms

The bilinear pairing is constructed by descending both Kähler presentations to the actual
degree-two de Rham quotient. Its value on generators is `ab dx ∧ dy`.
-/

@[expose] public noncomputable section

namespace Algebra.DeRham

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def kaehlerWedgeSymbol (b d : A) : A →ₗ[R] A →ₗ[R] Form R A 2 :=
  LinearMap.mk₂ R (fun a c => mk R A 2 (a * c) ![b, d])
    (by intro a a' c; simp [add_mul])
    (by intro r a c; simp)
    (by intro a c c'; simp [mul_add])
    (by intro r a c; simp)

def rawKaehlerWedge : (A →₀ A) →ₗ[R] (A →₀ A) →ₗ[R] Form R A 2 :=
  Finsupp.lsum R fun b => (Finsupp.lsum R fun d => (kaehlerWedgeSymbol R A b d).flip).flip

@[simp] theorem rawKaehlerWedge_single (a b c d : A) :
    rawKaehlerWedge R A (Finsupp.single b a) (Finsupp.single d c) =
      mk R A 2 (a * c) ![b, d] := by
  simp only [rawKaehlerWedge, Finsupp.lsum_single, LinearMap.flip_apply]
  rfl

private theorem update_zero (a b : A) :
    Function.update (![0, b] : Fin 2 → A) 0 a = ![a, b] := by
  funext i
  fin_cases i <;> simp

private theorem update_one (a b : A) :
    Function.update (![a, 0] : Fin 2 → A) 1 b = ![a, b] := by
  funext i
  fin_cases i <;> simp

theorem rawKaehlerWedge_left_relations :
    (KaehlerDifferential.kerTotal R A).restrictScalars R ≤
      LinearMap.ker (rawKaehlerWedge R A) := by
  intro x hx
  change x ∈ KaehlerDifferential.kerTotal R A at hx
  suffices h : ∀ a : A, ∀ y : A →₀ A, rawKaehlerWedge R A (a • x) y = 0 by
    apply LinearMap.ext
    intro y
    simpa using h 1 y
  induction hx using Submodule.span_induction with
  | mem x hx =>
      intro a y
      induction y using Finsupp.induction with
      | zero => simp
      | single_add d c y hd hc ih =>
          rw [map_add, ih, add_zero]
          rcases hx with ((⟨⟨b, e⟩, rfl⟩ | ⟨⟨b, e⟩, rfl⟩) | ⟨r, rfl⟩)
          · have h := mk_diff_add R A 2 (a * c) ![0, d] 0 b e
            simp only [update_zero] at h
            simp [smul_add, smul_sub, Finsupp.smul_single, h]
          · have h := mk_diff_mul R A 2 (a * c) ![0, d] 0 b e
            simp only [update_zero] at h
            simp [smul_add, smul_sub, Finsupp.smul_single, mul_left_comm, mul_comm, h]
          · have h := mk_diff_const R A 2 (a * c) ![0, d] 0 r
            simpa [Finsupp.smul_single, update_zero] using h
  | zero => simp
  | add x y _ _ hx hy =>
      intro a z
      simp only [smul_add, map_add, LinearMap.add_apply, hx a z, hy a z, add_zero]
  | smul b x _ hx =>
      intro a y
      rw [smul_smul]
      exact hx (a * b) y

theorem rawKaehlerWedge_right_relations :
    (KaehlerDifferential.kerTotal R A).restrictScalars R ≤
      LinearMap.ker (rawKaehlerWedge R A).flip := by
  intro y hy
  change y ∈ KaehlerDifferential.kerTotal R A at hy
  suffices h : ∀ c : A, ∀ x : A →₀ A, rawKaehlerWedge R A x (c • y) = 0 by
    apply LinearMap.ext
    intro x
    simpa using h 1 x
  induction hy using Submodule.span_induction with
  | mem y hy =>
      intro c x
      induction x using Finsupp.induction with
      | zero => simp
      | single_add b a x hb ha ih =>
          rw [map_add, LinearMap.add_apply, ih, add_zero]
          rcases hy with ((⟨⟨d, e⟩, rfl⟩ | ⟨⟨d, e⟩, rfl⟩) | ⟨r, rfl⟩)
          · have h := mk_diff_add R A 2 (a * c) ![b, 0] 1 d e
            simp only [update_one] at h
            simp [smul_add, smul_sub, Finsupp.smul_single, h]
          · have h := mk_diff_mul R A 2 (a * c) ![b, 0] 1 d e
            simp only [update_one] at h
            simp [smul_add, smul_sub, Finsupp.smul_single, mul_assoc, h]
          · have h := mk_diff_const R A 2 (a * c) ![b, 0] 1 r
            simpa [Finsupp.smul_single, update_one] using h
  | zero => simp
  | add x y _ _ hx hy =>
      intro c z
      simp only [smul_add, map_add, hx c z, hy c z, add_zero]
  | smul b x _ hx =>
      intro c y
      rw [smul_smul]
      exact hx (c * b) y

/-- The base-ring-linear version of the standard Kähler presentation equivalence. -/
def kaehlerPresentationEquiv :
    ((A →₀ A) ⧸ (KaehlerDifferential.kerTotal R A).restrictScalars R) ≃ₗ[R]
      KaehlerDifferential R A :=
  (Submodule.Quotient.restrictScalarsEquiv R (KaehlerDifferential.kerTotal R A)).trans
    ((KaehlerDifferential.quotKerTotalEquiv R A).restrictScalars R)

@[simp] theorem kaehlerPresentationEquiv_symm_smul_D (a b : A) :
    (kaehlerPresentationEquiv R A).symm (a • KaehlerDifferential.D R A b) =
      Submodule.Quotient.mk (Finsupp.single b a) := by
  have h : (KaehlerDifferential.quotKerTotalEquiv R A).symm
      (a • KaehlerDifferential.D R A b) =
      Submodule.Quotient.mk (Finsupp.single b a) := by
    change (KaehlerDifferential.derivationQuotKerTotal R A).liftKaehlerDifferential
      (a • KaehlerDifferential.D R A b) = _
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]
    simp [KaehlerDifferential.derivationQuotKerTotal_apply, ← Submodule.Quotient.mk_smul]
  change (Submodule.Quotient.restrictScalarsEquiv R (KaehlerDifferential.kerTotal R A)).symm
    ((KaehlerDifferential.quotKerTotalEquiv R A).symm
      (a • KaehlerDifferential.D R A b)) = _
  rw [h]
  rfl

/-- The wedge of two actual Kähler differentials, in the degree-two de Rham quotient. -/
def kaehlerWedge :
    KaehlerDifferential R A →ₗ[R] KaehlerDifferential R A →ₗ[R] Form R A 2 :=
  (((rawKaehlerWedge R A).liftQ₂
      ((KaehlerDifferential.kerTotal R A).restrictScalars R)
      ((KaehlerDifferential.kerTotal R A).restrictScalars R)
      (rawKaehlerWedge_left_relations R A) (rawKaehlerWedge_right_relations R A)).compl₂
    (kaehlerPresentationEquiv R A).symm.toLinearMap).comp
      (kaehlerPresentationEquiv R A).symm.toLinearMap

@[simp] theorem kaehlerWedge_smul_D_smul_D (a b c d : A) :
    kaehlerWedge R A (a • KaehlerDifferential.D R A b)
      (c • KaehlerDifferential.D R A d) = mk R A 2 (a * c) ![b, d] := by
  simp only [kaehlerWedge, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearEquiv.coe_toLinearMap, kaehlerPresentationEquiv_symm_smul_D,
    LinearMap.liftQ₂_mk, rawKaehlerWedge_single]

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Wedge formation commutes with the actual algebra maps used for restriction and pullback. -/
theorem kaehlerWedge_map (w z : KaehlerDifferential R A) :
    kaehlerWedge R B (KaehlerDifferential.map R R A B w)
      (KaehlerDifferential.map R R A B z) =
      map R (IsScalarTower.toAlgHom R A B) 2 (kaehlerWedge R A w z) := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A w
  obtain ⟨u, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A z
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b a v hb ha ih =>
      simp only [map_add, Finsupp.linearCombination_single, LinearMap.add_apply, ih]
      congr 1
      clear ih
      induction u using Finsupp.induction with
      | zero => simp
      | single_add d c u hd hc ih' =>
          simp only [map_add, Finsupp.linearCombination_single, ih']
          congr 1
          rw [(KaehlerDifferential.map R R A B).map_smul,
            (KaehlerDifferential.map R R A B).map_smul,
            KaehlerDifferential.map_D, KaehlerDifferential.map_D,
            ← IsScalarTower.algebraMap_smul B a, ← IsScalarTower.algebraMap_smul B c,
            kaehlerWedge_smul_D_smul_D, kaehlerWedge_smul_D_smul_D]
          simp
          congr 1
          funext i
          fin_cases i <;> rfl

end Algebra.DeRham
