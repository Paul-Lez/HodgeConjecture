/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# Comparing Kähler differentials with de Rham one-forms

The comparison sends `a • D b` in Mathlib's Kähler module to the actual symbol
`a db` in the repository's de Rham complex. It descends through the presentation
of Kähler differentials, so identities of Kähler forms can be transported to the
analytic construction without choosing representatives.
-/

@[expose] public noncomputable section

namespace Algebra.DeRham

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Interpret a finite linear combination of formal differentials as de Rham symbols. -/
def kaehlerPresentationToForm : (A →₀ A) →ₗ[R] Form R A 1 :=
  Finsupp.lsum R fun b =>
    { toFun := fun a => mk R A 1 a (fun _ => b)
      map_add' := fun a c => mk_coeff_add R A 1 a c _
      map_smul' := fun r a => mk_coeff_smul R A 1 r a _ }

@[simp] theorem kaehlerPresentationToForm_single (a b : A) :
    kaehlerPresentationToForm R A (Finsupp.single b a) = mk R A 1 a (fun _ => b) := by
  simp only [kaehlerPresentationToForm, Finsupp.lsum_single]
  rfl

private theorem update_fin_one (b : A) :
    Function.update (fun _ : Fin 1 => (0 : A)) 0 b = fun _ => b := by
  funext i
  have : i = 0 := Fin.eq_zero i
  simp [this]

/-- Every relation in the Kähler presentation vanishes in de Rham degree one. -/
theorem kaehlerPresentationToForm_relations :
    (KaehlerDifferential.kerTotal R A).restrictScalars R ≤
      LinearMap.ker (kaehlerPresentationToForm R A) := by
  intro x hx
  change x ∈ KaehlerDifferential.kerTotal R A at hx
  suffices h : ∀ a : A, kaehlerPresentationToForm R A (a • x) = 0 by
    simpa using h 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro a
    rcases hx with ((⟨⟨b, c⟩, rfl⟩ | ⟨⟨b, c⟩, rfl⟩) | ⟨r, rfl⟩)
    · have h := mk_diff_add R A 1 a (fun _ => 0) 0 b c
      simp only [update_fin_one] at h
      simp [smul_add, smul_sub, Finsupp.smul_single, h]
    · have h := mk_diff_mul R A 1 a (fun _ => 0) 0 b c
      simp only [update_fin_one] at h
      simp [smul_add, smul_sub, Finsupp.smul_single, h]
    · have h := mk_diff_const R A 1 a (fun _ => 0) 0 r
      simpa [Finsupp.smul_single, update_fin_one] using h
  | zero => simp
  | add x y _ _ hx hy =>
    intro a
    simp only [smul_add, map_add, hx a, hy a, add_zero]
  | smul b x _ hx =>
    intro a
    rw [smul_smul]
    exact hx (a * b)

/-- The canonical comparison from the actual Kähler module to de Rham one-forms. -/
def kaehlerToForm : KaehlerDifferential R A →ₗ[R] Form R A 1 :=
  ((KaehlerDifferential.kerTotal R A).restrictScalars R).liftQ
    (kaehlerPresentationToForm R A) (kaehlerPresentationToForm_relations R A) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R
      (KaehlerDifferential.kerTotal R A)).symm.toLinearMap ∘ₗ
    ((KaehlerDifferential.quotKerTotalEquiv R A).symm.restrictScalars R).toLinearMap

/-- The comparison retains the coefficient of each differential. -/
@[simp] theorem kaehlerToForm_smul_D (a b : A) :
    kaehlerToForm R A (a • KaehlerDifferential.D R A b) =
      mk R A 1 a (fun _ => b) := by
  have h : (KaehlerDifferential.quotKerTotalEquiv R A).symm
      (a • KaehlerDifferential.D R A b) =
      Submodule.Quotient.mk (Finsupp.single b a) := by
    change (KaehlerDifferential.derivationQuotKerTotal R A).liftKaehlerDifferential
      (a • KaehlerDifferential.D R A b) = _
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]
    simp [KaehlerDifferential.derivationQuotKerTotal_apply, ← Submodule.Quotient.mk_smul]
  change ((KaehlerDifferential.kerTotal R A).restrictScalars R).liftQ
    (kaehlerPresentationToForm R A) (kaehlerPresentationToForm_relations R A)
    ((Submodule.Quotient.restrictScalarsEquiv R
      (KaehlerDifferential.kerTotal R A)).symm
      ((KaehlerDifferential.quotKerTotalEquiv R A).symm
        (a • KaehlerDifferential.D R A b))) = _
  rw [h]
  exact kaehlerPresentationToForm_single R A a b

@[simp] theorem kaehlerToForm_D (b : A) :
    kaehlerToForm R A (KaehlerDifferential.D R A b) = mk R A 1 1 (fun _ => b) := by
  simpa using kaehlerToForm_smul_D R A 1 b

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The comparison commutes with restriction and every other change of coefficient algebra. -/
theorem kaehlerToForm_map (w : KaehlerDifferential R A) :
    kaehlerToForm R B (KaehlerDifferential.map R R A B w) =
      map R (IsScalarTower.toAlgHom R A B) 1 (kaehlerToForm R A w) := by
  obtain ⟨v, rfl⟩ := KaehlerDifferential.linearCombination_surjective R A w
  induction v using Finsupp.induction with
  | zero => simp
  | single_add b a v hb ha ih =>
    simp only [map_add, Finsupp.linearCombination_single, ih]
    congr 1
    rw [map_smul, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_smul B a, kaehlerToForm_smul_D]
    simp

end Algebra.DeRham
