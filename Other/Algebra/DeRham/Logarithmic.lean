/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.Algebra.DeRham.Basic

/-!
# Logarithmic differential forms

For units `u₁, …, uₚ`, construct the symbol
`(u₁ ⋯ uₚ)⁻¹ du₁ ∧ … ∧ duₚ` in the existing de Rham complex and prove it closed.
These are the differential forms used for local residue classes. The construction uses the
existing differential and quotient relations, rather than adding a new complex or an axiom of
closedness.
-/

@[expose] public noncomputable section

namespace Algebra.DeRham

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- A form with zero coefficient vanishes. -/
@[simp]
lemma mk_coeff_zero (p : ℕ) (v : Fin p → A) : mk R A p 0 v = 0 := by
  simpa using mk_coeff_smul R A p (0 : R) (0 : A) v

/-- Differentiating an inverse unit in one slot gives the usual inverse-square formula. -/
lemma mk_diff_unit_inv (p : ℕ) (a : A) (v : Fin p → A) (i : Fin p) (u : Aˣ) :
    mk R A p a (Function.update v i (↑u⁻¹ : A)) =
      -mk R A p (a * (↑u⁻¹ : A) ^ 2) (Function.update v i (u : A)) := by
  have h := mk_diff_mul R A p (a * (↑u⁻¹ : A)) v i (u : A) (↑u⁻¹ : A)
  have hc := mk_diff_const R A p (a * (↑u⁻¹ : A)) v i 1
  simp only [map_one, Units.mul_inv] at hc h
  have hleft : a * (↑u⁻¹ : A) * (u : A) = a := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  have hright : a * (↑u⁻¹ : A) * (↑u⁻¹ : A) = a * (↑u⁻¹ : A) ^ 2 := by
    rw [pow_two, mul_assoc]
  rw [hleft, hright, hc] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- A constant in the first differential slot gives zero. -/
lemma mk_cons_one (p : ℕ) (a : A) (v : Fin p → A) :
    mk R A (p + 1) a (Fin.cons 1 v) = 0 := by
  simpa using mk_diff_const R A (p + 1) a (Fin.cons 1 v) 0 1

/-- Repeating one of the trailing differentials in the first slot gives zero. -/
lemma mk_cons_eq_zero (p : ℕ) (a : A) (v : Fin p → A) (i : Fin p) :
    mk R A (p + 1) a (Fin.cons (v i) v) = 0 := by
  apply mk_alt R A (p + 1) a (Fin.cons (v i) v) 0 i.succ
  · simp
  · exact Fin.succ_ne_zero i |>.symm

/-- An inverse of one of the trailing units in the first differential slot also gives zero. -/
lemma mk_cons_unit_inv_eq_zero (p : ℕ) (a : A) (u : Fin p → Aˣ) (i : Fin p) :
    mk R A (p + 1) a (Fin.cons (↑(u i)⁻¹ : A) (fun j => (u j : A))) = 0 := by
  have h := mk_diff_unit_inv R A (p + 1) a
    (Fin.cons (↑(u i)⁻¹ : A) (fun j => (u j : A))) 0 (u i)
  simpa only [Fin.update_cons_zero,
    mk_cons_eq_zero R A p (a * (↑(u i)⁻¹ : A) ^ 2) (fun j => (u j : A)) i,
    neg_zero] using h

/-- The differential of a product of inverse units wedges to zero against the differentials
of all the units appearing in that product. -/
lemma mk_cons_prod_unit_inv_eq_zero (p : ℕ) (u : Fin p → Aˣ) (t : Finset (Fin p))
    (a : A) :
    mk R A (p + 1) a
      (Fin.cons (∏ i ∈ t, (↑(u i)⁻¹ : A)) (fun j => (u j : A))) = 0 := by
  classical
  induction t using Finset.induction_on generalizing a with
  | empty => simpa using mk_cons_one R A p a (fun j => (u j : A))
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi]
      have h := mk_diff_mul R A (p + 1) a
        (Fin.cons 0 (fun j => (u j : A))) 0
        (↑(u i)⁻¹ : A) (∏ j ∈ t, (↑(u j)⁻¹ : A))
      simpa [ih, mk_cons_unit_inv_eq_zero] using h

/-- The logarithmic `p`-form `dlog u₁ ∧ … ∧ dlog uₚ` for a tuple of units. -/
def logarithmicForm (p : ℕ) (u : Fin p → Aˣ) : Form R A p :=
  mk R A p (∏ i, (↑(u i)⁻¹ : A)) (fun i => (u i : A))

/-- Logarithmic forms are closed in the existing de Rham complex. -/
@[simp]
theorem differential_logarithmicForm (p : ℕ) (u : Fin p → Aˣ) :
    differential R A p (logarithmicForm R A p u) = 0 := by
  rw [logarithmicForm, differential_mk]
  exact mk_cons_prod_unit_inv_eq_zero R A p u Finset.univ 1

variable {A} {B : Type u} [CommRing B] [Algebra R B]

/-- Logarithmic forms commute with algebra homomorphisms, including restriction maps. -/
@[simp]
theorem map_logarithmicForm (f : A →ₐ[R] B) (p : ℕ) (u : Fin p → Aˣ) :
    map R f p (logarithmicForm R A p u) =
      logarithmicForm R B p (fun i => Units.map f.toMonoidHom (u i)) := by
  simp [logarithmicForm]

variable (A)

/-- The one-form `u⁻¹ du`. -/
def dlog (u : Aˣ) : Form R A 1 := logarithmicForm R A 1 (fun _ => u)

/-- Logarithmic differentials commute with changing the coefficient algebra. -/
@[simp]
theorem map_dlog (f : A →ₐ[R] B) (u : Aˣ) :
    map R f 1 (dlog R A u) = dlog R B (Units.map f.toMonoidHom u) :=
  map_logarithmicForm R f 1 _

@[simp]
theorem differential_dlog (u : Aˣ) : differential R A 1 (dlog R A u) = 0 :=
  differential_logarithmicForm R A 1 _

@[simp]
theorem dlog_one : dlog R A 1 = 0 := by
  simpa [dlog, logarithmicForm] using mk_diff_const R A 1 1 (fun _ => 1) 0 1

/-- The logarithmic differential turns multiplication of units into addition. -/
theorem dlog_mul (u v : Aˣ) : dlog R A (u * v) = dlog R A u + dlog R A v := by
  have h := mk_diff_mul R A 1 (↑((u * v)⁻¹) : A) (fun _ => 0) 0 (u : A) (v : A)
  have hu : (↑((u * v)⁻¹) : A) * (u : A) = (↑v⁻¹ : A) := by
    change ((↑v⁻¹ : A) * (↑u⁻¹ : A)) * (u : A) = _
    rw [mul_assoc, Units.inv_mul, mul_one]
  have hv : (↑((u * v)⁻¹) : A) * (v : A) = (↑u⁻¹ : A) := by
    change ((↑v⁻¹ : A) * (↑u⁻¹ : A)) * (v : A) = _
    rw [mul_comm (↑v⁻¹ : A) (↑u⁻¹ : A), mul_assoc, Units.inv_mul, mul_one]
  have ht (a : A) : Function.update (fun _ : Fin 1 => (0 : A)) 0 a = fun _ => a := by
    funext i
    have : i = 0 := Subsingleton.elim _ _
    simp [this]
  rw [hu, hv] at h
  simpa only [dlog, logarithmicForm, Fin.prod_univ_one, Units.val_mul, ht,
    add_comm] using h

/-- The logarithmic differential is a homomorphism from units to closed one-forms. -/
def dlogHom : Aˣ →* Multiplicative (LinearMap.ker (differential R A 1)) where
  toFun u := Multiplicative.ofAdd ⟨dlog R A u, differential_dlog R A u⟩
  map_one' := by
    apply Subtype.ext
    exact dlog_one R A
  map_mul' u v := by
    apply Subtype.ext
    exact dlog_mul R A u v

end Algebra.DeRham
