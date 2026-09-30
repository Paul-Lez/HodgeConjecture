/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Derivations detect first-order classes

This file contains the small commutative-algebra interface used when a geometric chart supplies
a residue-valued derivation.  The derivation is required to use the residue-field action on its
target, expressed by the condition that the maximal ideal acts trivially.  Its induced map on
the cotangent space is therefore well-defined.  A surjective induced map between equal finite
dimensional spaces is injective, so a nonzero cotangent class has nonzero derivative.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Derivation

variable {K R V : Type*} [Field K] [CommRing R] [AddCommGroup V]
  [Algebra K R] [Module K V] [Module R V] [IsScalarTower K R V]
  [IsLocalRing R]

/-- The cotangent map induced by a derivation whose target carries the residue-field action.

The `htrivial` hypothesis says that the maximal ideal acts by zero on the target.  It is exactly
what makes the derivation vanish on products from the maximal ideal. -/
def cotangentMap (D : Derivation K R V)
    (htrivial : ∀ (r : R), r ∈ maximalIdeal R → ∀ v : V, r • v = 0) :
    (CotangentSpace R) →ₗ[K] V := by
  let f : maximalIdeal R →ₗ[K] V :=
    { toFun := fun r => D r
      map_add' := fun r s => D.map_add r s
      map_smul' := fun c r => D.map_smul c r }
  refine Ideal.Cotangent.lift f ?_
  intro r s
  change f (r * s) = 0
  change D (r.1 * s.1) = 0
  rw [D.leibniz]
  simp only [htrivial r.1 r.2, htrivial s.1 s.2, add_zero]

omit [IsScalarTower K R V] in
@[simp]
lemma cotangentMap_toCotangent (D : Derivation K R V)
    (htrivial : ∀ (r : R), r ∈ maximalIdeal R → ∀ v : V, r • v = 0)
    (r : maximalIdeal R) :
    cotangentMap D htrivial ((maximalIdeal R).toCotangent r) = D r := by
  rfl

omit [IsScalarTower K R V] in
/-- A cotangent map detects a nonzero class whenever it is injective. -/
theorem ne_zero_of_mem_maximalIdeal_of_not_mem_square_of_injective
    (D : Derivation K R V)
    (htrivial : ∀ (r : R), r ∈ maximalIdeal R → ∀ v : V, r • v = 0)
    (hinj : Function.Injective (cotangentMap D htrivial))
    (a : R) (ha : a ∈ maximalIdeal R) (ha2 : a ∉ (maximalIdeal R) ^ 2) :
    D a ≠ 0 := by
  intro hDa
  have hcot : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0 := by
    apply hinj
    simpa only [cotangentMap_toCotangent, map_zero] using hDa
  exact ha2 ((Ideal.toCotangent_eq_zero (maximalIdeal R) ⟨a, ha⟩).mp hcot)

variable [FiniteDimensional K (CotangentSpace R)] [FiniteDimensional K V]

omit [IsScalarTower K R V] in
/-- A surjective residue-valued derivation detects every nonzero cotangent class. -/
theorem ne_zero_of_mem_maximalIdeal_of_not_mem_square
    (D : Derivation K R V)
    (htrivial : ∀ (r : R), r ∈ maximalIdeal R → ∀ v : V, r • v = 0)
    (hsurj : Function.Surjective (cotangentMap D htrivial))
    (hdim : Module.finrank K (CotangentSpace R) = Module.finrank K V)
    (a : R) (ha : a ∈ maximalIdeal R) (ha2 : a ∉ (maximalIdeal R) ^ 2) :
    D a ≠ 0 := by
  have hinj : Function.Injective (cotangentMap D htrivial) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := K) (V := CotangentSpace R) (V₂ := V)
      hdim).mpr hsurj
  exact ne_zero_of_mem_maximalIdeal_of_not_mem_square_of_injective
    D htrivial hinj a ha ha2

end Derivation
