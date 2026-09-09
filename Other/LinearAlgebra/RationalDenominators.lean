/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Clearing denominators of rational-valued linear maps

A rational-valued homomorphism on a finitely generated abelian group has a single
nonzero integer denominator. No freeness or torsion-freeness assumption is needed.
-/

@[expose] public noncomputable section

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]

/-- Multiplying a rational-valued linear map by a nonzero integer makes all its values integral. -/
theorem exists_integer_multiple_isInteger (f : M →ₗ[ℤ] ℚ) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x, IsLocalization.IsInteger ℤ (n • f x) := by
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := M)
  obtain ⟨n, hn⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ) S f
  refine ⟨n, nonZeroDivisors.ne_zero n.property, fun x ↦ ?_⟩
  have hx : x ∈ Submodule.span ℤ (S : Set M) := hS.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hn x hx
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | add x y hx hy ihx ihy =>
      simpa only [map_add, smul_add] using IsLocalization.isInteger_add ihx ihy
  | smul a x hx ih =>
      simpa only [map_smul, smul_comm n.val a] using
        (IsLocalization.isInteger_smul (a := a) ih)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A rational-valued linear map on a finitely generated abelian group becomes
integer-valued after multiplication by a nonzero integer. -/
theorem exists_integer_multiple (f : M →ₗ[ℤ] ℚ) :
    ∃ (n : ℤ) (g : M →ₗ[ℤ] ℤ), n ≠ 0 ∧
      (Algebra.linearMap ℤ ℚ).comp g = n • f := by
  obtain ⟨n, hn, h⟩ := exists_integer_multiple_isInteger f
  let j : ℤ →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ
  let e := LinearEquiv.ofInjective j (FaithfulSMul.algebraMap_injective ℤ ℚ)
  have hrange (x : M) : (n • f) x ∈ LinearMap.range j := h x
  let G := e.symm.toLinearMap.comp ((n • f).codRestrict (LinearMap.range j) hrange)
  refine ⟨n, G, hn, ?_⟩
  ext x
  have he := congrArg Subtype.val (e.apply_symm_apply ⟨(n • f) x, hrange x⟩)
  exact he

end LinearMap
