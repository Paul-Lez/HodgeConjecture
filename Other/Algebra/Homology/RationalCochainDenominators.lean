/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.LinearAlgebra.RationalDenominators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Denominator clearing for cohomology

This file gives a criterion for transporting denominator clearing from the
middle component of a short complex to its homology. Applying it to the
integral-to-rational cohomology map of an analytic space still requires a
suitable cochain model and coefficient comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {S T : ShortComplex (ModuleCat ℤ)}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- If middle-degree elements have nonzero integral multiples in the image, and
the next component is injective, the same holds for homology classes. -/
theorem homologyMap_exists_integer_multiple (φ : S ⟶ T)
    (h₃ : Function.Injective φ.τ₃)
    (h₂ : ∀ b : T.X₂, ∃ (n : ℤ) (a : S.X₂), n ≠ 0 ∧ φ.τ₂ a = n • b)
    (α : T.homology) :
    ∃ (n : ℤ) (β : S.homology), n ≠ 0 ∧ homologyMap φ β = n • α := by
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective T.homologyπ).mp inferInstance α
  obtain ⟨n, a, hn, ha⟩ := h₂ (T.iCycles b)
  have haz : S.g a = 0 := by
    apply h₃
    rw [map_zero]
    have hcomm := ConcreteCategory.congr_hom φ.comm₂₃ a
    change T.g (φ.τ₂ a) = φ.τ₃ (S.g a) at hcomm
    rw [← hcomm, ha]
    rw [map_zsmul]
    have hb := ConcreteCategory.congr_hom T.iCycles_g b
    change T.g (T.iCycles b) = 0 at hb
    rw [hb, zsmul_zero]
  let c : S.cycles := S.moduleCatCyclesIso.inv ⟨a, haz⟩
  have hc : S.iCycles c = a :=
    ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨a, haz⟩
  have hcb : cyclesMap φ c = n • b := by
    apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [map_zsmul]
    have hcomm := ConcreteCategory.congr_hom (cyclesMap_i φ) c
    change T.iCycles (cyclesMap φ c) = φ.τ₂ (S.iCycles c) at hcomm
    rw [hcomm, hc, ha]
  refine ⟨n, S.homologyπ c, hn, ?_⟩
  have hnat := ConcreteCategory.congr_hom (homologyπ_naturality φ) c
  change homologyMap φ (S.homologyπ c) = T.homologyπ (cyclesMap φ c) at hnat
  rw [hnat, hcb]
  exact map_zsmul T.homologyπ.hom n b

end CategoryTheory.ShortComplex
